module Gin.DriverSpec (spec) where

import Control.Exception (bracket)
import Control.Monad (forM_, unless)
import Data.ByteString qualified as BS
import Data.ByteString.Lazy qualified as LBS
import Data.List (intercalate, sort)
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Text.Encoding qualified as Text
import GHC.Clock (getMonotonicTime)
import GHC.IO.Handle (hDuplicate, hDuplicateTo)
import Gin.Backend.SystemVerilog (systemVerilog)
import Gin.Backend.Types (Backend (..))
import Gin.Backend.VHDL (vhdl)
import Gin.Backend.Verilog (verilog)
import Gin.Core.Json (encodeProgram, encodeVectors)
import Gin.Core.Syntax
import Gin.Driver (runCliWith)
import Gin.Examples
import Gin.Limits (maxInputBytes)
import Gin.Netlist.Build (buildNetlist)
import Gin.Netlist.Types (Module)
import Gin.Normalize (normalize)
import Gin.TestUtil (itWithTools, withTempDir)
import Gin.Vectors (Cycle (..), Vectors (..))
import System.Directory
  ( createDirectory
  , createFileLink
  , doesDirectoryExist
  , findExecutable
  , getPermissions
  , listDirectory
  , pathIsSymbolicLink
  , setOwnerExecutable
  , setPermissions
  )
import System.Environment (getEnvironment)
import System.Exit (ExitCode (..))
import System.FilePath ((</>))
import System.IO (Handle, IOMode (..), hClose, hFlush, stderr, stdout, withBinaryFile)
import Test.Hspec

spec :: Spec
spec = do
  exitCodeSpec
  compileFilesSpec
  certificateSpec
  vectorsMismatchSpec
  simSpec
  validateSpec
  timeoutSpec

----------------------------------------------------------------------
-- Exit codes and usage

exitCodeSpec :: Spec
exitCodeSpec = describe "exit codes" $ do
  it "[cli-exit-codes] returns 0 and prints nothing for a program that checks" $
    withTempDir $ \dir -> do
      file <- writeProgram dir "counter" counterProgram
      r <- gin ["check", file]
      r `shouldExit` ExitSuccess
      runOut r `shouldBe` ""
      runErr r `shouldBe` ""
  it "[cli-exit-codes] returns 1 with the stage's error for files that fail a check" $
    withTempDir $ \dir -> do
      illTyped <- writeProgram dir "ill-typed" missingTopDef
      garbage <- writeRaw dir "garbage.gin.json" "{\"format\": \"gin-ir/1\""
      let missing = dir </> "missing.gin.json"
      forM_
        [ (illTyped, "type error: ")
        , (garbage, "decode error: ")
        , (missing, "driver error: cannot read ")
        ]
        $ \(file, prefix) -> do
          r <- gin ["check", file]
          r `shouldExit` ExitFailure 1
          runErr r `shouldStartWith'` prefix
          runOut r `shouldBe` ""
  it "[cli-exit-codes] returns 1 for an input file over the size limit" $
    withTempDir $ \dir -> do
      file <- writeRaw dir "huge.gin.json" (Text.replicate (maxInputBytes + 1) " ")
      r <- gin ["check", file]
      r `shouldExit` ExitFailure 1
      runErr r `shouldStartWith'` "decode error: "
      runErr r `shouldContainText` "exceeds"
  it "[cli-exit-codes] returns 2 and prints usage to stderr for a usage error" $
    withTempDir $ \dir -> do
      file <- writeProgram dir "counter" counterProgram
      vecs <- writeVectors dir "counter" counterVectors
      forM_
        [ []
        , ["frobnicate", file]
        , ["check"]
        , ["check", file, "--bogus"]
        , ["check", file, "--allow-axiom"]
        , ["sim", file]
        , ["compile", file, "--target", "chisel"]
        , ["testbench", file, "--vectors", vecs, "-o"]
        , ["validate", file, "--vectors", vecs, "--tool-timeout", "0"]
        , ["validate", file, "--vectors", vecs, "--tool-timeout", "soon"]
        , ["validate", file, "--vectors", vecs, "--tool-timeout", "99999999999999999999"]
        ]
        $ \args -> do
          r <- gin args
          (args, runCode r) `shouldBe` (args, ExitFailure 2)
          (args, runOut r) `shouldBe` (args, "")
          (args, Text.isInfixOf "Usage: gin" (runErr r)) `shouldBe` (args, True)
  it "[cli-exit-codes] returns 0 and prints usage to stdout for --help" $
    forM_ [["--help"], ["compile", "--help"], ["validate", "--help"]] $ \args -> do
      r <- gin args
      (args, runCode r) `shouldBe` (args, ExitSuccess)
      (args, Text.isInfixOf "Usage: gin" (runOut r)) `shouldBe` (args, True)
      (args, runErr r) `shouldBe` (args, "")
  it "[cli-exit-codes] lists every command and validate's options in the help" $ do
    top <- gin ["--help"]
    forM_ ["check", "compile", "testbench", "sim", "validate"] $ \c ->
      runOut top `shouldContainText` c
    v <- gin ["validate", "--help"]
    forM_ ["--vectors", "--target", "--allow-axiom", "--allow-missing-tools", "--tool-timeout"] $
      shouldContainText (runOut v)

----------------------------------------------------------------------
-- File output

compileFilesSpec :: Spec
compileFilesSpec = describe "compile and testbench output" $ do
  it "[cli-compile-files] writes exactly DIR/<top>.<ext> for each requested target" $
    withTempDir $ \dir -> do
      file <- writeProgram dir "counter" counterProgram
      forM_
        [ (["--target", "verilog"], ["counter.v"])
        , (["--target", "vhdl", "--target", "systemverilog"], ["counter.sv", "counter.vhd"])
        , (["--target", "vhdl", "--target", "vhdl"], ["counter.vhd"])
        , ([], ["counter.sv", "counter.v", "counter.vhd"])
        ]
        $ \(targets, expected) -> withTempDir $ \out -> do
          r <- gin (["compile", file, "-o", out] <> targets)
          r `shouldExit` ExitSuccess
          files <- sort <$> listDirectory out
          (targets, files) `shouldBe` (targets, expected)
  it "[cli-compile-files] writes the backends' renderings byte for byte" $
    withTempDir $ \dir -> do
      file <- writeProgram dir "counter" counterProgram
      m <- netlistOf counterProgram
      r <- gin ["compile", file, "-o", dir </> "out"]
      r `shouldExit` ExitSuccess
      forM_ [verilog, systemVerilog, vhdl] $ \b -> do
        written <- readText (dir </> "out" </> ("counter." <> backendFileExt b))
        written `shouldBe` backendRender b m
  it "[cli-compile-files] testbench also writes DIR/<top>_tb.<ext>, creating DIR" $
    withTempDir $ \dir -> do
      file <- writeProgram dir "counter" counterProgram
      vecs <- writeVectors dir "counter" counterVectors
      m <- netlistOf counterProgram
      let out = dir </> "new" </> "nested"
      r <- gin ["testbench", file, "--vectors", vecs, "-o", out]
      r `shouldExit` ExitSuccess
      files <- sort <$> listDirectory out
      files
        `shouldBe` [ "counter.sv"
                   , "counter.v"
                   , "counter.vhd"
                   , "counter_tb.sv"
                   , "counter_tb.v"
                   , "counter_tb.vhd"
                   ]
      written <- readText (out </> "counter_tb.vhd")
      written `shouldBe` backendTestbench vhdl m counterVectors
  it "[cli-compile-files] writes nothing, and creates no directory, when compiling fails" $
    withTempDir $ \dir -> do
      clash <- writeProgram dir "clash" clockPort
      sorry <- writeProgram dir "sorry" (counterWithAxioms ["sorryAx"])
      vecs <- writeVectors dir "clash" counterVectors {vecInputs = [Port "clk" TBool]}
      forM_
        [ (["compile", clash], "netlist error: ")
        , (["compile", sorry], "certificate error: ")
        , (["testbench", clash, "--vectors", vecs], "netlist error: ")
        ]
        $ \(args, prefix) -> do
          let out = dir </> "out"
          r <- gin (args <> ["-o", out])
          r `shouldExit` ExitFailure 1
          runErr r `shouldStartWith'` prefix
          doesDirectoryExist out `shouldReturn` False
  it "[cli-compile-files] leaves an existing output directory as it was when compiling fails" $
    withTempDir $ \dir -> do
      clash <- writeProgram dir "clash" clockPort
      let out = dir </> "out"
      createDirectory out
      _ <- writeRaw out "keep.txt" "kept"
      r <- gin ["compile", clash, "-o", out, "--target", "verilog"]
      r `shouldExit` ExitFailure 1
      listDirectory out `shouldReturn` ["keep.txt"]
  it "[cli-compile-files] writes neither file of a target when one cannot be written" $
    withTempDir $ \dir -> do
      file <- writeProgram dir "counter" counterProgram
      vecs <- writeVectors dir "counter" counterVectors
      let out = dir </> "out"
      createDirectory out
      createDirectory (out </> "counter_tb.v")
      r <- gin ["testbench", file, "--vectors", vecs, "-o", out, "--target", "verilog"]
      r `shouldExit` ExitFailure 1
      runErr r `shouldStartWith'` "driver error: cannot write "
      listDirectory out `shouldReturn` ["counter_tb.v"]
  it "[cli-compile-files] replaces a symbolic link in DIR instead of writing through it" $
    withTempDir $ \dir -> do
      file <- writeProgram dir "counter" counterProgram
      victim <- writeRaw dir "victim.txt" "untouched"
      let out = dir </> "out"
      createDirectory out
      createFileLink victim (out </> "counter.v")
      r <- gin ["compile", file, "-o", out, "--target", "verilog"]
      r `shouldExit` ExitSuccess
      readText victim `shouldReturn` "untouched"
      pathIsSymbolicLink (out </> "counter.v") `shouldReturn` False
      readText (out </> "counter.v") >>= (`shouldContainText` "module counter")
      listDirectory out `shouldReturn` ["counter.v"]

----------------------------------------------------------------------
-- Certificates

certificateSpec :: Spec
certificateSpec = describe "certificate policy" $ do
  it "[cli-sorry] check rejects the sorry fixture with a certificate error" $ do
    r <- gin ["check", "test/fixtures/ir/sorry.gin.json"]
    r `shouldExit` ExitFailure 1
    runErr r `shouldStartWith'` "certificate error:"
    runErr r `shouldContainText` "sorryAx"
    runOut r `shouldBe` ""
  it "[cli-allow-axiom] --allow-axiom admits a named axiom, in every command" $
    withTempDir $ \dir -> do
      file <- writeProgram dir "counter" (counterWithAxioms ["propext", "Mathlib.Custom.ax"])
      vecs <- writeVectors dir "counter" counterVectors
      without <- gin ["check", file]
      without `shouldExit` ExitFailure 1
      runErr without `shouldStartWith'` "certificate error:"
      runErr without `shouldContainText` "Mathlib.Custom.ax"
      let allow = ["--allow-axiom", "Mathlib.Custom.ax"]
      forM_
        [ ["check", file]
        , ["compile", file, "-o", dir </> "out"]
        , ["testbench", file, "--vectors", vecs, "-o", dir </> "out"]
        , ["sim", file, "--vectors", vecs]
        , ["check", file, "--allow-axiom", "Other.ax"]
        ]
        $ \args -> do
          r <- gin (args <> allow)
          (args, runCode r, runErr r) `shouldBe` (args, ExitSuccess, "")
  it "[cli-allow-axiom] --allow-axiom never admits sorryAx, kernel bypasses or ._native. axioms" $
    withTempDir $ \dir -> do
      forM_
        [ "sorryAx"
        , "Lean.ofReduceBool"
        , "Lean.ofReduceNat"
        , "Lean.trustCompiler"
        , "Counter.counter_correct._native.bv_decide.ax_1_3"
        ]
        $ \axiom -> do
          file <- writeProgram dir "counter" (counterWithAxioms ["propext", axiom])
          r <- gin ["check", file, "--allow-axiom", Text.unpack axiom]
          (axiom, runCode r) `shouldBe` (axiom, ExitFailure 1)
          runErr r `shouldStartWith'` "certificate error:"
          runErr r `shouldContainText` axiom
  it "[cli-allow-axiom] --allow-axiom sorryAx does not admit the sorry fixture" $ do
    r <- gin ["check", "test/fixtures/ir/sorry.gin.json", "--allow-axiom", "sorryAx"]
    r `shouldExit` ExitFailure 1
    runErr r `shouldStartWith'` "certificate error:"

----------------------------------------------------------------------
-- Vectors that do not fit the program

vectorsMismatchSpec :: Spec
vectorsMismatchSpec = describe "vectors that do not match the program" $ do
  it "[cli-vectors-mismatch] testbench, sim and validate reject swapped mac inputs" $
    withTempDir $ \dir -> do
      file <- writeProgram dir "mac" macProgram
      vecs <- writeVectors dir "mac" swappedMac
      let out = dir </> "out"
      forM_
        [ ["testbench", file, "--vectors", vecs, "-o", out]
        , ["sim", file, "--vectors", vecs]
        , ["validate", file, "--vectors", vecs, "-o", out, "--allow-missing-tools"]
        ]
        $ \args -> do
          r <- gin args
          (args, runCode r) `shouldBe` (args, ExitFailure 1)
          runErr r `shouldStartWith'` "driver error: "
          runErr r `shouldContainText` "input port 0"
          runOut r `shouldBe` ""
          doesDirectoryExist out `shouldReturn` False
  it "[cli-vectors-mismatch] rejects vectors for another top, port count or port type" $
    withTempDir $ \dir -> do
      file <- writeProgram dir "counter" counterProgram
      forM_
        [ (counterVectors {vecTop = "other"}, "top entity")
        , (counterVectors {vecOutputs = [Port "total" (bv 8)]}, "output port 0")
        , (counterWidth9, "output port 0")
        , (counterExtraInput, "input port")
        ]
        $ \(vs, needle) -> do
          vecs <- writeVectors dir "bad" vs
          r <- gin ["sim", file, "--vectors", vecs]
          (needle, runCode r) `shouldBe` (needle, ExitFailure 1)
          runErr r `shouldStartWith'` "driver error: "
          runErr r `shouldContainText` needle
  it "[cli-vectors-mismatch] reports undecodable vectors as a decode error" $
    withTempDir $ \dir -> do
      file <- writeProgram dir "counter" counterProgram
      vecs <- writeRaw dir "bad.vectors.json" "{\"format\": \"gin-vectors/2\"}"
      r <- gin ["sim", file, "--vectors", vecs]
      r `shouldExit` ExitFailure 1
      runErr r `shouldStartWith'` "decode error: "

----------------------------------------------------------------------
-- sim

simSpec :: Spec
simSpec = describe "sim" $ do
  it "[cli-sim] prints PASS for both simulators on matching vectors" $
    withTempDir $ \dir ->
      forM_
        [ ("counter", counterProgram, counterVectors)
        , ("mac", macProgram, macVectors)
        , ("detector", detectorProgram, detectorVectors)
        ]
        $ \(name, p, vs) -> do
          file <- writeProgram dir name p
          vecs <- writeVectors dir name vs
          r <- gin ["sim", file, "--vectors", vecs]
          (name, runCode r) `shouldBe` (name, ExitSuccess)
          (name, outLines r) `shouldBe` (name, ["sim-core: PASS", "sim-normal: PASS"])
  it "[cli-sim] prints the first mismatch of each simulator and returns 1" $
    withTempDir $ \dir -> do
      file <- writeProgram dir "counter" counterProgram
      vecs <- writeVectors dir "counter" (counterExpecting [(3, 9), (5, 200)])
      r <- gin ["sim", file, "--vectors", vecs]
      r `shouldExit` ExitFailure 1
      outLines r
        `shouldBe` [ "sim-core: FAIL cycle=3 port=count expected=9 got=2"
                   , "sim-normal: FAIL cycle=3 port=count expected=9 got=2"
                   ]
  it "[cli-sim] prints Bool values as true and false" $
    withTempDir $ \dir -> do
      file <- writeProgram dir "detector" detectorProgram
      vecs <- writeVectors dir "detector" detectorMissingHit
      r <- gin ["sim", file, "--vectors", vecs]
      r `shouldExit` ExitFailure 1
      outLines r
        `shouldBe` [ "sim-core: FAIL cycle=2 port=hit expected=false got=true"
                   , "sim-normal: FAIL cycle=2 port=hit expected=false got=true"
                   ]
  it "[cli-sim] replaces control characters from the input files in what it prints" $
    withTempDir $ \dir -> do
      let port = "count\ESC[2J"
          outputs t = t {topOutputs = [Port port (bv 8)]}
          wrong = counterExpecting [(3, 9)]
      file <- writeProgram dir "counter" (withTop outputs counterProgram)
      vecs <- writeVectors dir "counter" wrong {vecOutputs = [Port port (bv 8)]}
      r <- gin ["sim", file, "--vectors", vecs]
      r `shouldExit` ExitFailure 1
      outLines r
        `shouldBe` [ "sim-core: FAIL cycle=3 port=count?[2J expected=9 got=2"
                   , "sim-normal: FAIL cycle=3 port=count?[2J expected=9 got=2"
                   ]
  it "[cli-sim] reports an exceeded core simulator bound as inconclusive, not as a failure" $
    withTempDir $ \dir -> do
      file <- writeProgram dir "doubling" (doublingProgram 18)
      vecs <- writeVectors dir "doubling" doublingVectors
      r <- gin ["sim", file, "--vectors", vecs]
      r `shouldExit` ExitSuccess
      case outLines r of
        [core, normal] -> do
          core `shouldStartWith'` "sim-core: SKIP(inconclusive: "
          core `shouldContainText` "evaluation steps"
          normal `shouldBe` "sim-normal: PASS"
        ls -> expectationFailure ("expected two lines, got " <> show ls)

----------------------------------------------------------------------
-- validate

validateSpec :: Spec
validateSpec = describe "validate" $ do
  itWithTools hdlTools "[cli-validate] passes every check for every target on counter" $
    withTempDir $ \dir -> do
      file <- writeProgram dir "counter" counterProgram
      vecs <- writeVectors dir "counter" counterVectors
      env <- getEnvironment
      cwdBefore <- sort <$> listDirectory "."
      r <- ginWith env ["validate", file, "--vectors", vecs]
      r `shouldExit` ExitSuccess
      outLines r
        `shouldBe` [ "sim-core: PASS"
                   , "sim-normal: PASS"
                   , "verilog-lint: PASS"
                   , "verilog-run: PASS"
                   , "systemverilog-lint: PASS"
                   , "systemverilog-run: PASS"
                   , "vhdl-lint: PASS"
                   , "vhdl-run: PASS"
                   ]
      -- Without -o the generated files live only in temporary directories.
      cwdAfter <- sort <$> listDirectory "."
      cwdAfter `shouldBe` cwdBefore
  itWithTools hdlTools "[cli-validate] keeps the generated files in DIR with -o" $
    withTempDir $ \dir -> do
      file <- writeProgram dir "mac" macProgram
      vecs <- writeVectors dir "mac" macVectors
      env <- getEnvironment
      let out = dir </> "out"
      r <- ginWith env ["validate", file, "--vectors", vecs, "-o", out, "--target", "vhdl"]
      r `shouldExit` ExitSuccess
      outLines r
        `shouldBe` ["sim-core: PASS", "sim-normal: PASS", "vhdl-lint: PASS", "vhdl-run: PASS"]
      sort <$> listDirectory out `shouldReturn` ["mac.vhd", "mac_tb.vhd"]
  itWithTools verilogTools "[cli-validate] fails the HDL run when the vectors are wrong" $
    withTempDir $ \dir -> do
      file <- writeProgram dir "counter" counterProgram
      vecs <- writeVectors dir "counter" (counterExpecting [(3, 9)])
      env <- getEnvironment
      r <- ginWith env ["validate", file, "--vectors", vecs, "--target", "verilog"]
      r `shouldExit` ExitFailure 1
      case outLines r of
        [core, normal, lint, run] -> do
          core `shouldStartWith'` "sim-core: FAIL cycle=3"
          normal `shouldStartWith'` "sim-normal: FAIL cycle=3"
          lint `shouldBe` "verilog-lint: PASS"
          run `shouldStartWith'` "verilog-run: FAIL"
        ls -> expectationFailure ("expected four lines, got " <> show ls)
      runErr r `shouldContainText` "GIN-MISMATCH"
  itWithTools (verilogTools <> ["perl"]) "[cli-validate] fails the checks whose tool is missing" $
    withTempDir $ \dir -> do
      file <- writeProgram dir "counter" counterProgram
      vecs <- writeVectors dir "counter" counterVectors
      bin <- linkTools dir ["iverilog", "vvp", "verilator", "perl"]
      let args = ["validate", file, "--vectors", vecs, "--target", "verilog", "--target", "vhdl"]
      r <- ginWith [("PATH", bin)] args
      r `shouldExit` ExitFailure 1
      outLines r
        `shouldBe` [ "sim-core: PASS"
                   , "sim-normal: PASS"
                   , "verilog-lint: PASS"
                   , "verilog-run: PASS"
                   , "vhdl-lint: FAIL missing tool: nvc"
                   , "vhdl-run: FAIL missing tool: nvc"
                   ]
      skipped <- ginWith [("PATH", bin)] (args <> ["--allow-missing-tools"])
      skipped `shouldExit` ExitSuccess
      drop 4 (outLines skipped)
        `shouldBe` ["vhdl-lint: SKIP(missing tool: nvc)", "vhdl-run: SKIP(missing tool: nvc)"]
  it "[cli-validate] skips every HDL check without tools when missing tools are allowed" $
    withTempDir $ \dir -> do
      file <- writeProgram dir "counter" counterProgram
      vecs <- writeVectors dir "counter" counterVectors
      empty <- linkTools dir []
      let args = ["validate", file, "--vectors", vecs, "--target", "systemverilog"]
      failed <- ginWith [("PATH", empty)] args
      failed `shouldExit` ExitFailure 1
      outLines failed
        `shouldBe` [ "sim-core: PASS"
                   , "sim-normal: PASS"
                   , "systemverilog-lint: FAIL missing tools: verilator, iverilog"
                   , "systemverilog-run: FAIL missing tools: iverilog, vvp"
                   ]
      -- No PATH at all is the same as an empty one.
      skipped <- ginWith [] (args <> ["--allow-missing-tools"])
      skipped `shouldExit` ExitSuccess
      outLines skipped
        `shouldBe` [ "sim-core: PASS"
                   , "sim-normal: PASS"
                   , "systemverilog-lint: SKIP(missing tools: verilator, iverilog)"
                   , "systemverilog-run: SKIP(missing tools: iverilog, vvp)"
                   ]
  -- The lint tools and iverilog are fakes that succeed; the fake vvp stands
  -- for a testbench run, and the run check must follow the pass rule of
  -- docs/semantics.md exactly.
  forM_ passRuleCases $ \(what, vvp, verdict) ->
    it ("[cli-validate] judges a testbench run that " <> what) $
      withTempDir $ \dir -> do
        file <- writeProgram dir "counter" counterProgram
        vecs <- writeVectors dir "counter" counterVectors
        bin <- fakeTools dir [("verilator", "exit 0"), ("iverilog", "exit 0"), ("vvp", vvp)]
        r <- ginWith [("PATH", bin)] ["validate", file, "--vectors", vecs, "--target", "verilog"]
        r `shouldExit` (if verdict == "PASS" then ExitSuccess else ExitFailure 1)
        outLines r
          `shouldBe` [ "sim-core: PASS"
                     , "sim-normal: PASS"
                     , "verilog-lint: PASS"
                     , "verilog-run: " <> verdict
                     ]

-- | What a fake @vvp@ does for counter's vectors, and the outcome of the run
-- check: @PASS@ or @FAIL <reason>@.
passRuleCases :: [(String, String, Text)]
passRuleCases =
  [ ("prints GIN-PASS with the cycle count among other output", say (progress <> [pass]), "PASS")
  , ( "prints GIN-PASS, and GIN-MISMATCH and GIN-FAIL only on standard error"
    , say [pass] <> warn ["GIN-MISMATCH t=0 port=count expected=0 got=1", "GIN-FAIL mismatches=1"]
    , "PASS"
    )
  , ("exits 0 without printing GIN-PASS", say progress, noPass "0")
  , ("prints no output at all", "exit 0", noPass "0")
  , ("prints GIN-PASS twice", say [pass, pass], noPass "2")
  , ("counts one cycle too few", say [passWith (cycles - 1)], wrongCount "GIN-PASS cycles=7")
  , ( "counts a number that only starts with the cycle count"
    , say [passWith (cycles * 10)]
    , wrongCount "GIN-PASS cycles=80"
    )
  , ("prints GIN-PASS without a count", say ["GIN-PASS"], wrongCount "GIN-PASS")
  , ("prints GIN-PASS and exits 1", say [pass] <> "; exit 1", "FAIL vvp exited with code 1")
  , ( "prints GIN-PASS and is killed"
    , say [pass] <> "; kill -9 $$"
    , "FAIL vvp was stopped by signal 9"
    )
  , ( "prints GIN-PASS after a GIN-MISMATCH line"
    , say ["GIN-MISMATCH t=3 port=count expected=2 got=9", pass]
    , "FAIL vvp printed GIN-MISMATCH t=3 port=count expected=2 got=9"
    )
  , ( "prints GIN-PASS and a GIN-FAIL line"
    , say [pass, "GIN-FAIL mismatches=1"]
    , "FAIL vvp printed GIN-FAIL mismatches=1"
    )
  ]
  where
    cycles = length (vecCycles counterVectors)
    passWith n = "GIN-PASS cycles=" <> show n
    pass = passWith cycles
    progress = ["VCD info: dumpfile tb.vcd opened for output."]
    say ls = intercalate "; " ["echo '" <> l <> "'" | l <- ls]
    warn ls = concat ["; echo '" <> l <> "' >&2" | l <- ls]
    noPass n = "FAIL vvp printed " <> n <> " GIN-PASS lines, expected one"
    wrongCount l = "FAIL vvp printed " <> l <> ", expected cycles=8"

timeoutSpec :: Spec
timeoutSpec = describe "tool timeout" $
  it "[cli-timeout] stops a tool that runs longer than --tool-timeout and reports FAIL" $
    withTempDir $ \dir -> do
      file <- writeProgram dir "counter" counterProgram
      vecs <- writeVectors dir "counter" counterVectors
      fake <- fakeTools dir [("nvc", "sleep 30")]
      start <- getMonotonicTime
      r <-
        ginWith
          [("PATH", fake <> ":/bin:/usr/bin")]
          ["validate", file, "--vectors", vecs, "--target", "vhdl", "--tool-timeout", "1"]
      elapsed <- subtract start <$> getMonotonicTime
      r `shouldExit` ExitFailure 1
      outLines r
        `shouldBe` [ "sim-core: PASS"
                   , "sim-normal: PASS"
                   , "vhdl-lint: FAIL nvc timed out after 1 s"
                   , "vhdl-run: FAIL nvc timed out after 1 s"
                   ]
      -- Two runs of 1 s each, plus a grace period for the killed tool to exit;
      -- the fake would otherwise sleep 30 s per run.
      unless (elapsed < 20) $
        expectationFailure ("validate took " <> show elapsed <> " s")

----------------------------------------------------------------------
-- Running the CLI

-- | What one CLI invocation returned and printed.
data Run = Run
  { runCode :: ExitCode
  , runOut :: Text
  , runErr :: Text
  }
  deriving stock (Show)

-- | Run the CLI in an environment without external tools.
gin :: [String] -> IO Run
gin = ginWith [("PATH", "")]

-- | Run the CLI with the given environment, capturing standard output and
-- standard error.
ginWith :: [(String, String)] -> [String] -> IO Run
ginWith env args = withTempDir $ \dir -> do
  ((code, err), out) <-
    redirect stdout (dir </> "stdout") (redirect stderr (dir </> "stderr") (runCliWith env args))
  pure (Run code out err)

-- | Point a standard handle at a file while the action runs, and return what
-- was written to it.
redirect :: Handle -> FilePath -> IO a -> IO (a, Text)
redirect h file act = do
  hFlush h
  a <- withBinaryFile file WriteMode $ \fh ->
    bracket (hDuplicate h) (\saved -> hFlush h >> hDuplicateTo saved h >> hClose saved) $ \_ ->
      hDuplicateTo fh h >> act
  (,) a <$> readText file

outLines :: Run -> [Text]
outLines = Text.lines . runOut

shouldExit :: Run -> ExitCode -> Expectation
shouldExit r code =
  unless (runCode r == code) $
    expectationFailure ("expected " <> show code <> ", got " <> show r)

shouldStartWith' :: Text -> Text -> Expectation
shouldStartWith' actual prefix =
  unless (prefix `Text.isPrefixOf` actual) $
    expectationFailure (show actual <> " does not start with " <> show prefix)

shouldContainText :: Text -> Text -> Expectation
shouldContainText actual needle =
  unless (needle `Text.isInfixOf` actual) $
    expectationFailure (show actual <> " does not contain " <> show needle)

----------------------------------------------------------------------
-- Fixtures

hdlTools, verilogTools :: [String]
hdlTools = verilogTools <> ["nvc"]
verilogTools = ["iverilog", "vvp", "verilator"]

writeProgram :: FilePath -> String -> Program -> IO FilePath
writeProgram dir name p = do
  let file = dir </> (name <> ".gin.json")
  LBS.writeFile file (encodeProgram p)
  pure file

writeVectors :: FilePath -> String -> Vectors -> IO FilePath
writeVectors dir name vs = do
  let file = dir </> (name <> ".vectors.json")
  LBS.writeFile file (encodeVectors vs)
  pure file

writeRaw :: FilePath -> FilePath -> Text -> IO FilePath
writeRaw dir name content = do
  let file = dir </> name
  BS.writeFile file (Text.encodeUtf8 content)
  pure file

readText :: FilePath -> IO Text
readText file = Text.decodeUtf8 <$> BS.readFile file

netlistOf :: Program -> IO Module
netlistOf p = case normalize p >>= buildNetlist of
  Right m -> pure m
  Left e -> fail ("fixture does not compile: " <> show e)

-- | A directory holding links to the named tools, as found on this process's
-- @PATH@, and nothing else.
linkTools :: FilePath -> [String] -> IO FilePath
linkTools dir tools = do
  let bin = dir </> "tools"
  createDirectory bin
  forM_ tools $ \t ->
    findExecutable t >>= \case
      Just path -> createFileLink path (bin </> t)
      Nothing -> expectationFailure ("tool not found: " <> t)
  pure bin

-- | A directory holding fake tools, each a @/bin/sh@ script with the given
-- body, and nothing else.
fakeTools :: FilePath -> [(String, String)] -> IO FilePath
fakeTools dir tools = do
  let bin = dir </> "fake"
  createDirectory bin
  forM_ tools $ \(name, body) -> do
    let exe = bin </> name
    writeFile exe ("#!/bin/sh\n" <> body <> "\n")
    perms <- getPermissions exe
    setPermissions exe (setOwnerExecutable True perms)
  pure bin

withTop :: (TopEntity -> TopEntity) -> Program -> Program
withTop f p = p {progTop = f (progTop p)}

-- | counter whose top definition does not exist: a type error.
missingTopDef :: Program
missingTopDef = withTop (\t -> t {topDef = "Counter.missing"}) counterProgram

-- | counter with its input port named @clk@: it type checks, but the port
-- collides with the clock every module gets.
clockPort :: Program
clockPort = withTop (\t -> t {topInputs = [Port "clk" TBool]}) counterProgram

counterWithAxioms :: [Text] -> Program
counterWithAxioms axioms =
  counterProgram {progCertificate = (progCertificate counterProgram) {certAxioms = axioms}}

-- | counter's vectors with the expected count replaced at the given cycles.
counterExpecting :: [(Int, Integer)] -> Vectors
counterExpecting changes =
  counterVectors {vecCycles = zipWith adjust [0 ..] (vecCycles counterVectors)}
  where
    adjust t c = maybe c (\n -> c {cycOutputs = [VBV 8 n]}) (lookup t changes)

-- | counter's vectors with a 9-bit count.
counterWidth9 :: Vectors
counterWidth9 =
  counterVectors
    { vecOutputs = [Port "count" (bv 9)]
    , vecCycles =
        [c {cycOutputs = [VBV 9 n | VBV _ n <- cycOutputs c]} | c <- vecCycles counterVectors]
    }

-- | counter's vectors with a second input.
counterExtraInput :: Vectors
counterExtraInput =
  counterVectors
    { vecInputs = vecInputs counterVectors <> [Port "clear" TBool]
    , vecCycles = [c {cycInputs = cycInputs c <> [VBool False]} | c <- vecCycles counterVectors]
    }

-- | mac's vectors with the inputs @x@ and @y@ swapped.
swappedMac :: Vectors
swappedMac =
  macVectors
    { vecInputs = reverse (vecInputs macVectors)
    , vecCycles = [c {cycInputs = reverse (cycInputs c)} | c <- vecCycles macVectors]
    }

-- | detector's vectors without the match at cycle 2.
detectorMissingHit :: Vectors
detectorMissingHit =
  detectorVectors {vecCycles = zipWith adjust [0 :: Int ..] (vecCycles detectorVectors)}
  where
    adjust t c = if t == 2 then c {cycOutputs = [VBool False]} else c

-- | @g0 v = v@ and @gi v = g(i-1) (g(i-1) v)@, with @gk@ lifted over the
-- input: the identity, which normalizes to no binds at all but costs the
-- core simulator about @7 * 2^k@ evaluation steps a cycle.
doublingProgram :: Int -> Program
doublingProgram k =
  Program
    { progProducer = Producer "gin-driver-spec" "n/a"
    , progTop =
        TopEntity
          { topName = "doubling"
          , topDomain = sysDomain
          , topInputs = [Port "x" (bv 8)]
          , topOutputs = [Port "o" (bv 8)]
          , topDef = "D.top"
          }
    , progDefs = Def "D.top" (TFun (sig (bv 8)) (sig (bv 8))) top : fmap g [0 .. k]
    , progCertificate = testCertificate "D.top_correct"
    }
  where
    name i = Name (Text.pack ("D.g" <> show i))
    fn = TFun (bv 8) (bv 8)
    lift1 = EPrim (SigLift 1) (tFuns [fn, sig (bv 8)] (sig (bv 8)))
    top = ELam [("x", sig (bv 8))] (EApp lift1 [EGlobal (name k), EVar "x"])
    g i = Def (name i) fn (ELam [("v", bv 8)] (body i))
    body i
      | i <= 0 = EVar "v"
      | otherwise = EApp (EGlobal (name (i - 1))) [EApp (EGlobal (name (i - 1))) [EVar "v"]]

doublingVectors :: Vectors
doublingVectors =
  Vectors
    { vecTop = "doubling"
    , vecInputs = [Port "x" (bv 8)]
    , vecOutputs = [Port "o" (bv 8)]
    , vecCycles = [Cycle [VBV 8 n] [VBV 8 n] | n <- [7, 9]]
    }
