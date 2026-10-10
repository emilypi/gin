module Gin.DriverSpec (spec) where

import Control.Concurrent (forkIO, killThread, threadDelay, yield)
import Control.Concurrent.MVar (MVar, newEmptyMVar, putMVar, tryReadMVar)
import Control.Exception (IOException, bracket, finally, try)
import Control.Monad (filterM, forM_, unless, void, when)
import Data.ByteString qualified as BS
import Data.ByteString.Lazy qualified as LBS
import Data.Char (GeneralCategory (..), generalCategory)
import Data.Either (fromRight)
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
import Gin.Certificate (certificateSpecHash)
import Gin.Core.Json (decodeProgram, encodeProgram, encodeVectors)
import Gin.Core.Syntax
import Gin.Driver (runCliWith)
import Gin.Error (renderError)
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
  , doesFileExist
  , findExecutable
  , getPermissions
  , listDirectory
  , pathIsSymbolicLink
  , removeFile
  , renamePath
  , setOwnerExecutable
  , setPermissions
  )
import System.Environment (getEnvironment)
import System.Exit (ExitCode (..))
import System.FilePath ((</>))
import System.IO (Handle, IOMode (..), hClose, hFlush, stderr, stdout, withBinaryFile)
import System.Process (readProcessWithExitCode)
import Test.Hspec

spec :: Spec
spec = do
  exitCodeSpec
  compileFilesSpec
  certificateSpec
  specHashSpec
  vectorsMismatchSpec
  simSpec
  escapeSpec
  validateSpec
  minCyclesSpec
  toolsLineSpec
  timeoutSpec
  simTimeoutSpec
  toolEnvSpec
  processGroupSpec
  atomicSpec

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
  it "[check-ports] check and compile both reject a top entity named clk or rst" $
    withTempDir $ \dir ->
      forM_ ["clk", "rst"] $ \name -> do
        let p = counterProgram{progTop = (progTop counterProgram){topName = name}}
        file <- writeProgram dir (Text.unpack name) p
        c <- gin ["check", file]
        c `shouldExit` ExitFailure 1
        runErr c `shouldStartWith'` "type error: "
        runErr c `shouldContainText` ("top name " <> name <> " is reserved")
        let out = dir </> ("out-" <> Text.unpack name)
        k <- gin ["compile", file, "-o", out, "--target", "verilog"]
        k `shouldExit` ExitFailure 1
        runErr k `shouldStartWith'` "type error: "
        doesDirectoryExist out `shouldReturn` False
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
        , ["sim", file, "--vectors", vecs, "--sim-timeout", "0"]
        , ["validate", file, "--vectors", vecs, "--sim-timeout", "later"]
        , ["validate", file, "--vectors", vecs, "--min-cycles", "0"]
        , ["validate", file, "--vectors", vecs, "--min-cycles", "-1"]
        , ["validate", file, "--vectors", vecs, "--min-cycles", "many"]
        , ["check", file, "--spec-hash"]
        , ["compile", file, "--sim-timeout", "1"]
        , ["sim", file, "--vectors", vecs, "--min-cycles", "1"]
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
    forM_
      [ "--vectors"
      , "--target"
      , "--allow-axiom"
      , "--spec-hash"
      , "--allow-missing-tools"
      , "--tool-timeout"
      , "--sim-timeout"
      , "--min-cycles"
      ]
      $ shouldContainText (runOut v)
    c <- gin ["check", "--help"]
    runOut c `shouldContainText` "--spec-hash"

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
        [ (["compile", clash], "type error: ")
        , (["compile", sorry], "certificate error: ")
        , (["testbench", clash, "--vectors", vecs], "type error: ")
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
-- Traces (@Certificate@ in the code, @"certificate"@ in the JSON)

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
  it "[cert-normalize] --allow-axiom rejects empty names and control characters as usage errors" $
    withTempDir $ \dir -> do
      file <- writeProgram dir "counter" counterProgram
      forM_ ["", " ", "\t", "\171\187", "Foo.ax\n", "Foo\ESC[2J.ax", "Foo.\8238ax", "\8203"] $
        \name -> do
          r <- gin ["check", file, "--allow-axiom", name]
          (name, runCode r) `shouldBe` (name, ExitFailure 2)
          (name, runOut r) `shouldBe` (name, "")
          runErr r `shouldContainText` "--allow-axiom"
          runErr r `shouldContainText` "Usage: gin"
  it "[cert-normalize] --allow-axiom matches names after normalization" $
    withTempDir $ \dir -> do
      file <- writeProgram dir "counter" (counterWithAxioms ["propext", "Mathlib.\171Custom\187.ax"])
      r <- gin ["check", file, "--allow-axiom", " \171Mathlib\187.Custom.ax "]
      (runCode r, runErr r) `shouldBe` (ExitSuccess, "")
  it "[cert-normalize] no spelling of sorryAx or a kernel bypass gets past --allow-axiom" $
    withTempDir $ \dir ->
      forM_ ["\171sorryAx\187", " sorryAx ", "\171Lean\187.\171ofReduceBool\187", "Lean.\171trustCompiler\187"] $
        \axiom -> do
          file <- writeProgram dir "counter" (counterWithAxioms ["propext", Text.pack axiom])
          r <- gin ["check", file, "--allow-axiom", axiom]
          (axiom, runCode r) `shouldBe` (axiom, ExitFailure 1)
          runErr r `shouldStartWith'` "certificate error:"
          runErr r `shouldContainText` "never allowed"

----------------------------------------------------------------------
-- Pinning the specification

specHashSpec :: Spec
specHashSpec = describe "--spec-hash" $ do
  it "[cli-spec-hash] accepts the certificate's specification hash, in either case, on every command" $
    withTempDir $ \dir -> do
      p <- decodeFixture specFixture
      file <- writeProgram dir "counter" p
      vecs <- writeVectors dir "counter" counterVectors
      let hash = certificateSpecHash (progCertificate p)
      forM_ [hash, Text.toUpper hash] $ \h ->
        forM_ (everyCommand file vecs (dir </> "out")) $ \args -> do
          r <- gin (args <> ["--spec-hash", Text.unpack h])
          (args, runCode r, runErr r) `shouldBe` (args, ExitSuccess, "")
  it "[cli-spec-hash] rejects any other hash with a certificate error naming both, on every command" $
    withTempDir $ \dir -> do
      p <- decodeFixture specFixture
      file <- writeProgram dir "counter" p
      vecs <- writeVectors dir "counter" counterVectors
      let hash = certificateSpecHash (progCertificate p)
          unreviewed = certificateSpecHash (progCertificate counterProgram)
          oneDigitOff = Text.init hash <> (if Text.takeEnd 1 hash == "0" then "1" else "0")
          out = dir </> "out"
      oneDigitOff `shouldNotBe` hash
      forM_ [unreviewed, oneDigitOff, "not-a-hash"] $ \wrong ->
        forM_ (everyCommand file vecs out) $ \args -> do
          r <- gin (args <> ["--spec-hash", Text.unpack wrong])
          (args, runCode r) `shouldBe` (args, ExitFailure 1)
          runErr r `shouldStartWith'` "certificate error:"
          runErr r `shouldContainText` hash
          runErr r `shouldContainText` wrong
          runOut r `shouldBe` ""
          doesDirectoryExist out `shouldReturn` False
  it "[cli-spec-hash] identifies the claim, not the axioms or the implementation" $
    withTempDir $ \dir -> do
      p <- decodeFixture specFixture
      let hash = Text.unpack (certificateSpecHash (progCertificate p))
          moreAxioms = p {progCertificate = (progCertificate p) {certAxioms = ["propext", "Quot.sound"]}}
      sameClaim <- writeProgram dir "axioms" moreAxioms
      r <- gin ["check", sameClaim, "--spec-hash", hash]
      (runCode r, runErr r) `shouldBe` (ExitSuccess, "")
      otherSpec <-
        writeProgram dir "spec" $
          p {progCertificate = (progCertificate p) {certSpecDefs = take 1 (certSpecDefs (progCertificate p))}}
      r' <- gin ["check", otherSpec, "--spec-hash", hash]
      r' `shouldExit` ExitFailure 1
      runErr r' `shouldStartWith'` "certificate error:"

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
-- Untrusted text in the output

escapeSpec :: Spec
escapeSpec = describe "text from the input files" $ do
  forM_ hostileBreaks $ \(what, c) -> do
    it ("[cli-escape] reports a port name containing " <> what <> " on escaped lines") $
      withTempDir $ \dir -> do
        let port = "count" <> c <> "sim-core: PASS"
        file <- writeProgram dir "counter" (withTop (\t -> t {topOutputs = [Port port (bv 8)]}) counterProgram)
        r <- gin ["check", file]
        r `shouldExit` ExitFailure 1
        runOut r `shouldBe` ""
        errorLines "type error: illegal port name " r
    it ("[cli-escape] reports a top name containing " <> what <> " on escaped lines") $
      withTempDir $ \dir -> do
        file <- writeProgram dir "counter" (withTop (\t -> t {topName = "counter" <> c <> "x"}) counterProgram)
        r <- gin ["check", file]
        r `shouldExit` ExitFailure 1
        errorLines "type error: illegal top name " r
    it ("[cli-escape] reports an axiom name containing " <> what <> " on escaped lines") $
      withTempDir $ \dir -> do
        file <- writeProgram dir "counter" (counterWithAxioms ["propext", "evil" <> c <> "sim-core: PASS"])
        r <- gin ["check", file]
        r `shouldExit` ExitFailure 1
        errorLines "certificate error: axiom " r
    it ("[cli-escape] reports a vectors top name containing " <> what <> " on escaped lines") $
      withTempDir $ \dir -> do
        file <- writeProgram dir "counter" counterProgram
        vecs <- writeVectors dir "counter" counterVectors {vecTop = "counter" <> c <> "sim-core: PASS"}
        r <- gin ["sim", file, "--vectors", vecs]
        r `shouldExit` ExitFailure 1
        runOut r `shouldBe` ""
        errorLines "driver error: the vectors are for top entity " r
  it "[cli-escape] keeps one sim line per check when a definition name contains line breaks" $
    withTempDir $ \dir -> do
      file <- writeProgram dir "forged" (constantBudgetProgram forgedName)
      vecs <- writeVectors dir "forged" constantBudgetVectors
      r <- gin ["sim", file, "--vectors", vecs]
      r `shouldExit` ExitSuccess
      case outLines r of
        [core, normal] -> do
          core `shouldStartWith'` "sim-core: SKIP(inconclusive: "
          core `shouldContainText` "in def D.c\\u{a}sim-normal: PASS\\u{a}verilog-lint: PASS"
          Text.takeEnd 1 core `shouldBe` ")"
          normal `shouldBe` "sim-normal: PASS"
        ls -> expectationFailure ("expected two lines, got " <> show ls)
  it "[cli-escape] keeps validate's lines parseable whatever the definition and theorem names" $
    withTempDir $ \dir -> do
      let p = constantBudgetProgram forgedName
          forgedTheorem = "D.ok\nverilog-run: PASS\r\ESC[1A\8238"
      file <- writeProgram dir "forged" p {progCertificate = testCertificate forgedTheorem}
      vecs <- writeVectors dir "forged" constantBudgetVectors
      r <- gin ["validate", file, "--vectors", vecs, "--target", "verilog", "--allow-missing-tools"]
      r `shouldExit` ExitSuccess
      length (outLines r) `shouldBe` 6
      forM_ (outLines r) $ \l -> (l, isOutputLine l) `shouldBe` (l, True)
      forM_ [runOut r, runErr r] $ \t ->
        Text.filter (\c -> c /= '\n' && hiddenChar c) t `shouldBe` ""
  where
    forgedName = "D.c\nsim-normal: PASS\nverilog-lint: PASS\nverilog-run: PASS\nX"

-- | Characters that end, rewrite or reorder a terminal line.
hostileBreaks :: [(String, Text)]
hostileBreaks =
  [ ("a line feed", "\n")
  , ("a carriage return", "\r")
  , ("an escape sequence", "\ESC[2K")
  , ("a bidirectional override", "\8238")
  , ("a line separator", "\8232")
  ]

-- | Standard error holds one error line starting with the prefix, then only
-- indented context lines, and no character that could break a line.
errorLines :: Text -> Run -> Expectation
errorLines prefix r = case Text.lines (runErr r) of
  first : contextLines -> do
    first `shouldStartWith'` prefix
    forM_ contextLines $ \l -> l `shouldStartWith'` "  "
    (first, Text.filter hiddenChar first) `shouldBe` (first, "")
    Text.filter (\c -> c /= '\n' && hiddenChar c) (runErr r) `shouldBe` ""
  [] -> expectationFailure "expected an error on standard error"

-- | Characters in the Unicode categories Cc, Cf, Zl, Zp, Cs, Co and Cn.
hiddenChar :: Char -> Bool
hiddenChar c =
  generalCategory c
    `elem` [Control, Format, LineSeparator, ParagraphSeparator, Surrogate, PrivateUse, NotAssigned]

-- | A line sim or validate prints: the vectors line, the tools line, or a
-- known check with PASS, FAIL and a reason, or SKIP(reason).
isOutputLine :: Text -> Bool
isOutputLine l = case Text.breakOn ": " l of
  ("tools", _) -> True
  (name, rest) | name `elem` checkNames -> verdict (Text.drop 2 rest)
  _ -> False
  where
    checkNames =
      ["vectors", "sim-core", "sim-normal"]
        <> [t <> "-" <> k | t <- ["verilog", "systemverilog", "vhdl"], k <- ["lint", "run"]]
    verdict v =
      v == "PASS"
        || "PASS cycles=" `Text.isPrefixOf` v
        || "FAIL " `Text.isPrefixOf` v
        || ("SKIP(" `Text.isPrefixOf` v && ")" `Text.isSuffixOf` v)

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
      take 1 (outLines r) `shouldBe` ["vectors: PASS cycles=8"]
      checkLines r
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
      checkLines r
        `shouldBe` ["sim-core: PASS", "sim-normal: PASS", "vhdl-lint: PASS", "vhdl-run: PASS"]
      sort <$> listDirectory out `shouldReturn` ["mac.vhd", "mac_tb.vhd"]
  itWithTools verilogTools "[cli-validate] fails the HDL run when the vectors are wrong" $
    withTempDir $ \dir -> do
      file <- writeProgram dir "counter" counterProgram
      vecs <- writeVectors dir "counter" (counterExpecting [(3, 9)])
      env <- getEnvironment
      r <- ginWith env ["validate", file, "--vectors", vecs, "--target", "verilog"]
      r `shouldExit` ExitFailure 1
      case checkLines r of
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
      checkLines r
        `shouldBe` [ "sim-core: PASS"
                   , "sim-normal: PASS"
                   , "verilog-lint: PASS"
                   , "verilog-run: PASS"
                   , "vhdl-lint: FAIL missing tool: nvc"
                   , "vhdl-run: FAIL missing tool: nvc"
                   ]
      skipped <- ginWith [("PATH", bin)] (args <> ["--allow-missing-tools"])
      skipped `shouldExit` ExitSuccess
      drop 4 (checkLines skipped)
        `shouldBe` ["vhdl-lint: SKIP(missing tool: nvc)", "vhdl-run: SKIP(missing tool: nvc)"]
  it "[cli-validate] skips every HDL check without tools when missing tools are allowed" $
    withTempDir $ \dir -> do
      file <- writeProgram dir "counter" counterProgram
      vecs <- writeVectors dir "counter" counterVectors
      empty <- linkTools dir []
      let args = ["validate", file, "--vectors", vecs, "--target", "systemverilog"]
      failed <- ginWith [("PATH", empty)] args
      failed `shouldExit` ExitFailure 1
      checkLines failed
        `shouldBe` [ "sim-core: PASS"
                   , "sim-normal: PASS"
                   , "systemverilog-lint: FAIL missing tools: verilator, iverilog"
                   , "systemverilog-run: FAIL missing tools: iverilog, vvp"
                   ]
      -- No PATH at all is the same as an empty one.
      skipped <- ginWith [] (args <> ["--allow-missing-tools"])
      skipped `shouldExit` ExitSuccess
      checkLines skipped
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
        checkLines r
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

minCyclesSpec :: Spec
minCyclesSpec = describe "validate --min-cycles" $ do
  it "[cli-min-cycles] first prints the number of vector cycles, which passes by default" $
    withTempDir $ \dir -> do
      file <- writeProgram dir "counter" counterProgram
      vecs <- writeVectors dir "counter" counterVectors
      r <- gin ["validate", file, "--vectors", vecs, "--target", "verilog", "--allow-missing-tools"]
      r `shouldExit` ExitSuccess
      take 1 (outLines r) `shouldBe` ["vectors: PASS cycles=8"]
  it "[cli-min-cycles] passes vectors with exactly --min-cycles cycles" $
    withTempDir $ \dir -> do
      file <- writeProgram dir "counter" counterProgram
      vecs <- writeVectors dir "counter" counterVectors
      r <- gin (validateArgs file vecs <> ["--min-cycles", "8"])
      r `shouldExit` ExitSuccess
      take 1 (outLines r) `shouldBe` ["vectors: PASS cycles=8"]
  it "[cli-min-cycles] fails vectors with fewer cycles than --min-cycles, and still runs the checks" $
    withTempDir $ \dir -> do
      file <- writeProgram dir "counter" counterProgram
      vecs <- writeVectors dir "counter" counterVectors
      forM_ [("9", "9"), ("1024", "1024"), ("0001024", "1024")] $ \(arg, shown) -> do
        r <- gin (validateArgs file vecs <> ["--min-cycles", arg])
        r `shouldExit` ExitFailure 1
        take 1 (outLines r) `shouldBe` ["vectors: FAIL cycles=8 < " <> shown]
        checkLines r
          `shouldBe` [ "sim-core: PASS"
                     , "sim-normal: PASS"
                     , "verilog-lint: SKIP(missing tools: verilator, iverilog)"
                     , "verilog-run: SKIP(missing tools: iverilog, vvp)"
                     ]
  where
    validateArgs file vecs =
      ["validate", file, "--vectors", vecs, "--target", "verilog", "--allow-missing-tools"]

toolsLineSpec :: Spec
toolsLineSpec = describe "validate's tools line" $ do
  itWithTools hdlTools "[cli-tools-line] names the version of every HDL tool it runs" $
    withTempDir $ \dir -> do
      file <- writeProgram dir "counter" counterProgram
      vecs <- writeVectors dir "counter" counterVectors
      env <- getEnvironment
      r <- ginWith env ["validate", file, "--vectors", vecs, "--target", "systemverilog"]
      r `shouldExit` ExitSuccess
      case drop 1 (outLines r) of
        tools : _ -> do
          tools `shouldStartWith'` "tools: verilator Verilator 5."
          forM_ [", iverilog Icarus Verilog version ", ", vvp Icarus Verilog runtime version "] $
            shouldContainText tools
        [] -> expectationFailure "expected a tools line"
  it "[cli-tools-line] shows the first line each tool prints for -V or --version" $
    withTempDir $ \dir -> do
      file <- writeProgram dir "counter" counterProgram
      vecs <- writeVectors dir "counter" counterVectors
      bin <-
        fakeTools
          dir
          [ ("verilator", "echo; echo \"  Verilator 5.052 fake $*  \"; echo second line")
          , ("iverilog", "echo \"Icarus fake $*\" >&2")
          , ("vvp", "echo \"vvp fake $*\"; echo 'GIN-PASS cycles=8'")
          , ("nvc", "printf 'nvc \\033[2J\\342\\200\\256 fake\\n'")
          ]
      r <- ginWith [("PATH", bin)] ["validate", file, "--vectors", vecs]
      take 2 (outLines r)
        `shouldBe` [ "vectors: PASS cycles=8"
                   , "tools: verilator Verilator 5.052 fake --version, iverilog Icarus fake -V, \
                     \vvp vvp fake -V, nvc nvc \\u{1b}[2J\\u{202e} fake"
                   ]
  it "[cli-tools-line] marks tools that are missing or print no version" $
    withTempDir $ \dir -> do
      file <- writeProgram dir "counter" counterProgram
      vecs <- writeVectors dir "counter" counterVectors
      bin <- fakeTools dir [("vvp", "exit 0"), ("iverilog", "kill -9 $$")]
      r <- ginWith [("PATH", bin)] ["validate", file, "--vectors", vecs, "--allow-missing-tools"]
      take 2 (outLines r)
        `shouldBe` [ "vectors: PASS cycles=8"
                   , "tools: verilator (not found), iverilog (version unknown), \
                     \vvp (version unknown), nvc (not found)"
                   ]
  it "[cli-tools-line] lists only the tools of the requested targets" $
    withTempDir $ \dir -> do
      file <- writeProgram dir "counter" counterProgram
      vecs <- writeVectors dir "counter" counterVectors
      r <- gin ["validate", file, "--vectors", vecs, "--target", "vhdl", "--allow-missing-tools"]
      r `shouldExit` ExitSuccess
      take 2 (outLines r) `shouldBe` ["vectors: PASS cycles=8", "tools: nvc (not found)"]

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
        `shouldBe` [ "vectors: PASS cycles=8"
                   , "tools: nvc (version unknown)"
                   , "sim-core: PASS"
                   , "sim-normal: PASS"
                   , "vhdl-lint: FAIL nvc timed out after 1 s"
                   , "vhdl-run: FAIL nvc timed out after 1 s"
                   ]
      -- Three runs (the version query, lint and run) of 1 s each, plus a
      -- grace period for each killed tool to exit; the fake would otherwise
      -- sleep 30 s per run.
      unless (elapsed < 20) $
        expectationFailure ("validate took " <> show elapsed <> " s")

simTimeoutSpec :: Spec
simTimeoutSpec = describe "simulation timeout" $ do
  it "[cli-sim-timeout] stops each simulator after --sim-timeout seconds" $
    withTempDir $ \dir -> do
      file <- writeProgram dir "squaring" (squaringProgram 13)
      vecs <- writeVectors dir "squaring" (squaringVectors 1000)
      start <- getMonotonicTime
      r <- gin ["sim", file, "--vectors", vecs, "--sim-timeout", "1"]
      elapsed <- subtract start <$> getMonotonicTime
      r `shouldExit` ExitFailure 1
      outLines r
        `shouldBe` [ "sim-core: SKIP(inconclusive: timeout after 1 s)"
                   , "sim-normal: FAIL timeout after 1 s"
                   ]
      -- Each simulator would run for minutes; a generous margin for a busy
      -- machine still tells the two apart.
      unless (elapsed < 30) $
        expectationFailure ("sim took " <> show elapsed <> " s")
  it "[cli-sim-timeout] validate stops the simulators after --sim-timeout seconds too" $
    withTempDir $ \dir -> do
      file <- writeProgram dir "squaring" (squaringProgram 13)
      vecs <- writeVectors dir "squaring" (squaringVectors 1000)
      r <-
        gin
          [ "validate"
          , file
          , "--vectors"
          , vecs
          , "--target"
          , "verilog"
          , "--allow-missing-tools"
          , "--sim-timeout"
          , "1"
          ]
      r `shouldExit` ExitFailure 1
      take 2 (checkLines r)
        `shouldBe` [ "sim-core: SKIP(inconclusive: timeout after 1 s)"
                   , "sim-normal: FAIL timeout after 1 s"
                   ]
  it "[cli-sim-timeout] leaves simulations that finish in time alone" $
    withTempDir $ \dir -> do
      file <- writeProgram dir "counter" counterProgram
      vecs <- writeVectors dir "counter" counterVectors
      r <- gin ["sim", file, "--vectors", vecs, "--sim-timeout", "1"]
      r `shouldExit` ExitSuccess
      outLines r `shouldBe` ["sim-core: PASS", "sim-normal: PASS"]

toolEnvSpec :: Spec
toolEnvSpec = describe "tool environment" $
  itWithTools ["perl"] "[cli-tool-env] runs tools with only PATH, HOME, TMPDIR and LC_ALL=C" $
    withTempDir $ \dir -> do
      file <- writeProgram dir "counter" counterProgram
      vecs <- writeVectors dir "counter" counterVectors
      perl <- findExecutable "perl" >>= maybe (fail "perl not found") pure
      let logFile = dir </> "env.log"
          dumpEnv =
            "#!" <> perl <> "\n\
            \open(my $f, '>>', '" <> logFile <> "') or die;\n\
            \print $f join(' ', map { \"$_=$ENV{$_}\" } sort keys %ENV), \"\\n\";\n"
      bin <- scriptTools dir [(t, dumpEnv) | t <- verilogTools]
      let args = ["validate", file, "--vectors", vecs, "--target", "verilog"]
          caller =
            [ ("PATH", bin)
            , ("HOME", dir </> "home")
            , ("TMPDIR", dir)
            , ("LC_ALL", "en_US.UTF-8")
            , ("LANG", "en_US.UTF-8")
            , ("GIN_TEST_SECRET", "hunter2")
            , ("VERILATOR_ROOT", dir)
            , ("IVERILOG_DUMPER", "lxt")
            ]
      _ <- ginWith caller args
      -- Three version queries, two lint runs and two testbench runs.
      readLines logFile
        `shouldReturn` replicate
          7
          ("HOME=" <> Text.pack (dir </> "home") <> " LC_ALL=C PATH=" <> Text.pack bin <> " TMPDIR=" <> Text.pack dir)
      removeFile logFile
      _ <- ginWith [("PATH", bin), ("GIN_TEST_SECRET", "hunter2")] args
      readLines logFile `shouldReturn` replicate 7 ("LC_ALL=C PATH=" <> Text.pack bin)

processGroupSpec :: Spec
processGroupSpec = describe "tool timeout and process groups" $ do
  it "[cli-pgkill] kills a timed-out tool that ignores SIGTERM together with its child" $
    withTempDir $ \dir -> do
      let pids = dir </> "pids"
      leaked <-
        timedOutTool
          dir
          ( "trap '' TERM INT HUP\nsleep 60 &\necho $! >> "
              <> pids
              <> "\necho $$ >> "
              <> pids
              <> "\nwait"
          )
          pids
      -- Three runs (the version query, lint and run), each a leader and a child.
      fmap length (readLines pids) `shouldReturn` 6
      leaked `shouldBe` []
  it "[cli-pgkill] kills the children of a tool whose leader has already exited" $
    withTempDir $ \dir -> do
      let pids = dir </> "pids"
      leaked <- timedOutTool dir ("sleep 60 &\necho $! >> " <> pids <> "\nexit 0") pids
      fmap length (readLines pids) `shouldReturn` 3
      leaked `shouldBe` []

-- | Run validate for VHDL with a fake nvc that never finishes within the
-- 1 s tool timeout and records process ids in the file; return the ids of
-- the processes still alive a few seconds after gin returns (and kill
-- them, so a failing test leaks nothing).
timedOutTool :: FilePath -> String -> FilePath -> IO [Text]
timedOutTool dir body pids = do
  file <- writeProgram dir "counter" counterProgram
  vecs <- writeVectors dir "counter" counterVectors
  bin <- fakeTools dir [("nvc", body)]
  r <-
    ginWith
      [("PATH", bin <> ":/bin:/usr/bin")]
      ["validate", file, "--vectors", vecs, "--target", "vhdl", "--tool-timeout", "1"]
  r `shouldExit` ExitFailure 1
  checkLines r
    `shouldBe` [ "sim-core: PASS"
               , "sim-normal: PASS"
               , "vhdl-lint: FAIL nvc timed out after 1 s"
               , "vhdl-run: FAIL nvc timed out after 1 s"
               ]
  ids <- readLines pids
  leaked <- survivors 50 ids
  forM_ leaked $ \pid -> readProcessWithExitCode "/bin/sh" ["-c", "kill -9 " <> Text.unpack pid] ""
  pure leaked

-- | The processes among these that are still alive after polling for up to
-- @n@ tenths of a second.
survivors :: Int -> [Text] -> IO [Text]
survivors n pids = do
  alive <- filterM isAlive pids
  if null alive || n <= 0 then pure alive else threadDelay 100000 >> survivors (n - 1) alive
  where
    isAlive pid = do
      (code, _, _) <- readProcessWithExitCode "/bin/sh" ["-c", "kill -0 " <> Text.unpack pid] ""
      pure (code == ExitSuccess)

----------------------------------------------------------------------
-- Writing generated files

atomicSpec :: Spec
atomicSpec = describe "writing a target's files" $ do
  it "[cli-atomic] a testbench that cannot be put in place leaves no design file of its target" $
    withTempDir $ \dir -> do
      file <- writeProgram dir "counter" counterProgram
      vecs <- writeVectors dir "counter" counterVectors
      let out = dir </> "out"
      createDirectory out
      _ <- writeRaw out "counter.v" "old design"
      createDirectory (out </> "counter_tb.v")
      _ <- writeRaw (out </> "counter_tb.v") "keep.txt" "kept"
      r <-
        gin
          ["testbench", file, "--vectors", vecs, "-o", out, "--target", "vhdl", "--target", "verilog"]
      r `shouldExit` ExitFailure 1
      runErr r `shouldStartWith'` "driver error: cannot write "
      -- The VHDL target was complete before the Verilog one failed.
      sort <$> listDirectory out `shouldReturn` ["counter.vhd", "counter_tb.v", "counter_tb.vhd"]
      listDirectory (out </> "counter_tb.v") `shouldReturn` ["keep.txt"]
  it "[cli-atomic] validate -o DIR runs the tools on what it generated, not on DIR" $
    withTempDir $ \dir -> do
      file <- writeProgram dir "counter" counterProgram
      vecs <- writeVectors dir "counter" counterVectors
      m <- netlistOf counterProgram
      secret <- writeRaw dir "secret.txt" "secret"
      let out = dir </> "out"
          seen = dir </> "seen"
          generated =
            concat
              [ [ ("counter." <> backendFileExt b, backendRender b m)
                , ("counter_tb." <> backendFileExt b, backendTestbench b m counterVectors)
                ]
              | b <- [verilog, systemVerilog, vhdl]
              ]
          -- Every fake tool keeps a copy of the HDL files it is given.
          keepInputs =
            "for f in \"$@\"; do case \"$f\" in *.v|*.sv|*.vhd) [ -f \"$f\" ] && cat \"$f\" > "
              <> seen
              <> "/\"$f\";; esac; done\n"
      createDirectory out
      createDirectory seen
      bin <-
        fakeTools
          dir
          [ ("verilator", keepInputs)
          , ("iverilog", keepInputs)
          , ("vvp", "echo 'GIN-PASS cycles=8'")
          , ("nvc", keepInputs <> "echo 'GIN-PASS cycles=8'")
          ]
      -- A co-writer of DIR keeps replacing the files gin writes there with
      -- links to another file, as fast as it can.
      forM_ [1 :: Int .. 3] $ \_ -> do
        stop <- newEmptyMVar
        swapper <- forkIO (swapInLinks stop secret out (fmap fst generated))
        r <-
          ginWith [("PATH", bin <> ":/bin:/usr/bin")] ["validate", file, "--vectors", vecs, "-o", out]
            `finally` (putMVar stop () >> killThread swapper)
        r `shouldExit` ExitSuccess
        forM_ generated $ \(name, content) ->
          (name, readText (seen </> name)) `shouldReturnFor` (name, content)

-- | Until told to stop, replace each named regular file in the directory
-- with a symbolic link to the target, atomically, as a co-writer of an
-- output directory could.
swapInLinks :: MVar () -> FilePath -> FilePath -> [FilePath] -> IO ()
swapInLinks stop target dir names =
  tryReadMVar stop >>= \case
    Just () -> pure ()
    Nothing -> do
      forM_ names $ \name -> do
        let path = dir </> name
            tmp = dir </> (".swap-" <> name)
        regular <- (&&) <$> doesFileExist path <*> (not <$> isLink path)
        when regular . void . tryIO $ do
          createFileLink target tmp
          renamePath tmp path
      yield
      swapInLinks stop target dir names
  where
    isLink path = fromRight False <$> tryIO (pathIsSymbolicLink path)
    tryIO :: IO a -> IO (Either IOException a)
    tryIO = try

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

-- | The check lines validate prints after its informational vectors and
-- tools lines.
checkLines :: Run -> [Text]
checkLines r = case outLines r of
  vectorsLine : toolsLine : rest
    | "vectors: " `Text.isPrefixOf` vectorsLine && "tools: " `Text.isPrefixOf` toolsLine -> rest
  ls -> "(missing vectors and tools lines)" : ls

-- | Like 'shouldReturn', labelled so that a failure says which item it is.
shouldReturnFor :: (Show a, Eq a, Show l, Eq l) => (l, IO a) -> (l, a) -> Expectation
shouldReturnFor (label, act) expected = act >>= \a -> (label, a) `shouldBe` expected

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

writeProgram :: FilePath -> String -> Program Ty Name -> IO FilePath
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

netlistOf :: Program Ty Name -> IO Module
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
fakeTools dir tools = scriptTools dir [(name, "#!/bin/sh\n" <> body <> "\n") | (name, body) <- tools]

-- | A directory holding executable scripts with the given contents, and
-- nothing else.
scriptTools :: FilePath -> [(String, String)] -> IO FilePath
scriptTools dir tools = do
  let bin = dir </> "fake"
  createDirectory bin
  forM_ tools $ \(name, script) -> do
    let exe = bin </> name
    writeFile exe script
    perms <- getPermissions exe
    setPermissions exe (setOwnerExecutable True perms)
  pure bin

readLines :: FilePath -> IO [Text]
readLines file = Text.lines <$> readText file

-- | Every command, with the arguments it needs; output goes to @out@.
everyCommand :: FilePath -> FilePath -> FilePath -> [[String]]
everyCommand file vecs out =
  [ ["check", file]
  , ["compile", file, "-o", out]
  , ["testbench", file, "--vectors", vecs, "-o", out]
  , ["sim", file, "--vectors", vecs]
  , ["validate", file, "--vectors", vecs, "-o", out, "--allow-missing-tools"]
  ]

-- | counter with a trace that lists its specification's definitions
-- (canonical encoding).
specFixture :: FilePath
specFixture = "test/fixtures/ir/counter-spec.canonical.json"

decodeFixture :: FilePath -> IO (Program Ty Name)
decodeFixture path = do
  bytes <- LBS.readFile path
  either (fail . Text.unpack . renderError) pure (decodeProgram bytes)

withTop :: (TopEntity Ty Name -> TopEntity Ty Name) -> Program Ty Name -> Program Ty Name
withTop f p = p {progTop = f (progTop p)}

-- | counter whose top definition does not exist: a type error.
missingTopDef :: Program Ty Name
missingTopDef = withTop (\t -> t {topDef = "Counter.missing"}) counterProgram

-- | counter with its input port named @clk@, which collides with the clock
-- every module gets: the checker rejects it.
clockPort :: Program Ty Name
clockPort = withTop (\t -> t {topInputs = [Port "clk" TBool]}) counterProgram

counterWithAxioms :: [Text] -> Program Ty Name
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
doublingProgram :: Int -> Program Ty Name
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
    , progDefs = Def "D.top" (TFun (sig (bv 8)) (sig (bv 8))) top : doublingDefs k
    , progCertificate = testCertificate "D.top_correct"
    }
  where
    top = ELam [("x", sig (bv 8))] (EApp (lift1 (bv 8) (bv 8)) [EGlobal (doublingName k), EVar "x"])

-- | The functions @g0@ to @gk@ of 'doublingProgram'.
doublingDefs :: Int -> [Def Ty Name]
doublingDefs k = fmap g [0 .. k]
  where
    fn = TFun (bv 8) (bv 8)
    g i = Def (doublingName i) fn (ELam [("v", bv 8)] (body i))
    body i
      | i <= 0 = EVar "v"
      | otherwise =
          EApp (EGlobal (doublingName (i - 1))) [EApp (EGlobal (doublingName (i - 1))) [EVar "v"]]

doublingName :: Int -> Name
doublingName i = Name (Text.pack ("D.g" <> show i))

-- | @sig.lift 1@ at the given argument and result types.
lift1 :: Ty -> Ty -> Expr Ty Name
lift1 a r = EPrim (SigLift 1) (tFuns [TFun a r, sig a] (sig r))

doublingVectors :: Vectors
doublingVectors =
  Vectors
    { vecTop = "doubling"
    , vecInputs = [Port "x" (bv 8)]
    , vecOutputs = [Port "o" (bv 8)]
    , vecCycles = [Cycle [VBV 8 n] [VBV 8 n] | n <- [7, 9]]
    }

-- | A top definition with the given name computing @o = l18 x = x@, where
-- @l0 s = sig.lift id s@ and @l(i+1) s = li (li s)@. Normalization erases
-- the identity lifts, but the core simulator builds one network node per
-- lift and reaches its node cap (@2^18@) while building the top
-- definition, so its name ends up in the inconclusive message.
constantBudgetProgram :: Text -> Program Ty Name
constantBudgetProgram topDefName =
  Program
    { progProducer = Producer "gin-driver-spec" "n/a"
    , progTop =
        TopEntity
          { topName = "forged"
          , topDomain = sysDomain
          , topInputs = [Port "x" (bv 8)]
          , topOutputs = [Port "o" (bv 8)]
          , topDef = Name topDefName
          }
    , progDefs =
        Def (Name topDefName) sigFn (ELam [("x", sig (bv 8))] (EApp (EGlobal (liftName 18)) [EVar "x"]))
          : fmap level [0 .. 18]
    , progCertificate = testCertificate "D.top_correct"
    }
  where
    sigFn = TFun (sig (bv 8)) (sig (bv 8))
    liftName :: Int -> Name
    liftName i = Name (Text.pack ("D.l" <> show i))
    level i =
      Def (liftName i) sigFn . ELam [("s", sig (bv 8))] $
        if i == 0
          then EApp (lift1 (bv 8) (bv 8)) [ELam [("v", bv 8)] (EVar "v"), EVar "s"]
          else EApp (EGlobal (liftName (i - 1))) [EApp (EGlobal (liftName (i - 1))) [EVar "s"]]

constantBudgetVectors :: Vectors
constantBudgetVectors =
  Vectors
    { vecTop = "forged"
    , vecInputs = [Port "x" (bv 8)]
    , vecOutputs = [Port "o" (bv 8)]
    , vecCycles = [Cycle [VBV 8 n] [VBV 8 n] | n <- [7, 9]]
    }

-- | @f0 v = v * v@ and @fi v = f(i-1) (f(i-1) v)@ on 4096-bit vectors, so
-- @fk@ squares @2^k@ times; the output is whether @fk (zext b + c)@ is
-- below @2^4095@. Every cycle costs either simulator @2^k@ multiplications
-- of 4096-bit numbers, all within its bounds.
squaringProgram :: Int -> Program Ty Name
squaringProgram k =
  Program
    { progProducer = Producer "gin-driver-spec" "n/a"
    , progTop =
        TopEntity
          { topName = "squaring"
          , topDomain = sysDomain
          , topInputs = [Port "b" TBool]
          , topOutputs = [Port "y" TBool]
          , topDef = "S.top"
          }
    , progDefs = fmap f [0 .. k] <> [Def "S.top" (TFun (sig TBool) (sig TBool)) top]
    , progCertificate = testCertificate "S.top_correct"
    }
  where
    w = bv 4096
    name i = Name (Text.pack ("S.f" <> show i))
    binary op = EPrim op (tFuns [w, w] w)
    f i = Def (name i) (TFun w w) (ELam [("v", w)] (body i))
    body i
      | i <= 0 = EApp (binary BvMul) [EVar "v", EVar "v"]
      | otherwise = EApp (EGlobal (name (i - 1))) [EApp (EGlobal (name (i - 1))) [EVar "v"]]
    widen e =
      EApp
        (EPrim (BvZext 4096) (TFun (bv 1) w))
        [EApp (EPrim BvOfBool (TFun TBool (bv 1))) [e]]
    start = EApp (binary BvAdd) [widen (EVar "b"), ELit (VBV 4096 (2 ^ (4095 :: Int) + 12345))]
    below =
      EApp
        (EPrim BvUlt (tFuns [w, w] TBool))
        [EApp (EGlobal (name k)) [start], ELit (VBV 4096 (2 ^ (4095 :: Int)))]
    top = ELam [("a", sig TBool)] (EApp (lift1 TBool TBool) [ELam [("b", TBool)] below, EVar "a"])

-- | @n@ cycles for 'squaringProgram'. The expected outputs are arbitrary:
-- the tests stop both simulators long before they get to compare them.
squaringVectors :: Int -> Vectors
squaringVectors n =
  Vectors
    { vecTop = "squaring"
    , vecInputs = [Port "b" TBool]
    , vecOutputs = [Port "y" TBool]
    , vecCycles = [Cycle [VBool (odd i)] [VBool False] | i <- [1 .. n]]
    }
