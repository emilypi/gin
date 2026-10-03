-- | End-to-end tests of the compiler pipeline, through the library API.
--
-- Every hand-written example circuit ("Gin.Examples"), and the counter
-- read from @test/fixtures/ir/counter.gin.json@, goes through every stage
-- the compiler runs: JSON decoding, type checking, the certificate
-- policy, normalization, the netlist builder and all three backends. Each
-- generated design must pass its backend's lint commands, and each
-- generated testbench must pass on the circuit's vectors under the real
-- HDL simulators (Icarus Verilog for Verilog and SystemVerilog, nvc for
-- VHDL), by the pass rule of @docs/semantics.md@. Both reference
-- simulators ("Gin.Sim") must reproduce the vectors, and they must agree
-- with each other on random input rows.
--
-- Fault injection then checks that a fault is caught at the level where
-- it is introduced:
--
--   * a fault in the core IR program makes 'simulateCore' disagree with
--     the vectors (and the compiled program carries the same fault);
--   * a fault in the normal form makes 'simulateNormal' disagree with the
--     vectors while 'simulateCore' still reproduces them;
--   * a fault in the netlist makes every HDL testbench fail, with the
--     mismatches the reference simulator predicts for the same fault,
--     while both reference simulators still reproduce the vectors.
--
-- Tool runs use the commands of the backend interface ("Gin.Backend.Types"),
-- each in a private temporary directory holding @<module>.<ext>@ and
-- @<module>_tb.<ext>@. A test whose tools are missing is pending, or
-- fails when @GIN_REQUIRE_TOOLS=1@.
module Gin.E2ESpec (spec) where

import Control.Monad (forM_, unless)
import Data.Bifunctor (first)
import Data.ByteString qualified as ByteString
import Data.ByteString.Lazy qualified as LazyByteString
import Data.Char (isDigit)
import Data.List (inits, nub, tails)
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Text.Encoding qualified as Text
import Gin.Backend.SystemVerilog (systemVerilog)
import Gin.Backend.Types
  ( Backend (..)
  , Target (..)
  , failMarker
  , mismatchMarker
  , passMarker
  , targetName
  )
import Gin.Backend.VHDL (vhdl)
import Gin.Backend.Verilog (verilog)
import Gin.Certificate (checkCertificate, defaultPolicy)
import Gin.Core.Check (checkProgram)
import Gin.Core.Json (decodeProgram, decodeVectors, encodeProgram, encodeVectors)
import Gin.Core.Normal (NBind (..), NModule (..), NRhs (..))
import Gin.Core.Syntax
  ( Bind (..)
  , Def (..)
  , Expr (..)
  , Port (..)
  , PrimOp (..)
  , Program (..)
  , TopEntity (..)
  , Ty (..)
  , Value (..)
  , validValue
  , valueTy
  )
import Gin.Error (GinError, renderError)
import Gin.Examples
  ( counterProgram
  , counterVectors
  , detectorProgram
  , detectorVectors
  , macProgram
  , macVectors
  )
import Gin.Netlist.Build (buildNetlist)
import Gin.Netlist.Types
  ( Decl (..)
  , HLit (..)
  , HwType (..)
  , Ident (..)
  , Module (..)
  , Net (..)
  , Output (..)
  )
import Gin.Normalize (checkNormal, normalize)
import Gin.Sim (isBudgetError, simulateCore, simulateNormal)
import Gin.TestUtil (itWithTools, runTool, withTempDir)
import Gin.Vectors (Cycle (..), Vectors (..))
import System.Exit (ExitCode (..))
import System.FilePath ((</>))
import Test.Hspec
  ( Expectation
  , Spec
  , describe
  , expectationFailure
  , it
  , shouldBe
  , shouldNotBe
  , shouldSatisfy
  )
import Test.QuickCheck
  ( Gen
  , Property
  , arbitrary
  , choose
  , conjoin
  , counterexample
  , forAll
  , forAllShrink
  , frequency
  , shrinkIntegral
  , shrinkList
  , sized
  , vectorOf
  , withMaxSuccess
  , (===)
  )

----------------------------------------------------------------------
-- Spec

-- | The end-to-end suite: the pass rule, the pipeline on every circuit,
-- the reference simulators on random rows, and fault injection.
spec :: Spec
spec = do
  describe "pass rule" passRuleSpec
  describe "pipeline" $ do
    forM_ examples $ \ex ->
      describe (exName ex) $ do
        it "[e2e-fixtures] decoding its JSON encoding gives the example back" $ do
          decodeProgram (encodeProgram (exProgram ex)) `shouldBe` Right (exProgram ex)
          decodeVectors (encodeVectors (exVectors ex)) `shouldBe` Right (exVectors ex)
        circuitSpec (exampleCircuit ex)
    describe "counter.gin.json" $ do
      it "[e2e-json-fixture] decodes to the hand-written counter and its vectors" $
        withDecoded jsonFixture $ \p vs -> do
          p `shouldBe` counterProgram
          vs `shouldBe` counterVectors
      circuitSpec jsonFixture
  describe "reference simulators on random input rows" $ do
    forM_ examples $ \ex -> do
      let ports = topInputs (progTop (exProgram ex))
      it ("[e2e-quickcheck] " <> exName ex <> ": generated rows have the input port types") $
        withRowGen ports $ \gen ->
          forAll gen $ \rows ->
            all (\row -> fmap valueTy row == fmap portTy ports && all validValue row) rows
      it ("[e2e-quickcheck] " <> exName ex <> ": simulateCore equals simulateNormal . normalize") $
        coreAgreesWithNormal (exProgram ex)
  -- Each fault is injected into every example it applies to: the detector
  -- has no bv.add and the normal form of mac has no mux.
  describe "fault injection" $ do
    describe "in the core IR program (bv.add becomes bv.sub)" $
      forM_ [counter, mac] coreFaultSpec
    describe "in the normal form (the first mux's branches swapped)" $
      forM_ [counter, detector] normalFaultSpec
    describe "in the netlist (the first register's reset value inverted)" $
      forM_ examples netlistFaultSpec

-- | The items every circuit goes through: compile, simulate, then lint and
-- run the generated HDL of every backend.
circuitSpec :: Circuit -> Spec
circuitSpec c = do
  item "decodes, type checks, passes the certificate policy, normalizes and builds a netlist" $
    withCompiled c interfaceAgrees
  item "both reference simulators reproduce the vectors" $
    withCompiled c $ \p vs comp -> simulatorsReproduce p (compNormal comp) vs
  forM_ targets $ \t -> do
    let hdl = targetLabel t
    itWithTools (lintTools t) (tagged ("the " <> hdl <> " design passes its lint commands")) $
      withCompiled c $ \_ _ comp -> lintsClean t (compNetlist comp)
    itWithTools (runTools t) (tagged ("the " <> hdl <> " testbench passes on the vectors")) $
      withCompiled c $ \_ vs comp ->
        runTestbench t (compNetlist comp) vs >>= shouldPass (hdl <> " testbench") (cycleCount vs)
  where
    tagged what = "[" <> circTag c <> "] " <> what
    item what = it (tagged what)

-- | A program fault is caught by the core IR simulator, and normalization
-- carries the fault into the normal form unchanged.
coreFaultSpec :: Example -> Spec
coreFaultSpec ex = do
  it ("[e2e-fault-core] " <> exName ex <> ": simulateCore disagrees with the vectors") $ do
    faulty `shouldNotBe` p
    checkProgram faulty `shouldBe` Right ()
    disagrees (outputRows vs) (runCore faulty (inputRows vs))
  it ("[e2e-fault-core] " <> exName ex <> ": the compiled faulty program keeps the fault") $
    stage "compiling the faulty program" (compile faulty) $ \comp -> do
      disagrees (outputRows vs) (runCore faulty (inputRows vs))
      runNormal (compNormal comp) (inputRows vs) `shouldBe` runCore faulty (inputRows vs)
  where
    p = exProgram ex
    vs = exVectors ex
    faulty = addBecomesSub p

-- | A normal-form fault is caught by the normal-form simulator, while the
-- core IR simulator, which never sees the normal form, still agrees.
normalFaultSpec :: Example -> Spec
normalFaultSpec ex =
  it ("[e2e-fault-normal] " <> exName ex <> ": simulateNormal disagrees, simulateCore agrees") $
    stage "compiling" (compile p) $ \comp -> case swapFirstMux (compNormal comp) of
      Nothing -> expectationFailure "the normal form has no mux"
      Just faulty -> do
        checkNormal faulty `shouldBe` Right ()
        runCore p (inputRows vs) `shouldBe` Right (outputRows vs)
        disagrees (outputRows vs) (runNormal faulty (inputRows vs))
  where
    p = exProgram ex
    vs = exVectors ex

-- | A netlist fault is caught by every HDL testbench, while both reference
-- simulators, which never see the netlist, still agree with the vectors.
-- The same fault applied to the normal form predicts how many
-- (cycle, port) mismatches each testbench must report.
netlistFaultSpec :: Example -> Spec
netlistFaultSpec ex = forM_ targets $ \t -> do
  let hdl = targetLabel t
      label = "[e2e-fault-netlist] " <> exName ex <> ": the " <> hdl <> " testbench fails"
  itWithTools (nub (lintTools t <> runTools t)) (label <> ", the simulators agree") $
    stage "compiling" (compile p) $ \comp -> do
      simulatorsReproduce p (compNormal comp) vs
      case (invertFirstReset (compNetlist comp), invertFirstInit (compNormal comp)) of
        (Just faulty, Just faultyNormal) ->
          stage "simulating the faulty normal form" (simulateNormal faultyNormal rows) $ \outs -> do
            let k = mismatchCount (outputRows vs) outs
            k `shouldSatisfy` (> 0)
            lintsClean t faulty
            runTestbench t faulty vs >>= shouldFailWith (hdl <> " testbench") (cycleCount vs) k
        _ -> expectationFailure "the circuit has no register"
  where
    p = exProgram ex
    vs = exVectors ex
    rows = inputRows vs

----------------------------------------------------------------------
-- Circuits

-- | A hand-written example with its vectors.
data Example = Example
  { exName :: !String
  , exProgram :: !Program
  , exVectors :: !Vectors
  }

examples :: [Example]
examples = [counter, mac, detector]

counter, mac, detector :: Example
counter = Example "counter" counterProgram counterVectors
mac = Example "mac" macProgram macVectors
detector = Example "detector" detectorProgram detectorVectors

-- | A circuit as the compiler receives it: the JSON of its program and of
-- its vectors.
data Circuit = Circuit
  { circTag :: !String
  -- ^ The tag of the items run on this circuit.
  , circLoad :: !(IO (LazyByteString.ByteString, LazyByteString.ByteString))
  }

-- | An example, entering the pipeline as its canonical JSON encoding.
exampleCircuit :: Example -> Circuit
exampleCircuit ex =
  Circuit "e2e-fixtures" (pure (encodeProgram (exProgram ex), encodeVectors (exVectors ex)))

-- | The counter as checked-in JSON files.
jsonFixture :: Circuit
jsonFixture =
  Circuit "e2e-json-fixture" $
    (,) <$> readBytes ("test" </> "fixtures" </> "ir" </> "counter.gin.json")
      <*> readBytes ("test" </> "fixtures" </> "ir" </> "counter.vectors.canonical.json")
  where
    readBytes path = LazyByteString.fromStrict <$> ByteString.readFile path

----------------------------------------------------------------------
-- The pipeline

-- | What the compiler produces for a program.
data Compiled = Compiled
  { compNormal :: !NModule
  , compNetlist :: !Module
  }

-- | Every stage after decoding, in the order the compiler runs them.
compile :: Program -> Either GinError Compiled
compile p = do
  checkProgram p
  checkCertificate defaultPolicy (progCertificate p)
  m <- normalize p
  checkNormal m
  Compiled m <$> buildNetlist m

-- | Continue with a stage's result, or fail with its rendered error.
stage :: String -> Either GinError a -> (a -> Expectation) -> Expectation
stage what result k = case result of
  Left e -> expectationFailure (what <> " failed:\n" <> Text.unpack (renderError e))
  Right a -> k a

-- | Decode a circuit's program and vectors.
withDecoded :: Circuit -> (Program -> Vectors -> Expectation) -> Expectation
withDecoded c k = do
  (programJson, vectorsJson) <- circLoad c
  stage "decoding the program" (decodeProgram programJson) $ \p ->
    stage "decoding the vectors" (decodeVectors vectorsJson) (k p)

-- | Decode and compile a circuit.
withCompiled :: Circuit -> (Program -> Vectors -> Compiled -> Expectation) -> Expectation
withCompiled c k = withDecoded c $ \p vs -> stage "compiling" (compile p) (k p vs)

-- | The vectors describe the program's top entity, and the netlist keeps
-- its name and ports unchanged (they are the hardware interface), as the
-- testbench generators require.
interfaceAgrees :: Program -> Vectors -> Compiled -> Expectation
interfaceAgrees p vs comp = do
  vecTop vs `shouldBe` topName top
  vecInputs vs `shouldBe` topInputs top
  vecOutputs vs `shouldBe` topOutputs top
  nmName (compNormal comp) `shouldBe` topName top
  modName n `shouldBe` Ident (topName top)
  Just (modInputs n) `shouldBe` traverse portNet (topInputs top)
  Just (fmap outNet (modOutputs n)) `shouldBe` traverse portNet (topOutputs top)
  where
    top = progTop p
    n = compNetlist comp
    portNet port = Net (Ident (portName port)) <$> hwType (portTy port)
    hwType = \case
      TBool -> Just HBit
      TBitVec w -> Just (HVec w)
      _ -> Nothing

----------------------------------------------------------------------
-- Reference simulators

inputRows, outputRows :: Vectors -> [[Value]]
inputRows = fmap cycInputs . vecCycles
outputRows = fmap cycOutputs . vecCycles

cycleCount :: Vectors -> Int
cycleCount = length . vecCycles

-- | 'simulateCore' with its error rendered. An inconclusive result (the
-- simulator exceeded a bound, 'isBudgetError') is labelled as such; the
-- examples are far inside the bounds, so any error fails a test.
runCore :: Program -> [[Value]] -> Either Text [[Value]]
runCore p rows = first describeError (simulateCore p rows)
  where
    describeError e
      | isBudgetError e = "inconclusive, a simulation bound was exceeded: " <> renderError e
      | otherwise = renderError e

-- | 'simulateNormal' with its error rendered.
runNormal :: NModule -> [[Value]] -> Either Text [[Value]]
runNormal m rows = first renderError (simulateNormal m rows)

-- | Both reference simulators reproduce the expected output rows.
simulatorsReproduce :: Program -> NModule -> Vectors -> Expectation
simulatorsReproduce p m vs = do
  runCore p (inputRows vs) `shouldBe` Right (outputRows vs)
  runNormal m (inputRows vs) `shouldBe` Right (outputRows vs)

-- | A simulator returned output rows, and they differ from the expected ones.
disagrees :: [[Value]] -> Either Text [[Value]] -> Expectation
disagrees expected = \case
  Left e -> expectationFailure ("expected output rows, got an error:\n" <> Text.unpack e)
  Right actual -> actual `shouldNotBe` expected

-- | Number of (cycle, port) pairs whose values differ.
mismatchCount :: [[Value]] -> [[Value]] -> Int
mismatchCount expected actual =
  length (filter id (zipWith (/=) (concat expected) (concat actual)))

----------------------------------------------------------------------
-- Random input rows

-- | On random input rows, the core IR simulator gives the same output rows
-- as the normal-form simulator on the normalized program, one row per
-- input row, each of the output port types.
coreAgreesWithNormal :: Program -> Property
coreAgreesWithNormal p = case normalize p of
  Left e -> counterexample (Text.unpack (renderError e)) False
  Right m ->
    withRowGen (topInputs top) $ \gen ->
      withMaxSuccess 300 . forAllShrink gen (shrinkList shrinkRow) $ \rows ->
        case (runCore p rows, runNormal m rows) of
          (Right core, Right normal) ->
            conjoin
              [ core === normal
              , length core === length rows
              , counterexample "an output row does not have the output port types" $
                  all (\row -> fmap valueTy row == fmap portTy (topOutputs top)) core
              ]
          (Left e, _) -> counterexample ("simulateCore: " <> Text.unpack e) False
          (_, Left e) -> counterexample ("simulateNormal: " <> Text.unpack e) False
  where
    top = progTop p

-- | Run a property on a generator of input rows for these ports, or fail
-- if a port type has no generator (ports are always scalar).
withRowGen :: [Port] -> (Gen [[Value]] -> Property) -> Property
withRowGen ports k = case traverse (portValue . portTy) ports of
  Nothing -> counterexample "a port type is not scalar" False
  Just values -> k (sized (\n -> choose (0, min 64 n)) >>= \len -> vectorOf len (sequence values))

-- | Values of a scalar port type. Bit vectors are drawn uniformly, or from
-- the edges of their range (0, 1 and all ones) so that wrap-around is
-- exercised often.
portValue :: Ty -> Maybe (Gen Value)
portValue = \case
  TBool -> Just (VBool <$> arbitrary)
  TBitVec w ->
    let top = 2 ^ w - 1
     in Just (VBV w <$> frequency [(1, pure 0), (1, pure 1), (1, pure top), (5, choose (0, top))])
  _ -> Nothing

-- | Shrink one value of a row at a time, keeping its type.
shrinkRow :: [Value] -> [[Value]]
shrinkRow row =
  [ before <> (smaller : after)
  | (before, value : after) <- zip (inits row) (tails row)
  , smaller <- shrinkValue value
  ]

shrinkValue :: Value -> [Value]
shrinkValue = \case
  VBool True -> [VBool False]
  VBool False -> []
  VBV w x -> [VBV w y | y <- shrinkIntegral x, y >= 0]
  VTuple _ -> []

----------------------------------------------------------------------
-- Faults

-- | Replace every @bv.add@ by @bv.sub@ at the same type: still well typed,
-- but a different circuit.
addBecomesSub :: Program -> Program
addBecomesSub p = p {progDefs = fmap mutate (progDefs p)}
  where
    mutate d = d {defBody = rewrite toSub (defBody d)}
    toSub = \case
      EPrim BvAdd ty -> EPrim BvSub ty
      e -> e

-- | Apply a function to every subexpression, innermost first.
rewrite :: (Expr -> Expr) -> Expr -> Expr
rewrite f = go
  where
    go e = f $ case e of
      EVar _ -> e
      EGlobal _ -> e
      ELit _ -> e
      EPrim _ _ -> e
      EApp g args -> EApp (go g) (fmap go args)
      ELam binders body -> ELam binders (go body)
      ELet isRec binds body -> ELet isRec [b {bindExpr = go (bindExpr b)} | b <- binds] (go body)
      ETuple es -> ETuple (fmap go es)
      EProj i x -> EProj i (go x)
      EIf c t x -> EIf (go c) (go t) (go x)

-- | Swap the branches of the first mux, in bind order.
swapFirstMux :: NModule -> Maybe NModule
swapFirstMux m = case break isMux (nmBinds m) of
  (before, NBind n ty (NMux c t e) : after) ->
    Just m {nmBinds = before <> (NBind n ty (NMux c e t) : after)}
  _ -> Nothing
  where
    isMux b = case nbRhs b of
      NMux {} -> True
      _ -> False

-- | Invert every bit of the first register's reset value, in declaration
-- order.
invertFirstReset :: Module -> Maybe Module
invertFirstReset m = case break isReg (modDecls m) of
  (before, DReg n reset next : after) ->
    Just m {modDecls = before <> (DReg n (invertLit reset) next : after)}
  _ -> Nothing
  where
    isReg = \case
      DReg {} -> True
      DAssign {} -> False
    invertLit = \case
      HLitBit b -> HLitBit (not b)
      HLitVec w x -> HLitVec w (2 ^ w - 1 - x)

-- | The fault of 'invertFirstReset' in the normal form. The netlist builder
-- emits at most one declaration per bind, in bind order, and keeps every
-- register (normal-form binds are all read), so the first register of the
-- netlist comes from the first register of the normal form.
invertFirstInit :: NModule -> Maybe NModule
invertFirstInit m = case break isReg (nmBinds m) of
  (before, NBind n ty (NReg initial next) : after) ->
    Just m {nmBinds = before <> (NBind n ty (NReg (invertValue initial) next) : after)}
  _ -> Nothing
  where
    isReg b = case nbRhs b of
      NReg {} -> True
      _ -> False

invertValue :: Value -> Value
invertValue = \case
  VBool b -> VBool (not b)
  VBV w x -> VBV w (2 ^ w - 1 - x)
  VTuple vs -> VTuple (fmap invertValue vs)

----------------------------------------------------------------------
-- HDL tools

-- | Every backend.
targets :: [Target]
targets = [minBound .. maxBound]

targetLabel :: Target -> String
targetLabel = Text.unpack . targetName

backendFor :: Target -> Backend
backendFor = \case
  Verilog -> verilog
  SystemVerilog -> systemVerilog
  VHDL -> vhdl

-- | A tool invocation, run without a shell in the directory holding the
-- generated files.
data Command = Command
  { cmdExe :: !String
  , cmdArgs :: ![String]
  }
  deriving stock (Show)

-- | The lint commands of the backend interface, for module @m@.
lintCommands :: Target -> String -> [Command]
lintCommands t m = case t of
  Verilog ->
    [ Command "verilator" ["--lint-only", "-Wall", "--default-language", "1364-2005", m <> ".v"]
    , Command "iverilog" ["-g2005", "-o", "/dev/null", m <> ".v"]
    ]
  SystemVerilog ->
    [ Command "verilator" ["--lint-only", "-Wall", "--default-language", "1800-2017", m <> ".sv"]
    , Command "iverilog" ["-g2012", "-o", "/dev/null", m <> ".sv"]
    ]
  VHDL -> [Command "nvc" (nvcFlags <> ["-a", m <> ".vhd"])]

-- | The run commands of the backend interface, for module @m@: the build
-- steps, then the run whose standard output carries the testbench
-- protocol.
runCommands :: Target -> String -> ([Command], Command)
runCommands t m = case t of
  Verilog ->
    ([Command "iverilog" ["-g2005", "-o", "tb.vvp", m <> ".v", m <> "_tb.v"]], vvp)
  SystemVerilog ->
    ([Command "iverilog" ["-g2012", "-o", "tb.vvp", m <> ".sv", m <> "_tb.sv"]], vvp)
  VHDL ->
    ([], Command "nvc" (nvcFlags <> ["-a", m <> ".vhd", m <> "_tb.vhd", "-e", m <> "_tb", "-r"]))
  where
    vvp = Command "vvp" ["-n", "tb.vvp"]

nvcFlags :: [String]
nvcFlags = ["-M", "1g", "--std=2008"]

-- | The tools the lint and run commands need (they do not depend on the
-- module name).
lintTools, runTools :: Target -> [String]
lintTools t = nub (fmap cmdExe (lintCommands t "design"))
runTools t = nub (fmap cmdExe (build <> [run]))
  where
    (build, run) = runCommands t "design"

type ToolResult = (ExitCode, Text, Text)

moduleStem :: Module -> String
moduleStem = Text.unpack . unIdent . modName

writeUtf8 :: FilePath -> Text -> IO ()
writeUtf8 path = ByteString.writeFile path . Text.encodeUtf8

writeDesign :: FilePath -> Target -> Module -> IO ()
writeDesign dir t m =
  writeUtf8 (dir </> moduleStem m <> "." <> backendFileExt b) (backendRender b m)
  where
    b = backendFor t

-- | Messages that make a command's run unclean: Verilator's warning and
-- error lines (it also prints a statistics report), and any output at all
-- from the other tools.
diagnostics :: Command -> ToolResult -> [Text]
diagnostics c (_, out, err)
  | cmdExe c == "verilator" = filter ("%" `Text.isPrefixOf`) ls
  | otherwise = filter (not . Text.null . Text.strip) ls
  where
    ls = Text.lines out <> Text.lines err

-- | Run a command that must exit 0 without diagnostics.
runClean :: FilePath -> Command -> Expectation
runClean dir c = do
  result@(code, _, _) <- runTool dir (cmdExe c) (cmdArgs c)
  unless (code == ExitSuccess && null (diagnostics c result)) $
    expectationFailure (describeRun (unwords (cmdExe c : cmdArgs c)) result)

-- | The design passes every lint command of its backend.
lintsClean :: Target -> Module -> Expectation
lintsClean t m = withTempDir $ \dir -> do
  writeDesign dir t m
  mapM_ (runClean dir) (lintCommands t (moduleStem m))

-- | Build the design and testbench, which must build cleanly, and run the
-- testbench.
runTestbench :: Target -> Module -> Vectors -> IO ToolResult
runTestbench t m vs = withTempDir $ \dir -> do
  writeDesign dir t m
  writeUtf8
    (dir </> moduleStem m <> "_tb." <> backendFileExt b)
    (backendTestbench b m vs)
  let (build, run) = runCommands t (moduleStem m)
  mapM_ (runClean dir) build
  runTool dir (cmdExe run) (cmdArgs run)
  where
    b = backendFor t

----------------------------------------------------------------------
-- The pass rule

-- | The pass rule of @docs/semantics.md@: the simulator exits 0, exactly
-- one line of standard output contains @GIN-PASS cycles=<n>@, and no line
-- of standard output contains @GIN-FAIL@ or @GIN-MISMATCH@. Standard error
-- is not inspected. The count is read as a whole number: a line with
-- @GIN-PASS cycles=80@ does not contain @GIN-PASS cycles=8@.
passes :: Int -> ToolResult -> Bool
passes n (code, out, _) =
  code == ExitSuccess
    && length (filter (containsCount (passMarker <> " cycles=") n) ls) == 1
    && not (any (\l -> any (`Text.isInfixOf` l) [failMarker, mismatchMarker]) ls)
  where
    ls = Text.lines out

-- | Does the line contain @prefix@ immediately followed by the decimal @n@
-- and then something other than a digit?
containsCount :: Text -> Int -> Text -> Bool
containsCount prefix n line =
  any (followedByCount . Text.drop (Text.length needle) . snd) (Text.breakOnAll needle line)
  where
    needle = prefix <> Text.pack (show n)
    followedByCount rest = maybe True (not . isDigit . fst) (Text.uncons rest)

-- | The run passes by the pass rule.
shouldPass :: String -> Int -> ToolResult -> Expectation
shouldPass what n result =
  unless (passes n result) $
    expectationFailure (describeRun (what <> ": expected GIN-PASS cycles=" <> show n) result)

-- | The run fails by the pass rule, reporting exactly @k@ mismatches: @k@
-- mismatch lines, one @GIN-FAIL mismatches=<k>@ line and no pass line.
shouldFailWith :: String -> Int -> Int -> ToolResult -> Expectation
shouldFailWith what n k result@(_, out, _) =
  unless ok $
    expectationFailure (describeRun (what <> ": expected " <> show k <> " mismatches") result)
  where
    ls = Text.lines out
    marked marker = filter (marker `Text.isInfixOf`) ls
    ok =
      not (passes n result)
        && null (marked passMarker)
        && length (marked mismatchMarker) == k
        && fmap (containsCount (failMarker <> " mismatches=") k) (marked failMarker) == [True]

describeRun :: String -> ToolResult -> String
describeRun what (code, out, err) =
  unlines
    [ what
    , "exit: " <> show code
    , "stdout:"
    , clip out
    , "stderr:"
    , clip err
    ]
  where
    clip = Text.unpack . Text.take 4000

-- | The pass rule on hand-written simulator results for an 8-cycle run.
passRuleSpec :: Spec
passRuleSpec =
  forM_ cases $ \(what, result, expected) ->
    it what $ passes 8 result `shouldBe` expected
  where
    stdoutOnly out = (ExitSuccess, out, "")
    cases :: [(String, ToolResult, Bool)]
    cases =
      [ ("accepts exactly one pass line", stdoutOnly "GIN-PASS cycles=8\n", True)
      , ("accepts text around the pass marker", stdoutOnly "x GIN-PASS cycles=8 done", True)
      , ("ignores markers on standard error", (ExitSuccess, "GIN-PASS cycles=8", "GIN-FAIL"), True)
      , ("rejects a nonzero exit", (ExitFailure 1, "GIN-PASS cycles=8\n", ""), False)
      , ("rejects another cycle count", stdoutOnly "GIN-PASS cycles=80\n", False)
      , ("rejects a missing pass line", stdoutOnly "", False)
      , ("rejects two pass lines", stdoutOnly "GIN-PASS cycles=8\nGIN-PASS cycles=8\n", False)
      ,
        ( "rejects a mismatch line"
        , stdoutOnly "GIN-MISMATCH cycle=0 port=a expected=0 got=1\nGIN-PASS cycles=8\n"
        , False
        )
      , ("rejects a fail line", stdoutOnly "GIN-PASS cycles=8\nGIN-FAIL mismatches=0\n", False)
      ]
