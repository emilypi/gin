-- | Translation validation of the circuits exported from Lean.
--
-- Each example under @examples/<name>/@ is the output of
-- @scripts/export-examples.sh@: the core IR of a Lean definition whose
-- refinement theorem the kernel checked (@<name>.gin.json@), and test
-- vectors computed by running the compiled Lean definition on seeded
-- inputs (@<name>.vectors.json@). For every example these tests check that
--
--   * both reference simulators ("Gin.Sim") reproduce the Lean vectors
--     exactly, the core IR simulator on the program as exported and the
--     normal-form simulator on the normalized program;
--   * the exported program has the interface of the hand-written fixture of
--     the same circuit ("Gin.Examples") and behaves like it: each replays
--     the other's vectors;
--   * @gin validate@ passes every check on all three targets, so the HDL
--     simulators reproduce the Lean vectors too, and fails when an expected
--     output is changed.
--
-- The files are read as committed. After changing the Lean sources, rerun
-- @scripts/export-examples.sh@ and commit its output; @scripts/validate.sh@
-- checks that the committed files are what the export produces. Tests
-- that run the HDL tools are pending when a tool is missing, or fail when
-- @GIN_REQUIRE_TOOLS=1@.
module Gin.LeanExamplesSpec (spec) where

import Control.Exception (bracket)
import Control.Monad (forM_, unless)
import Data.Bifunctor (first)
import Data.ByteString qualified as ByteString
import Data.ByteString.Lazy qualified as LazyByteString
import Data.List (unsnoc)
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Text.Encoding qualified as Text
import GHC.IO.Handle (hDuplicate, hDuplicateTo)
import Gin.Backend.Types (Target (..), mismatchMarker, targetName)
import Gin.Certificate (checkCertificate, defaultPolicy)
import Gin.Core.Check (checkProgram)
import Gin.Core.Json (decodeProgram, decodeVectors, encodeVectors)
import Gin.Core.Normal (NModule (..))
import Gin.Core.Syntax (Certificate (..), Port (..), Program (..), TopEntity (..), Value (..))
import Gin.Driver (runCli)
import Gin.Error (GinError, renderError)
import Gin.Examples
  ( counterProgram
  , counterVectors
  , detectorProgram
  , detectorVectors
  , macProgram
  , macVectors
  )
import Gin.Normalize (checkNormal, normalize)
import Gin.Sim (simulateCore, simulateNormal)
import Gin.TestUtil (itWithTools, withTempDir)
import Gin.Vectors (Cycle (..), Vectors (..))
import System.Exit (ExitCode (..))
import System.FilePath ((</>))
import System.IO (Handle, IOMode (..), hClose, hFlush, stderr, stdout, withBinaryFile)
import Test.Hspec
  ( Expectation
  , Spec
  , describe
  , expectationFailure
  , it
  , shouldBe
  , shouldSatisfy
  )

----------------------------------------------------------------------
-- Spec

-- | Every exported example, checked against its Lean vectors, its
-- hand-written fixture and the HDL simulators.
spec :: Spec
spec = forM_ leanExamples $ \ex -> describe ("examples" </> exName ex) $ do
  vectorsSpec ex
  fixtureSpec ex
  validateSpec ex

-- | The reference simulators reproduce the vectors computed in Lean.
vectorsSpec :: LeanExample -> Spec
vectorsSpec ex = do
  it "[lean-vectors-match] loads as gin loads it, with vectors for its top entity" $
    withExported ex $ \p vs -> do
      let top = progTop p
      vecTop vs `shouldBe` topName top
      vecInputs vs `shouldBe` topInputs top
      vecOutputs vs `shouldBe` topOutputs top
      length (vecCycles vs) `shouldBe` leanCycles
  it "[lean-vectors-match] simulateCore reproduces the exported vectors exactly" $
    withExported ex $ \p vs ->
      runCore p (inputRows vs) `shouldBe` Right (outputRows vs)
  it "[lean-vectors-match] simulateNormal . normalize reproduces the exported vectors exactly" $
    withExported ex $ \p vs ->
      stage "normalizing" (normalize p) $ \m -> do
        checkNormal m `shouldBe` Right ()
        nmName m `shouldBe` topName (progTop p)
        runNormal m (inputRows vs) `shouldBe` Right (outputRows vs)

-- | The exported program is the circuit the hand-written fixture describes.
fixtureSpec :: LeanExample -> Spec
fixtureSpec ex = do
  it "[lean-fixture-agreement] has the fixture's top entity, ports and theorem" $
    withExported ex $ \p vs -> do
      progTop p `shouldBe` progTop fixture
      certTheorem (progCertificate p) `shouldBe` certTheorem (progCertificate fixture)
      (vecInputs vs, vecOutputs vs) `shouldBe` (vecInputs fixtureVs, vecOutputs fixtureVs)
  it "[lean-fixture-agreement] reproduces the first cycles the fixture's vectors give" $
    withExported ex $ \p _ -> do
      length (vecCycles fixtureVs) `shouldSatisfy` (> 0)
      runCore p (inputRows fixtureVs) `shouldBe` Right (outputRows fixtureVs)
      stage "normalizing" (normalize p) $ \m ->
        runNormal m (inputRows fixtureVs) `shouldBe` Right (outputRows fixtureVs)
  it "[lean-fixture-agreement] the fixture reproduces the exported vectors" $
    withExported ex $ \_ vs ->
      runCore fixture (inputRows vs) `shouldBe` Right (outputRows vs)
  where
    fixture = exFixture ex
    fixtureVs = exFixtureVectors ex

-- | @gin validate@ on the committed files, with the HDL tools of the
-- process's @PATH@, as a user runs it.
validateSpec :: LeanExample -> Spec
validateSpec ex = do
  itWithTools hdlTools "[lean-e2e] gin validate passes every check on all three targets" $ do
    r <- gin ["validate", programFile ex, "--vectors", vectorsFile ex]
    r `shouldExit` ExitSuccess
    outLines r `shouldBe` (["sim-core: PASS", "sim-normal: PASS"] <> concatMap passes targets)
    runErr r `shouldBe` ""
  itWithTools hdlTools "[lean-e2e] gin validate fails every simulation when an output is changed" $
    withExported ex $ \_ vs -> case changeLastOutput vs of
      Nothing -> expectationFailure "the vectors have no output to change"
      Just (changed, mismatch) -> withTempDir $ \dir -> do
        let file = dir </> exName ex <> ".vectors.json"
        LazyByteString.writeFile file (encodeVectors changed)
        r <- gin ["validate", programFile ex, "--vectors", file]
        r `shouldExit` ExitFailure 1
        case outLines r of
          core : normal : hdl -> do
            core `shouldBe` "sim-core: FAIL " <> mismatch
            normal `shouldBe` "sim-normal: FAIL " <> mismatch
            -- The designs still lint; every testbench reports the change.
            fmap (Text.unwords . take 2 . Text.words) hdl
              `shouldBe` concatMap (\t -> [check t "lint" "PASS", check t "run" "FAIL"]) targets
          ls -> expectationFailure ("expected one line per check, got " <> show ls)
        -- The failing runs' output goes to standard error: one mismatch each.
        length (filter (mismatchMarker `Text.isInfixOf`) (Text.lines (runErr r)))
          `shouldBe` length targets
  where
    passes t = [check t "lint" "PASS", check t "run" "PASS"]
    check t what verdict = targetName t <> "-" <> what <> ": " <> verdict

----------------------------------------------------------------------
-- The examples

-- | An exported example and the hand-written fixture of the same circuit.
data LeanExample = LeanExample
  { exName :: !String
  , exFixture :: !Program
  , exFixtureVectors :: !Vectors
  }

leanExamples :: [LeanExample]
leanExamples =
  [ LeanExample "counter" counterProgram counterVectors
  , LeanExample "detector" detectorProgram detectorVectors
  , LeanExample "mac" macProgram macVectors
  ]

programFile, vectorsFile :: LeanExample -> FilePath
programFile ex = "examples" </> exName ex </> exName ex <> ".gin.json"
vectorsFile ex = "examples" </> exName ex </> exName ex <> ".vectors.json"

-- | The exporter writes 64 cycles of vectors for every example.
leanCycles :: Int
leanCycles = 64

-- | Decode an example's committed files and run the checks every gin
-- command runs on loading: type checking and the default axiom policy.
withExported :: LeanExample -> (Program -> Vectors -> Expectation) -> Expectation
withExported ex k = do
  programJson <- readBytes (programFile ex)
  vectorsJson <- readBytes (vectorsFile ex)
  stage ("loading " <> programFile ex) (load programJson vectorsJson) (uncurry k)
  where
    readBytes path = LazyByteString.fromStrict <$> ByteString.readFile path
    load programJson vectorsJson = do
      p <- decodeProgram programJson
      checkProgram p
      checkCertificate defaultPolicy (progCertificate p)
      vs <- decodeVectors vectorsJson
      pure (p, vs)

-- | Continue with a stage's result, or fail with its rendered error.
stage :: String -> Either GinError a -> (a -> Expectation) -> Expectation
stage what result k = case result of
  Left e -> expectationFailure (what <> " failed:\n" <> Text.unpack (renderError e))
  Right a -> k a

-- | The vectors with the expected value of the first output port changed in
-- the last cycle, and the mismatch the reference simulators then report.
changeLastOutput :: Vectors -> Maybe (Vectors, Text)
changeLastOutput vs = case (unsnoc (vecCycles vs), vecOutputs vs) of
  (Just (earlier, c), port : _) -> case cycOutputs c of
    actual : rest ->
      let expected = otherValue actual
       in Just
            ( vs {vecCycles = earlier <> [c {cycOutputs = expected : rest}]}
            , Text.unwords
                [ "cycle=" <> tshow (length earlier)
                , "port=" <> portName port
                , "expected=" <> renderValue expected
                , "got=" <> renderValue actual
                ]
            )
    [] -> Nothing
  _ -> Nothing

-- | A different value of the same type.
otherValue :: Value -> Value
otherValue = \case
  VBool b -> VBool (not b)
  VBV w x -> VBV w ((x + 1) `mod` (2 ^ w))
  VTuple vs -> VTuple (fmap otherValue vs)

-- | A value as gin prints it in a mismatch, which is how the vectors file
-- writes it.
renderValue :: Value -> Text
renderValue = \case
  VBool b -> if b then "true" else "false"
  VBV _ x -> tshow x
  VTuple vs -> "(" <> Text.intercalate ", " (fmap renderValue vs) <> ")"

tshow :: (Show a) => a -> Text
tshow = Text.pack . show

----------------------------------------------------------------------
-- Reference simulators

inputRows, outputRows :: Vectors -> [[Value]]
inputRows = fmap cycInputs . vecCycles
outputRows = fmap cycOutputs . vecCycles

-- | 'simulateCore' with its error rendered. The examples are far inside
-- its bounds, so any error, inconclusive or not, fails a test.
runCore :: Program -> [[Value]] -> Either Text [[Value]]
runCore p = first renderError . simulateCore p

runNormal :: NModule -> [[Value]] -> Either Text [[Value]]
runNormal m = first renderError . simulateNormal m

----------------------------------------------------------------------
-- Running the CLI

targets :: [Target]
targets = [minBound .. maxBound]

-- | The tools @gin validate@ runs for the three targets.
hdlTools :: [String]
hdlTools = ["iverilog", "vvp", "verilator", "nvc"]

-- | What one CLI invocation returned and printed.
data Run = Run
  { runCode :: !ExitCode
  , runOut :: !Text
  , runErr :: !Text
  }
  deriving stock (Show)

-- | Run the CLI as the @gin@ executable does, in the process's
-- environment, capturing standard output and standard error.
gin :: [String] -> IO Run
gin args = withTempDir $ \dir -> do
  ((code, err), out) <-
    capture stdout (dir </> "stdout") (capture stderr (dir </> "stderr") (runCli args))
  pure (Run code out err)

-- | Point a standard handle at a file while the action runs, and return
-- what was written to it.
capture :: Handle -> FilePath -> IO a -> IO (a, Text)
capture h file act = do
  hFlush h
  a <- withBinaryFile file WriteMode $ \fh ->
    bracket (hDuplicate h) (\saved -> hFlush h >> hDuplicateTo saved h >> hClose saved) $ \_ ->
      hDuplicateTo fh h >> act
  (,) a . Text.decodeUtf8Lenient <$> ByteString.readFile file

outLines :: Run -> [Text]
outLines = Text.lines . runOut

shouldExit :: Run -> ExitCode -> Expectation
shouldExit r code =
  unless (runCode r == code) $
    expectationFailure ("expected " <> show code <> ", got " <> show r)
