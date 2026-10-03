-- | Runs the compiler pipeline and implements the CLI commands.
--
-- > gin check     FILE.gin.json [--allow-axiom NAME]...
-- > gin compile   FILE.gin.json [--target T]... [-o DIR] [--allow-axiom NAME]...
-- > gin testbench FILE.gin.json --vectors V.json [--target T]... [-o DIR] [--allow-axiom NAME]...
-- > gin sim       FILE.gin.json --vectors V.json [--allow-axiom NAME]...
-- > gin validate  FILE.gin.json --vectors V.json [--target T]... [-o DIR]
-- >               [--allow-axiom NAME]... [--allow-missing-tools] [--tool-timeout SECONDS]
--
-- @T@ is @verilog@, @systemverilog@ or @vhdl@; without @--target@ every
-- target is generated.
--
-- Every command first loads the IR file: it reads at most
-- 'maxInputBytes' (plus one, to detect a larger file), decodes it
-- ('decodeProgram'), type checks it ('checkProgram') and checks its
-- certificate ('checkCertificate') against 'defaultPolicy' extended with
-- the @--allow-axiom@ names. No flag admits an axiom in
-- 'Gin.Certificate.alwaysRejected' or one containing @._native.@. Commands
-- that take @--vectors@ then decode the vectors and reject them unless
-- their top name and their input and output ports (names, types and
-- order) equal the program's top entity.
--
-- [@check@] Stops after loading.
--
-- [@compile@] Normalizes, builds the netlist and writes @DIR/<top>.<ext>@
--   for each target. @DIR@ defaults to the current directory and is created
--   if missing. File names derive only from the top name, which is a legal
--   HDL identifier. Each file is written to a temporary name in @DIR@ and
--   renamed into place, so an existing file (or a symbolic link) is
--   replaced, never written through, and a target that fails leaves
--   nothing behind.
--
-- [@testbench@] Like @compile@, and also writes @DIR/<top>_tb.<ext>@.
--
-- [@sim@] Normalizes (which is bounded) and then runs both reference
--   simulators ("Gin.Sim") on the vectors' inputs, printing one line each:
--
--   > sim-core: PASS
--   > sim-normal: FAIL cycle=<t> port=<name> expected=<v> got=<v>
--
--   reporting the first mismatching cycle and port. Values print as
--   @true@ and @false@ or as the decimal value of a bit vector, as in the
--   vectors file. When the core simulator stops at one of its bounds
--   ('isBudgetError') it prints @sim-core: SKIP(inconclusive: <message>)@,
--   which is not a failure: the normal-form simulator and the HDL runs
--   still check the circuit against the vectors, only the localization of
--   a disagreement is lost.
--
-- [@validate@] Runs @sim@, then for each target generates the design and
--   testbench (into @DIR@ when @-o@ is given, else into a temporary
--   directory), copies them into a fresh private temporary directory and
--   runs the target's lint commands and testbench there. It prints one line
--   per check, @<check>: PASS@, @<check>: FAIL <reason>@ or
--   @<check>: SKIP(<reason>)@, for the checks @sim-core@, @sim-normal@,
--   @<target>-lint@ and @<target>-run@; the output of a failing tool goes
--   to standard error. A testbench run passes by the rule in
--   @docs/semantics.md@, applied to standard output only. A tool that is
--   not found fails its check, or skips it with @--allow-missing-tools@.
--
-- Exit status: 0 on success, 1 when a check, compile or validation fails
-- (errors are printed with 'renderError', so a certificate error starts
-- with @certificate error:@), 2 on a usage error.
--
-- External tools are looked up in the directories of the @PATH@ of the
-- environment 'runCliWith' is given (empty entries, which a shell would
-- read as the current directory, are ignored) and spawned by absolute
-- path, with an argument list rather than a shell command, with that
-- environment, and in their own process group. Each run is limited to
-- @--tool-timeout@ seconds ('defaultToolTimeoutSeconds' by default); a run
-- that takes longer is interrupted and terminated, and its check fails. A
-- tool that ignores both signals keeps running after gin has moved on.
--
-- Text that comes from input files is printed with control and other
-- invisible characters replaced by @?@, so a file cannot drive the
-- terminal.
module Gin.Driver
  ( runCli
  , runCliWith
  ) where

import Control.Applicative (many, optional, (<**>), (<|>))
import Control.Concurrent (forkIO, killThread)
import Control.Concurrent.MVar (newEmptyMVar, putMVar, readMVar)
import Control.Exception
  ( IOException
  , SomeAsyncException
  , SomeException
  , bracketOnError
  , displayException
  , evaluate
  , finally
  , fromException
  , throwIO
  , try
  )
import Control.Monad (guard, unless, void, when)
import Control.Monad.Except (ExceptT (..), liftEither, runExceptT, throwError)
import Control.Monad.IO.Class (liftIO)
import Data.ByteString qualified as BS
import Data.ByteString.Lazy qualified as LBS
import Data.Char (GeneralCategory (..), generalCategory, isDigit)
import Data.Containers.ListUtils (nubOrd)
import Data.Either (fromRight)
import Data.Foldable (for_, traverse_)
import Data.List (find)
import Data.Maybe (catMaybes, fromMaybe, isJust, listToMaybe)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Text.Encoding qualified as Text
import Data.Traversable (for)
import GHC.IO.Exception (IOException (..))
import Gin.Backend.SystemVerilog (systemVerilog)
import Gin.Backend.Types
  ( Backend (..)
  , Target (..)
  , failMarker
  , mismatchMarker
  , parseTarget
  , passMarker
  , targetName
  )
import Gin.Backend.VHDL (vhdl)
import Gin.Backend.Verilog (verilog)
import Gin.Certificate (CertPolicy (..), checkCertificate, defaultPolicy)
import Gin.Core.Check (checkProgram)
import Gin.Core.Json (decodeProgram, decodeVectors)
import Gin.Core.Normal (NModule)
import Gin.Core.Syntax (Port (..), Program (..), TopEntity (..), Ty (..), Value (..))
import Gin.Error (GinError (..), Stage (..), ginError, renderError, withContext)
import Gin.Limits (defaultToolTimeoutSeconds, maxInputBytes)
import Gin.Netlist.Build (buildNetlist)
import Gin.Netlist.Types (HwType (..), Ident (..), Module (..), Net (..), Output (..))
import Gin.Normalize (checkNormal, normalize)
import Gin.Sim (isBudgetError, simulateCore, simulateNormal)
import Gin.Vectors (Cycle (..), Vectors (..))
import Options.Applicative
  ( Parser
  , ParserInfo
  , ParserResult (..)
  , ReadM
  , command
  , eitherReader
  , execCompletion
  , execParserPure
  , footer
  , fullDesc
  , header
  , help
  , helper
  , hsubparser
  , info
  , long
  , metavar
  , option
  , prefs
  , progDesc
  , renderFailure
  , short
  , showDefault
  , showHelpOnEmpty
  , strArgument
  , strOption
  , switch
  , value
  )
import System.Directory
  ( copyFile
  , createDirectoryIfMissing
  , doesDirectoryExist
  , findExecutablesInDirectories
  , makeAbsolute
  , removeFile
  , renameFile
  )
import System.Environment (getEnvironment)
import System.Exit (ExitCode (..))
import System.FilePath ((<.>), (</>))
import System.IO
  ( Handle
  , IOMode (..)
  , hClose
  , hFlush
  , openBinaryTempFileWithDefaultPermissions
  , stderr
  , stdout
  , withBinaryFile
  )
import System.IO.Temp (withSystemTempDirectory)
import System.Process
  ( CreateProcess (..)
  , ProcessHandle
  , StdStream (..)
  , interruptProcessGroupOf
  , proc
  , terminateProcess
  , waitForProcess
  , withCreateProcess
  )
import System.Timeout (timeout)
import Text.Read (readMaybe)

-- | Parse the arguments and run one command. Never calls 'exitWith';
-- returns 'ExitSuccess', @ExitFailure 1@ for a failed check or compile,
-- or @ExitFailure 2@ for a usage error.
runCli :: [String] -> IO ExitCode
runCli args = getEnvironment >>= \env -> runCliWith env args

-- | 'runCli' with an explicit environment. External tools are looked up
-- in the directories of the environment's @PATH@ and spawned by absolute
-- path with that environment, so tests can substitute or hide tools
-- without touching the process environment.
runCliWith :: [(String, String)] -> [String] -> IO ExitCode
runCliWith environment args =
  case execParserPure (prefs showHelpOnEmpty) cliInfo args of
    Success cmd -> runCommand environment cmd
    Failure failure -> case renderFailure failure progName of
      (msg, ExitSuccess) -> ExitSuccess <$ putLine stdout (Text.pack msg)
      (msg, ExitFailure _) -> ExitFailure 2 <$ putLine stderr (Text.pack msg)
    CompletionInvoked completion -> do
      msg <- execCompletion completion progName
      ExitSuccess <$ putText stdout (Text.pack msg)

progName :: String
progName = "gin"

----------------------------------------------------------------------
-- Command line

-- | The environment external tools see.
type Env = [(String, String)]

-- | One parsed command line.
data Command
  = CheckCmd !Inputs
  | CompileCmd !Inputs !Outputs
  | TestbenchCmd !Inputs !FilePath !Outputs
  | SimCmd !Inputs !FilePath
  | ValidateCmd !Inputs !FilePath !Outputs !ToolOptions

-- | The IR file and the axioms its certificate may use beyond
-- 'defaultPolicy'.
data Inputs = Inputs
  { inFile :: !FilePath
  , inAllowAxioms :: ![Text]
  }

-- | Which targets to generate, and where.
data Outputs = Outputs
  { outTargets :: ![Target]
  -- ^ Empty means every target.
  , outDir :: !(Maybe FilePath)
  }

-- | How @validate@ runs external tools.
data ToolOptions = ToolOptions
  { toolAllowMissing :: !Bool
  , toolTimeoutSeconds :: !Int
  }

cliInfo :: ParserInfo Command
cliInfo =
  info (commands <**> helper) $
    fullDesc
      <> header "gin - compile proof-carrying Lean 4 circuits to Verilog, SystemVerilog and VHDL"
      <> progDesc "Check, compile, simulate and validate a circuit exported by the Lean side."
      <> footer
        "Exit status: 0 on success, 1 when a check, compile or validation fails, \
        \2 on a usage error."

commands :: Parser Command
commands =
  hsubparser $
    cmd
      "check"
      "Decode and type check FILE and check its certificate."
      (CheckCmd . fst <$> inputs (pure ()))
      <> cmd
        "compile"
        "Write DIR/<top>.<ext> for each target."
        (uncurry CompileCmd <$> inputs outputs)
      <> cmd
        "testbench"
        "Write DIR/<top>.<ext> and the testbench DIR/<top>_tb.<ext> for each target."
        ((\(i, (v, o)) -> TestbenchCmd i v o) <$> inputs ((,) <$> vectorsOpt <*> outputs))
      <> cmd
        "sim"
        "Run both reference simulators on the vectors and compare their outputs."
        (uncurry SimCmd <$> inputs vectorsOpt)
      <> cmd
        "validate"
        "Run sim, then lint the generated HDL and run its testbench with the HDL tools."
        ( (\(i, (v, o)) t -> ValidateCmd i v o t)
            <$> inputs ((,) <$> vectorsOpt <*> outputs)
            <*> toolOptions
        )
  where
    cmd name desc p = command name (info p (progDesc desc))

-- | The IR file, the command's own options, then @--allow-axiom@, in the
-- order the usage line shows them.
inputs :: Parser a -> Parser (Inputs, a)
inputs rest =
  (\file a axioms -> (Inputs file axioms, a))
    <$> strArgument (metavar "FILE.gin.json" <> help "IR file exported by the Lean side")
    <*> rest
    <*> many
      ( strOption
          ( long "allow-axiom"
              <> metavar "NAME"
              <> help
                "Also accept this axiom in the certificate (repeatable). sorryAx, \
                \Lean.ofReduceBool, Lean.ofReduceNat, Lean.trustCompiler and ._native. \
                \axioms are always rejected."
          )
      )

vectorsOpt :: Parser FilePath
vectorsOpt =
  strOption (long "vectors" <> metavar "V.json" <> help "Test vectors exported by the Lean side")

outputs :: Parser Outputs
outputs =
  Outputs
    <$> many
      ( option
          targetReader
          ( long "target"
              <> metavar "T"
              <> help "verilog, systemverilog or vhdl (repeatable; default: all three)"
          )
      )
    <*> optional
      ( orCurrent
          <$> strOption (short 'o' <> metavar "DIR" <> help "Output directory (created if missing)")
      )
  where
    orCurrent dir = if null dir then "." else dir

toolOptions :: Parser ToolOptions
toolOptions =
  ToolOptions
    <$> switch
      ( long "allow-missing-tools"
          <> help "Skip, instead of failing, the checks whose tool is not on PATH"
      )
    <*> option
      secondsReader
      ( long "tool-timeout"
          <> metavar "SECONDS"
          <> value defaultToolTimeoutSeconds
          <> showDefault
          <> help "Wall-clock limit for each external tool run"
      )

targetReader :: ReadM Target
targetReader = eitherReader $ \s ->
  maybe
    (Left ("unknown target " <> show s <> "; expected verilog, systemverilog or vhdl"))
    Right
    (parseTarget (Text.pack s))

-- | A whole number of seconds, at least 1 and small enough that its
-- microseconds fit in an 'Int'.
secondsReader :: ReadM Int
secondsReader = eitherReader $ \s ->
  maybe (Left ("expected a whole number of seconds from 1 to " <> show maxSeconds)) Right $ do
    guard (not (null s) && length s <= 18 && all isDigit s)
    n <- readMaybe s
    guard (n >= 1 && n <= maxSeconds)
    pure (fromInteger n)
  where
    maxSeconds = toInteger (maxBound :: Int) `div` 1000000

----------------------------------------------------------------------
-- Commands

-- | Stage errors abort a command; check outcomes do not.
type Pipe = ExceptT GinError IO

runCommand :: Env -> Command -> IO ExitCode
runCommand environment cmd =
  tryNonAsync (runExceptT (execute environment cmd)) >>= \case
    Right (Right True) -> pure ExitSuccess
    Right (Right False) -> pure (ExitFailure 1)
    Right (Left e) -> ExitFailure 1 <$ putLine stderr (renderError e)
    Left ex ->
      ExitFailure 1
        <$ ignoreIO (putLine stderr (renderError (driverError (Text.pack (displayException ex)))))

-- | Run a command; 'False' when one of its checks failed.
execute :: Env -> Command -> Pipe Bool
execute environment = \case
  CheckCmd ins -> True <$ loadProgram ins
  CompileCmd ins outs -> do
    prog <- loadProgram ins
    (_, m) <- compileProgram prog
    for_ (backendsOf outs) $ \b -> writeGroup (outputDir outs) (generatedFiles m Nothing b)
    pure True
  TestbenchCmd ins vecFile outs -> do
    prog <- loadProgram ins
    vecs <- loadVectors prog vecFile
    (_, m) <- compileProgram prog
    liftEither (testbenchPrecondition m vecs)
    for_ (backendsOf outs) $ \b -> writeGroup (outputDir outs) (generatedFiles m (Just vecs) b)
    pure True
  SimCmd ins vecFile -> do
    prog <- loadProgram ins
    vecs <- loadVectors prog vecFile
    nm <- liftEither (normalize prog)
    liftIO (reportAll (simChecks prog nm vecs))
  ValidateCmd ins vecFile outs tools -> do
    prog <- loadProgram ins
    vecs <- loadVectors prog vecFile
    (nm, m) <- compileProgram prog
    liftEither (testbenchPrecondition m vecs)
    simOk <- liftIO (reportAll (simChecks prog nm vecs))
    hdlOk <- for (backendsOf outs) (validateTarget environment tools m vecs (outDir outs))
    pure (simOk && and hdlOk)

outputDir :: Outputs -> FilePath
outputDir = fromMaybe "." . outDir

backendsOf :: Outputs -> [Backend]
backendsOf outs = fmap backendFor $ case outTargets outs of
  [] -> [minBound .. maxBound]
  ts -> nubOrd ts

backendFor :: Target -> Backend
backendFor = \case
  Verilog -> verilog
  SystemVerilog -> systemVerilog
  VHDL -> vhdl

----------------------------------------------------------------------
-- Loading

-- | Read, decode and check the IR file, including its certificate.
loadProgram :: Inputs -> Pipe Program
loadProgram ins = do
  let file = inFile ins
  bytes <- readInput file
  liftEither . inFileContext file $ do
    prog <- decodeProgram bytes
    checkProgram prog
    checkCertificate (policyWith (inAllowAxioms ins)) (progCertificate prog)
    pure prog

-- | 'defaultPolicy' plus the given axioms. 'checkCertificate' still rejects
-- the axioms no policy can admit.
policyWith :: [Text] -> CertPolicy
policyWith extra = CertPolicy (allowedAxioms defaultPolicy <> Set.fromList extra)

-- | Read and decode the vectors file, and check that it describes the
-- program's top entity.
loadVectors :: Program -> FilePath -> Pipe Vectors
loadVectors prog file = do
  bytes <- readInput file
  liftEither . inFileContext file $ do
    vecs <- decodeVectors bytes
    vecs <$ matchVectors (progTop prog) vecs

inFileContext :: FilePath -> Either GinError a -> Either GinError a
inFileContext file = withContext ("in " <> Text.pack file)

-- | At most @'maxInputBytes' + 1@ bytes of a file, so that the decoder can
-- reject a larger file without gin reading all of it.
readInput :: FilePath -> Pipe LBS.ByteString
readInput file =
  liftIO (tryIO (withBinaryFile file ReadMode readBounded)) >>= \case
    Left e -> throwError (driverError ("cannot read " <> Text.pack file <> ": " <> ioMessage e))
    Right bytes -> pure bytes
  where
    readBounded h = do
      contents <- LBS.hGetContents h
      let bounded = LBS.take (fromIntegral maxInputBytes + 1) contents
      LBS.fromStrict <$> evaluate (LBS.toStrict bounded)

-- | The vectors must be for the program's top entity, with the same ports
-- (names, types and order).
matchVectors :: TopEntity -> Vectors -> Either GinError ()
matchVectors top vecs = do
  unless (vecTop vecs == topName top) $
    Left . driverError $
      "the vectors are for top entity "
        <> clip (vecTop vecs)
        <> ", but the program's top entity is "
        <> clip (topName top)
  matchPorts "input" (topInputs top) (vecInputs vecs)
  matchPorts "output" (topOutputs top) (vecOutputs vecs)

matchPorts :: Text -> [Port] -> [Port] -> Either GinError ()
matchPorts kind expected actual = do
  for_ (zip3 [0 :: Int ..] expected actual) $ \(i, e, a) ->
    unless (e == a) $
      Left . driverError $
        kind
          <> " port "
          <> showT i
          <> " is "
          <> renderPort a
          <> " in the vectors, but "
          <> renderPort e
          <> " in the program"
  unless (length expected == length actual) $
    Left . driverError $
      "the vectors have "
        <> ports (length actual)
        <> ", but the program has "
        <> ports (length expected)
  where
    ports n = showT n <> " " <> kind <> (if n == 1 then " port" else " ports")

renderPort :: Port -> Text
renderPort p = clip (portName p) <> " : " <> renderTy (portTy p)
  where
    renderTy = \case
      TBool -> "Bool"
      TBitVec w -> "BitVec " <> showT w
      _ -> "a non-scalar type"

-- | Untrusted names in error messages are cut short.
clip :: Text -> Text
clip t
  | Text.length t > 64 = Text.take 64 t <> "..."
  | otherwise = t

----------------------------------------------------------------------
-- Compiling and writing files

compileProgram :: Program -> Pipe (NModule, Module)
compileProgram prog = liftEither $ do
  nm <- normalize prog
  checkNormal nm
  m <- buildNetlist nm
  pure (nm, m)

-- | The precondition of 'backendTestbench': the vectors' ports are the
-- module's, by name, order and type. It follows from 'matchVectors', since
-- the netlist builder never renames ports; checked again here because a
-- testbench for other ports would be meaningless.
testbenchPrecondition :: Module -> Vectors -> Either GinError ()
testbenchPrecondition m vecs =
  unless
    ( fmap portShape (vecInputs vecs) == fmap netShape (modInputs m)
        && fmap portShape (vecOutputs vecs) == fmap (netShape . outNet) (modOutputs m)
    )
    (Left (driverError "the vectors' ports differ from the generated module's ports"))
  where
    portShape p = (portName p, hwType (portTy p))
    netShape n = (unIdent (netName n), Just (netType n))
    hwType = \case
      TBool -> Just HBit
      TBitVec w -> Just (HVec w)
      _ -> Nothing

-- | The files one backend generates, named after the module: the design
-- and, given vectors, the testbench.
generatedFiles :: Module -> Maybe Vectors -> Backend -> [(FilePath, Text)]
generatedFiles m mvecs b =
  (base <.> ext, backendRender b m)
    : foldMap (\vecs -> [(base <> "_tb" <.> ext, backendTestbench b m vecs)]) mvecs
  where
    base = Text.unpack (unIdent (modName m))
    ext = backendFileExt b

-- | Write a group of files into a directory, creating it if missing. Each
-- file is written to a temporary name in the directory and renamed into
-- place only once every file of the group is complete, so a failure
-- leaves none of them behind (and removes the temporary files). Renaming
-- replaces an existing file or symbolic link instead of writing through
-- it.
writeGroup :: FilePath -> [(FilePath, Text)] -> Pipe ()
writeGroup dir files = do
  guardIO $ createDirectoryIfMissing True dir
  for_ files $ \(name, _) -> do
    isDir <- guardIO $ doesDirectoryExist (dir </> name)
    when isDir . throwError . driverError $
      "cannot write " <> Text.pack (dir </> name) <> ": it is a directory"
  guardIO $ stage files []
  where
    guardIO :: IO a -> Pipe a
    guardIO act =
      liftIO (tryIO act) >>= \case
        Left e ->
          throwError (driverError ("cannot write to " <> Text.pack dir <> ": " <> ioMessage e))
        Right a -> pure a
    stage [] staged = for_ (reverse staged) (uncurry renameFile)
    stage ((name, content) : rest) staged =
      bracketOnError (writeTemp dir name content) (ignoreIO . removeFile) $ \tmp ->
        stage rest ((tmp, dir </> name) : staged)

-- | Write a file under a fresh hidden temporary name in the directory and
-- return that name.
writeTemp :: FilePath -> FilePath -> Text -> IO FilePath
writeTemp dir name content = do
  bytes <- evaluate (Text.encodeUtf8 content)
  bracketOnError
    (openBinaryTempFileWithDefaultPermissions dir ("." <> name <> ".tmp"))
    (\(tmp, h) -> hClose h >> ignoreIO (removeFile tmp))
    (\(tmp, h) -> tmp <$ (BS.hPut h bytes >> hClose h))

----------------------------------------------------------------------
-- Checks

-- | The result of one check.
data Outcome
  = Pass
  | -- | With a one-line reason.
    Fail !Text
  | -- | With a one-line reason.
    Skip !Text

isFail :: Outcome -> Bool
isFail = \case
  Fail _ -> True
  _ -> False

-- | Print one line per check, as each is computed; 'False' if any failed.
reportAll :: [(Text, Outcome)] -> IO Bool
reportAll checks = not . or <$> traverse (\(name, o) -> isFail o <$ report name o) checks

report :: Text -> Outcome -> IO ()
report name = \case
  Pass -> putLine stdout (name <> ": PASS")
  Fail why -> putLine stdout (name <> ": FAIL" <> (if Text.null why then "" else " " <> why))
  Skip why -> putLine stdout (name <> ": SKIP(" <> why <> ")")

-- | Both reference simulators against the vectors' expected outputs.
simChecks :: Program -> NModule -> Vectors -> [(Text, Outcome)]
simChecks prog nm vecs =
  [ ("sim-core", coreOutcome (simulateCore prog rows))
  , ("sim-normal", compareRows (vecOutputs vecs) expected (simulateNormal nm rows))
  ]
  where
    rows = fmap cycInputs (vecCycles vecs)
    expected = fmap cycOutputs (vecCycles vecs)
    coreOutcome = \case
      Left e | isBudgetError e -> Skip ("inconclusive: " <> oneLine (errMessage e : errContext e))
      r -> compareRows (vecOutputs vecs) expected r

-- | 'Pass' when the simulated rows equal the expected ones, else the first
-- mismatch.
compareRows :: [Port] -> [[Value]] -> Either GinError [[Value]] -> Outcome
compareRows ports expected = \case
  Left e -> Fail (oneLine (Text.lines (renderError e)))
  Right actual
    | length actual /= length expected ->
        Fail ("expected " <> showT (length expected) <> " cycles, got " <> showT (length actual))
    | otherwise ->
        maybe Pass Fail . listToMaybe . concat $
          zipWith3 rowMismatches [0 :: Int ..] expected actual
  where
    rowMismatches t want got
      | length want /= length got =
          [ "cycle="
              <> showT t
              <> " expected "
              <> showT (length want)
              <> " outputs, got "
              <> showT (length got)
          ]
      | otherwise =
          [ "cycle="
              <> showT t
              <> " port="
              <> portName p
              <> " expected="
              <> renderValue e
              <> " got="
              <> renderValue a
          | (p, e, a) <- zip3 ports want got
          , e /= a
          ]

renderValue :: Value -> Text
renderValue = \case
  VBool b -> if b then "true" else "false"
  VBV _ n -> showT n
  VTuple vs -> "(" <> Text.intercalate ", " (fmap renderValue vs) <> ")"

oneLine :: [Text] -> Text
oneLine = Text.intercalate ", " . filter (not . Text.null) . fmap Text.strip

----------------------------------------------------------------------
-- validate: HDL tools

-- | Generate one target's design and testbench, then lint and run them in
-- a fresh private directory. Prints the target's two check lines.
validateTarget :: Env -> ToolOptions -> Module -> Vectors -> Maybe FilePath -> Backend -> Pipe Bool
validateTarget environment tools m vecs dir b = inGenerationDir $ \genDir -> do
  writeGroup genDir files
  ExceptT . withSystemTempDirectory "gin-validate" $ \work -> runExceptT $ do
    copied <- liftIO . tryIO . for_ files $ \(name, _) -> copyFile (genDir </> name) (work </> name)
    case copied of
      Left e -> throwError (driverError ("cannot copy the generated files: " <> ioMessage e))
      Right () -> pure ()
    liftIO $ do
      lint <- runCheck environment tools work (lintRuns b base)
      reportWithOutput (check "lint") lint
      run <- runCheck environment tools work (testbenchRuns b base (length (vecCycles vecs)))
      reportWithOutput (check "run") run
      pure (not (isFail (fst lint) || isFail (fst run)))
  where
    files = generatedFiles m (Just vecs) b
    base = Text.unpack (unIdent (modName m))
    check kind = targetName (backendTarget b) <> "-" <> kind
    inGenerationDir act = case dir of
      Just d -> act d
      Nothing -> ExceptT (withSystemTempDirectory "gin-generated" (runExceptT . act))

-- | One external tool invocation and how its result is judged.
data ToolRun = ToolRun
  { trTool :: !String
  , trArgs :: ![String]
  , trJudge :: ExitCode -> Text -> Text -> Maybe Text
  -- ^ Exit code, standard output and standard error to a failure reason
  -- (completing "<tool> ..."), or 'Nothing' if the run passed.
  }

-- | The lint commands for a design file.
lintRuns :: Backend -> String -> [ToolRun]
lintRuns b base = case backendTarget b of
  Verilog -> [verilator "1364-2005", iverilog "-g2005"]
  SystemVerilog -> [verilator "1800-2017", iverilog "-g2012"]
  VHDL -> [ToolRun "nvc" ["-M", "1g", "--std=2008", "-a", design] exitedCleanly]
  where
    design = base <.> backendFileExt b
    verilator lang =
      ToolRun
        "verilator"
        ["--lint-only", "-Wall", "--default-language", lang, design]
        withoutWarnings
    iverilog gen = ToolRun "iverilog" [gen, "-o", "/dev/null", design] exitedCleanly

-- | The commands that build and run the testbench; the last one prints the
-- testbench protocol.
testbenchRuns :: Backend -> String -> Int -> [ToolRun]
testbenchRuns b base cycles = case backendTarget b of
  Verilog -> icarus "-g2005"
  SystemVerilog -> icarus "-g2012"
  VHDL ->
    [ ToolRun
        "nvc"
        ["-M", "1g", "--std=2008", "-a", design, testbench, "-e", base <> "_tb", "-r"]
        (passRule cycles)
    ]
  where
    ext = backendFileExt b
    design = base <.> ext
    testbench = base <> "_tb" <.> ext
    icarus gen =
      [ ToolRun "iverilog" [gen, "-o", "tb.vvp", design, testbench] exitedCleanly
      , ToolRun "vvp" ["-n", "tb.vvp"] (passRule cycles)
      ]

exitedCleanly :: ExitCode -> Text -> Text -> Maybe Text
exitedCleanly code _ _ = case code of
  ExitSuccess -> Nothing
  ExitFailure n
    | n < 0 -> Just ("was stopped by signal " <> showT (negate n))
    | otherwise -> Just ("exited with code " <> showT n)

-- | Verilator exits non-zero on a warning under @-Wall@; any warning in its
-- output fails the check as well.
withoutWarnings :: ExitCode -> Text -> Text -> Maybe Text
withoutWarnings code out err =
  exitedCleanly code out err
    <|> if any ("%Warning" `Text.isInfixOf`) [out, err] then Just "reported warnings" else Nothing

-- | The testbench pass rule of @docs/semantics.md@, on standard output
-- only: exit 0, no line containing 'failMarker' or 'mismatchMarker', and
-- exactly one line containing 'passMarker', which reads
-- @GIN-PASS cycles=<N>@ for the number of vector cycles.
passRule :: Int -> ExitCode -> Text -> Text -> Maybe Text
passRule cycles code out err =
  listToMaybe (catMaybes [markers, exitedCleanly code out err, passLine])
  where
    ls = Text.lines out
    markers =
      fmap
        (\l -> "printed " <> clip (Text.strip l))
        ( find (failMarker `Text.isInfixOf`) ls
            <|> find (mismatchMarker `Text.isInfixOf`) ls
        )
    passLine = case filter (passMarker `Text.isInfixOf`) ls of
      [l]
        | passedCycles l == Just (showT cycles) -> Nothing
        | otherwise ->
            Just ("printed " <> clip (Text.strip l) <> ", expected cycles=" <> showT cycles)
      found ->
        Just ("printed " <> showT (length found) <> " " <> passMarker <> " lines, expected one")
    passedCycles l = case Text.breakOn passCycles l of
      (_, rest)
        | Text.null rest -> Nothing
        | otherwise -> Just (Text.takeWhile isDigit (Text.drop (Text.length passCycles) rest))
    passCycles = passMarker <> " cycles="

-- | Print a check's line, then, on standard error, the output of the tool
-- that failed it.
reportWithOutput :: Text -> (Outcome, Maybe Text) -> IO ()
reportWithOutput name (outcome, output) = report name outcome >> traverse_ (putLine stderr) output

-- | Resolve every tool of a check, then run its commands in order in the
-- working directory, stopping at the first that fails. Returns the outcome
-- and the output of the tool that failed it, if it ran to the end.
runCheck :: Env -> ToolOptions -> FilePath -> [ToolRun] -> IO (Outcome, Maybe Text)
runCheck environment tools work runs = do
  resolved <- traverse (\r -> (,) r <$> resolveTool environment (trTool r)) runs
  case nubOrd [trTool r | (r, Nothing) <- resolved] of
    [] -> go [(r, exe) | (r, Just exe) <- resolved]
    missing -> pure (missingTools missing, Nothing)
  where
    missingTools names =
      (if toolAllowMissing tools then Skip else Fail) $
        (if length names == 1 then "missing tool: " else "missing tools: ")
          <> Text.intercalate ", " (fmap Text.pack names)
    seconds = toolTimeoutSeconds tools
    go [] = pure (Pass, Nothing)
    go ((r, exe) : rest) = do
      result <- runTool environment work seconds exe (trArgs r)
      let tool = Text.pack (trTool r)
          failed why = (Fail (tool <> " " <> why), Nothing)
      case result of
        Finished code out err -> case trJudge r code out err of
          Nothing -> go rest
          Just why -> pure (Fail (tool <> " " <> why), Just (toolOutput r out err))
        TimedOut -> pure (failed ("timed out after " <> showT seconds <> " s"))
        NotStarted why -> pure (failed ("could not be started: " <> why))
    toolOutput r out err =
      Text.intercalate "\n" $
        ("output of " <> Text.unwords (fmap Text.pack (trTool r : trArgs r)) <> ":")
          : (excerpt out <> excerpt err)

-- | At most the first 40 lines of a tool's output, each cut to 500
-- characters, indented.
excerpt :: Text -> [Text]
excerpt t =
  fmap (("  " <>) . cut) shown
    <> ["  ... (" <> showT (length rest) <> " more lines)" | not (null rest)]
  where
    (shown, rest) = splitAt 40 (Text.lines t)
    cut l = if Text.length l > 500 then Text.take 500 l <> " ..." else l

-- | The first executable of that name in the directories of the
-- environment's @PATH@, as an absolute path.
resolveTool :: Env -> String -> IO (Maybe FilePath)
resolveTool environment name =
  tryIO (findExecutablesInDirectories dirs name >>= traverse makeAbsolute . listToMaybe)
    >>= either (const (pure Nothing)) pure
  where
    dirs =
      fmap Text.unpack . filter (not . Text.null) . Text.splitOn ":" . Text.pack $
        fromMaybe "" (lookup "PATH" environment)

data ToolResult
  = Finished !ExitCode !Text !Text
  | TimedOut
  | NotStarted !Text

-- | Run a tool with an argument list (no shell), the given environment and
-- working directory, an empty standard input, and its own process group;
-- collect its standard output and standard error. A run that has not
-- finished, including closing its output, within the time limit is
-- stopped: its process group is interrupted and the tool terminated.
runTool :: Env -> FilePath -> Int -> FilePath -> [String] -> IO ToolResult
runTool environment work seconds exe args =
  either (NotStarted . ioMessage) id <$> tryIO (withCreateProcess spec supervise)
  where
    spec =
      (proc exe args)
        { cwd = Just work
        , env = Just environment
        , std_in = CreatePipe
        , std_out = CreatePipe
        , std_err = CreatePipe
        , close_fds = True
        , create_group = True
        }
    supervise (Just hin) (Just hout) (Just herr) ph = superviseTool seconds ph hin hout herr
    supervise _ _ _ ph = NotStarted "no pipes to the process" <$ terminateProcess ph

superviseTool :: Int -> ProcessHandle -> Handle -> Handle -> Handle -> IO ToolResult
superviseTool seconds ph hin hout herr = do
  ignoreIO (hClose hin)
  outVar <- newEmptyMVar
  errVar <- newEmptyMVar
  exitVar <- newEmptyMVar
  readers <- traverse (uncurry forkReader) [(hout, outVar), (herr, errVar)]
  -- Waiting happens in its own thread so that the time limit never depends
  -- on interrupting a blocked system call.
  void (forkIO (tryIO (waitForProcess ph) >>= putMVar exitVar))
  let collect = (,,) <$> readMVar exitVar <*> readMVar outVar <*> readMVar errVar
  ( timeout (seconds * 1000000) collect >>= \case
      Just (Right code, out, err) -> pure (Finished code (decodeOutput out) (decodeOutput err))
      Just (Left e, _, _) -> pure (NotStarted (ioMessage e))
      Nothing -> do
        ignoreIO (interruptProcessGroupOf ph)
        ignoreIO (terminateProcess ph)
        TimedOut <$ timeout (2 * 1000000) (readMVar exitVar)
    )
    `finally` traverse_ killThread readers
  where
    forkReader h var = forkIO (tryIO (BS.hGetContents h) >>= putMVar var . fromRight BS.empty)
    decodeOutput = Text.decodeUtf8Lenient

----------------------------------------------------------------------
-- Helpers

driverError :: Text -> GinError
driverError = ginError StDriver

showT :: (Show a) => a -> Text
showT = Text.pack . show

-- | The kind of an I/O error and the system's description of it, without
-- the file name and location that callers already report.
ioMessage :: IOException -> Text
ioMessage e =
  Text.pack (show (ioe_type e))
    <> if null (ioe_description e) then "" else " (" <> Text.pack (ioe_description e) <> ")"

tryIO :: IO a -> IO (Either IOException a)
tryIO = try

ignoreIO :: IO () -> IO ()
ignoreIO act = void (tryIO act)

-- | Catch every exception except asynchronous ones (such as a user
-- interrupt), which keep propagating.
tryNonAsync :: IO a -> IO (Either SomeException a)
tryNonAsync act =
  try act >>= \case
    Left e | isAsync e -> throwIO e
    r -> pure r
  where
    isAsync e = isJust (fromException e :: Maybe SomeAsyncException)

-- | Write a line, with every character that could control the terminal or
-- hide text replaced by @?@ (newlines and tabs are kept), as UTF-8 whatever
-- the locale.
putLine :: Handle -> Text -> IO ()
putLine h t = putText h (t <> "\n")

putText :: Handle -> Text -> IO ()
putText h t = BS.hPut h (Text.encodeUtf8 (Text.map visible t)) >> hFlush h
  where
    visible c
      | c == '\n' || c == '\t' = c
      | generalCategory c `elem` hidden = '?'
      | otherwise = c
    hidden =
      [Control, Format, LineSeparator, ParagraphSeparator, Surrogate, PrivateUse, NotAssigned]
