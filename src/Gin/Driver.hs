-- | Runs the compiler pipeline and implements the CLI commands.
--
-- > gin check     FILE.gin.json [--allow-axiom NAME]...
-- > gin compile   FILE.gin.json [--target T]... [-o DIR] [--allow-axiom NAME]...
-- > gin testbench FILE.gin.json --vectors V.json [--target T]... [-o DIR] [--allow-axiom NAME]...
-- > gin sim       FILE.gin.json --vectors V.json [--allow-axiom NAME]...
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
-- Exit status: 0 on success, 1 when a check or compile fails
-- (errors are printed with 'renderError', so a certificate error starts
-- with @certificate error:@), 2 on a usage error.
--
-- Text that comes from input files is printed with control and other
-- invisible characters replaced by @?@, so a file cannot drive the
-- terminal.
module Gin.Driver
  ( runCli
  , runCliWith
  ) where

import Control.Applicative (many, optional, (<**>))
import Control.Exception
  ( IOException
  , SomeAsyncException
  , SomeException
  , bracketOnError
  , displayException
  , evaluate
  , fromException
  , throwIO
  , try
  )
import Control.Monad (unless, void, when)
import Control.Monad.Except (ExceptT, liftEither, runExceptT, throwError)
import Control.Monad.IO.Class (liftIO)
import Data.ByteString qualified as BS
import Data.ByteString.Lazy qualified as LBS
import Data.Char (GeneralCategory (..), generalCategory)
import Data.Containers.ListUtils (nubOrd)
import Data.Foldable (for_)
import Data.Maybe (fromMaybe, isJust, listToMaybe)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Text.Encoding qualified as Text
import GHC.IO.Exception (IOException (..))
import Gin.Backend.SystemVerilog (systemVerilog)
import Gin.Backend.Types (Backend (..), Target (..), parseTarget)
import Gin.Backend.VHDL (vhdl)
import Gin.Backend.Verilog (verilog)
import Gin.Certificate (CertPolicy (..), checkCertificate, defaultPolicy)
import Gin.Core.Check (checkProgram)
import Gin.Core.Json (decodeProgram, decodeVectors)
import Gin.Core.Normal (NModule)
import Gin.Core.Syntax (Port (..), Program (..), TopEntity (..), Ty (..), Value (..))
import Gin.Error (GinError (..), Stage (..), ginError, renderError, withContext)
import Gin.Limits (maxInputBytes)
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
  , showHelpOnEmpty
  , strArgument
  , strOption
  )
import System.Directory (createDirectoryIfMissing, doesDirectoryExist, removeFile, renameFile)
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
runCliWith _environment args =
  case execParserPure (prefs showHelpOnEmpty) cliInfo args of
    Success cmd -> runCommand cmd
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

-- | One parsed command line.
data Command
  = CheckCmd !Inputs
  | CompileCmd !Inputs !Outputs
  | TestbenchCmd !Inputs !FilePath !Outputs
  | SimCmd !Inputs !FilePath

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

cliInfo :: ParserInfo Command
cliInfo =
  info (commands <**> helper) $
    fullDesc
      <> header "gin - compile proof-carrying Lean 4 circuits to Verilog, SystemVerilog and VHDL"
      <> progDesc "Check, compile, simulate and validate a circuit exported by the Lean side."
      <> footer
        "Exit status: 0 on success, 1 when a check or compile fails, 2 on a usage error."

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

targetReader :: ReadM Target
targetReader = eitherReader $ \s ->
  maybe
    (Left ("unknown target " <> show s <> "; expected verilog, systemverilog or vhdl"))
    Right
    (parseTarget (Text.pack s))

----------------------------------------------------------------------
-- Commands

-- | Stage errors abort a command; check outcomes do not.
type Pipe = ExceptT GinError IO

runCommand :: Command -> IO ExitCode
runCommand cmd =
  tryNonAsync (runExceptT (execute cmd)) >>= \case
    Right (Right True) -> pure ExitSuccess
    Right (Right False) -> pure (ExitFailure 1)
    Right (Left e) -> ExitFailure 1 <$ putLine stderr (renderError e)
    Left ex ->
      ExitFailure 1
        <$ ignoreIO (putLine stderr (renderError (driverError (Text.pack (displayException ex)))))

-- | Run a command; 'False' when one of its checks failed.
execute :: Command -> Pipe Bool
execute = \case
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
