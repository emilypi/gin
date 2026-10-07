-- | Tests for the VHDL-2008 backend. They answer the README's third
-- question for VHDL: does the generated hardware still implement the
-- functionality described by Lean?
--
-- Design files are compared against golden files under @test/golden/vhdl@
-- and analysed with nvc; testbenches are simulated with nvc and must print
-- @GIN-PASS@ on standard output for correct vectors and @GIN-MISMATCH@ /
-- @GIN-FAIL@ for corrupted ones. Expected outputs of generated vector sets
-- come from 'evalModule', a small reference evaluator written directly from
-- @docs/semantics.md@ and independent of the backend.
module Gin.Backend.VHDLSpec (spec) where

import Control.Exception (evaluate)
import Control.Monad (unless)
import Data.Bits (shiftR, xor, (.&.), (.|.))
import Data.ByteString qualified as ByteString
import Data.Char (GeneralCategory (..), generalCategory, isAlpha, isAlphaNum, toLower)
import Data.List (mapAccumL, unfoldr)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe (mapMaybe)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Text.Encoding qualified as Text
import Data.Text.Read qualified as TextRead
import Gin.Backend.Types (Backend (..), Target (..), failMarker, mismatchMarker, passMarker)
import Gin.Backend.VHDL (vhdl)
import Gin.Core.Syntax (Port (..), Ty (..), Value (..))
import Gin.Examples
  ( counterNetlist
  , counterVectors
  , detectorNetlist
  , detectorVectors
  , macNetlist
  , macVectors
  )
import Gin.Limits (maxNormalBinds, maxVectorBits)
import Gin.Netlist.BuildSpec (withSpecCounter)
import Gin.Netlist.Types
import Gin.TestUtil (goldenText, itWithTools, runTool, withTempDir)
import Gin.Vectors (Cycle (..), Vectors (..))
import Numeric (showHex)
import Numeric.Natural (Natural)
import System.Exit (ExitCode (..))
import System.FilePath ((</>))
import System.Timeout (timeout)
import Test.Hspec

spec :: Spec
spec = do
  describe "backend record" $
    it "targets VHDL and writes .vhd files" $ do
      backendTarget vhdl `shouldBe` VHDL
      backendFileExt vhdl `shouldBe` "vhd"

  describe "design files" $ do
    for_ fixtures $ \(name, m, _) ->
      it ("[vhd-golden] " <> name <> " matches test/golden/vhdl/" <> name <> ".vhd") $
        goldenText ("vhdl/" <> name <> ".vhd") (backendRender vhdl m)
    it "[vhd-golden] the operator coverage netlist matches test/golden/vhdl/coverage.vhd" $
      goldenText "vhdl/coverage.vhd" (backendRender vhdl coverageNetlist)
    for_ fixtures $ \(name, m, _) ->
      itWithTools ["nvc"] ("[vhd-analyze] " <> name <> " passes nvc analysis with no diagnostics") $
        analyze m >>= shouldAnalyze
    it "emits every header line as a comment before the context clause" $ do
      let ls = Text.lines (backendRender vhdl counterNetlist)
      takeWhile ("--" `Text.isPrefixOf`) ls `shouldBe` fmap ("-- " <>) (modHeader counterNetlist)
      drop (length (modHeader counterNetlist)) ls `shouldStartWith` ["library ieee;"]
    it "keeps header text containing line breaks and control characters inside comments" $ do
      let out = backendRender vhdl hostileHeader
          (comments, rest) = span ("--" `Text.isPrefixOf`) (Text.lines out)
      length comments `shouldBe` 13
      take 1 rest `shouldBe` ["library ieee;"]
      Text.filter isSuspicious out `shouldBe` ""
      comments `shouldContain` ["-- unicode stays: \8704 x, f x = g x"]
    itWithTools ["nvc"] "[vhd-analyze] a design with a hostile header passes nvc analysis" $
      analyze hostileHeader >>= shouldAnalyze
    it "[nl-header-spec] the built counter with spec definitions matches its golden file" $
      withSpecCounter (goldenText "vhdl/counter_spec.vhd" . backendRender vhdl)
    it "[nl-header-spec] emits every header line, spec lines and hash included, as a comment" $
      withSpecCounter $ \m -> do
        let ls = Text.lines (backendRender vhdl m)
        filter ("-- spec" `Text.isPrefixOf`) ls `shouldSatisfy` ((> 2) . length)
        take (length (modHeader m)) ls `shouldBe` fmap ("-- " <>) (modHeader m)
    itWithTools ["nvc"] "[nl-header-spec] the counter with spec definitions analyzes and passes" $
      withSpecCounter $ \m -> do
        analyze m >>= shouldAnalyze
        simulate m counterVectors >>= shouldPassCycles (length (vecCycles counterVectors))
    it "qualifies every constant and never calls to_unsigned" $
      for_ allDesigns $ \m -> do
        let src = backendRender vhdl m
        unqualifiedLiterals src `shouldBe` []
        "to_unsigned" `Text.isInfixOf` src `shouldBe` False
    it "references only nets, gin_ names and reserved predeclared names" $
      for_ allDesigns $ \m -> do
        unexpectedIdentifiers m (backendRender vhdl m) `shouldBe` Set.empty
        unexpectedIdentifiers m (backendTestbench vhdl m (vectorsFor m (inputRows 1 2 m)))
          `shouldBe` Set.empty
    it "folds a slice of a constant instead of slicing a literal" $
      backendRender vhdl constantSlice
        `shouldSatisfy` Text.isInfixOf "s <= unsigned'(\"1101\");"

  describe "testbenches" $ do
    for_ fixtures $ \(name, m, vs) ->
      it ("[vhd-golden] " <> name <> " matches test/golden/vhdl/" <> name <> "_tb.vhd") $
        goldenText ("vhdl/" <> name <> "_tb.vhd") (backendTestbench vhdl m vs)
    for_ fixtures $ \(name, m, vs) ->
      itWithTools ["nvc"] ("[vhd-tb-pass] " <> name <> " prints GIN-PASS on stdout only") $
        simulate m vs >>= shouldPassCycles (length (vecCycles vs))
    itWithTools ["nvc"] "[vhd-tb-fail] a corrupted counter value is reported on stdout" $
      simulate counterNetlist (corrupt 7 0 counterVectors)
        >>= shouldReportOnly
          ["GIN-MISMATCH cycle=7 port=count expected=05 got=04", "GIN-FAIL mismatches=1"]
    itWithTools ["nvc"] "[vhd-tb-fail] a corrupted detector bit is reported on stdout" $
      simulate detectorNetlist (corrupt 2 0 detectorVectors)
        >>= shouldReportOnly
          ["GIN-MISMATCH cycle=2 port=hit expected=0 got=1", "GIN-FAIL mismatches=1"]
    itWithTools ["nvc"] "[vhd-tb-fail] every corrupted mac cycle is counted" $
      simulate macNetlist (corrupt 4 0 (corrupt 0 0 macVectors))
        >>= shouldReportOnly
          [ "GIN-MISMATCH cycle=0 port=acc expected=0001 got=0000"
          , "GIN-MISMATCH cycle=4 port=acc expected=FC2D got=FC2C"
          , "GIN-FAIL mismatches=2"
          ]
    itWithTools ["nvc"] "an empty vector set resets the design and passes with cycles=0" $
      simulate counterNetlist counterVectors {vecCycles = []} >>= shouldPassCycles 0
    itWithTools ["nvc"] "a port named like the testbench entity does not clash with it" $
      checkRun tbNamedPort (vectorsFor tbNamedPort (inputRows 31 8 tbNamedPort))
    it "renders vectors that violate the port precondition without throwing" $ do
      n <- evaluate (Text.length (backendTestbench vhdl counterNetlist macVectors))
      n `shouldSatisfy` (> 0)
    it "[backend-minors] reports nothing extra for well-formed vectors" $
      for_ fixtures $ \(_, m, vs) ->
        backendTestbench vhdl m vs `shouldNotSatisfy` Text.isInfixOf "malformed"
    itWithTools ["nvc"] "[backend-minors] an extra input value in a row counts as a mismatch" $ do
      let bad = editRow 2 (\c -> c {cycInputs = cycInputs c <> [VBool True]}) counterVectors
      simulate counterNetlist bad
        >>= shouldReportOnly
          ["GIN-MISMATCH malformed-values=1 first-cycle=2", "GIN-FAIL mismatches=1"]
    itWithTools ["nvc"] "[backend-minors] an ill-typed value of an unread input is a mismatch" $ do
      let vs = vectorsFor idleInputNetlist (inputRows 41 6 idleInputNetlist)
          bad = editRow 4 (\c -> c {cycInputs = take 1 (cycInputs c) <> [VBool True]}) vs
      checkRun idleInputNetlist vs
      simulate idleInputNetlist bad
        >>= shouldReportOnly
          ["GIN-MISMATCH malformed-values=1 first-cycle=4", "GIN-FAIL mismatches=1"]
    itWithTools ["nvc"] "[backend-minors] missing and extra expected values are mismatches" $ do
      let bad =
            editRow 6 (\c -> c {cycOutputs = cycOutputs c <> [VBV 8 0]}) $
              editRow 3 (\c -> c {cycOutputs = []}) counterVectors
      simulate counterNetlist bad
        >>= shouldReportOnly
          [ "GIN-MISMATCH malformed-values=2 first-cycle=3"
          , "GIN-MISMATCH cycle=3 port=count expected=00 got=02"
          , "GIN-FAIL mismatches=3"
          ]

  describe "operators" $ do
    it "the reference evaluator reproduces the hand-written fixture vectors" $
      for_ fixtures $ \(_, m, vs) ->
        vectorsFor m (fmap cycInputs (vecCycles vs)) `shouldBe` vs
    it "[o0-fast] the test netlists satisfy the netlist identifier and reference invariants" $
      withinSeconds 60 . for_ (allDesigns <> largeDesigns) $ \m ->
        invariantViolations m `shouldBe` []
    itWithTools ["nvc"] "[vhd-coverage] every operator with constants in every position analyzes" $
      analyze coverageNetlist >>= shouldAnalyze
    itWithTools ["nvc"] "[vhd-coverage] every operator with constants in every position simulates" $
      checkRun coverageNetlist (vectorsFor coverageNetlist (inputRows 7 64 coverageNetlist))

  describe "widths" $ do
    itWithTools ["nvc"] "[vhd-wide] 4096-bit ports, operators and literals analyze and pass" $ do
      let vs = vectorsFor wideNetlist (inputRows 11 6 wideNetlist)
      payloadBits vs `shouldSatisfy` (<= maxVectorBits)
      analyze wideNetlist >>= shouldAnalyze
      checkRun wideNetlist vs
    itWithTools ["nvc"] "[vhd-wide] literals wider than 32 bits analyze and pass" $ do
      analyze literalNetlist >>= shouldAnalyze
      checkRun literalNetlist (vectorsFor literalNetlist (inputRows 13 32 literalNetlist))
    itWithTools ["nvc"] "[vhd-wide] width-1 vectors analyze and pass" $ do
      analyze narrowNetlist >>= shouldAnalyze
      checkRun narrowNetlist (vectorsFor narrowNetlist (inputRows 17 32 narrowNetlist))

  describe "combinational depth and variable storage" $ do
    it "computes every combinational net once and reads no variable before assigning it" $
      for_ (allDesigns <> [shallowDag, windowNetlist]) $ \m -> do
        let src = backendRender vhdl m
        readsBeforeAssigned src `shouldBe` []
        sum (processSizes src) `shouldBe` length [() | DAssign {} <- modDecls m]
    it "splits deep logic into processes of at most 1000 nets each" $ do
      let sizes = processSizes (backendRender vhdl (chainNetlist 8 12000))
      sizes `shouldBe` replicate 12 1000
    it "reads a net from a variable up to 127 nets later in a 4096-bit process, one of 16" $ do
      let stmts = concatMap snd (combinationalProcesses (backendRender vhdl windowNetlist))
      stmts `shouldContain` ["gin_v127 := gin_v126 + gin_v0;"]
      stmts `shouldContain` ["gin_v0 := gin_v127 - x;"]
      stmts `shouldContain` ["gin_v1 := gin_v0 xor x;", "w <= gin_v1;"]
    it "keeps narrower nets and bits in the low elements of wider variables" $ do
      let stmts = concatMap snd (combinationalProcesses (backendRender vhdl windowNetlist))
      stmts `shouldContain` ["gin_v2(7 downto 0) := gin_v1(7 downto 0);"]
      let less = "gin_v3(0) := std_logic'('1') when gin_v2(7 downto 0) < b"
      stmts `shouldContain` [less <> " else std_logic'('0');", "g <= gin_v3(0);"]
      stmts `shouldContain` ["gin_v6(3 downto 0) := gin_v4(5 downto 2);"]
    itWithTools ["nvc"] "nets sharing a variable keep their values until their last read from it" $
      checkRunRows 24 windowNetlist
    it "keeps the variables of every design within 8 MiB, 16 MiB being nvc's heap" $
      for_ (allDesigns <> largeDesigns) $ \m -> do
        let perProcess = processVariables (backendRender vhdl m)
        sum (fmap sum perProcess) `shouldSatisfy` (<= 2 ^ (23 :: Int))
        perProcess `shouldSatisfy` all (all (<= 4096))
    it "gives each process of the largest 4096-bit design 31 variables" $ do
      let perProcess = processVariables (backendRender vhdl (chainNetlist 4096 65535))
      fmap length perProcess `shouldBe` replicate 66 31
    itWithTools ["nvc"] "a chain of 5000 nets of 4096 bits passes (nvc's heap is 16 MiB)" $
      checkRunRows 4 (chainNetlist 4096 5000)
    itWithTools ["nvc"] "a layered DAG of 20000 nets of 4096 bits passes" $
      checkRunRows 4 shallowDag
    itWithTools ["nvc"] "a chain keeps its variables while values read much later are pending" $
      checkRunRows 4 crowdedNetlist
    itWithTools ["nvc"] "a chain of 12000 nets of 2048 bits (past 10000 delta cycles) passes" $
      checkRunRows 4 (chainNetlist 2048 12000)
    itWithTools ["nvc"] "a chain of 65535 nets of 4096 bits, the deepest and widest, passes" $ do
      let deepest = chainNetlist 4096 65535
      length (modDecls deepest) `shouldBe` maxNormalBinds
      checkRunRows 4 deepest
    it "reads every net of a narrow design from a variable within its process" $
      for_ [interleavedNetlist, chainNetlist 8 12000] $ \m ->
        signalReads m (backendRender vhdl m) `shouldBe` []
    it "[vhd-waterfill] shares variables by need: lanes beside a narrow chain read no signal" $ do
      let src = backendRender vhdl lanesNetlist
      length (combinationalProcesses src) `shouldBe` 66
      length (modDecls lanesNetlist) `shouldSatisfy` (<= maxNormalBinds)
      combinationalBits lanesNetlist `shouldSatisfy` (<= 2 ^ (23 :: Int))
      -- an equal share of 2^23 elements between 66 processes holds 31 nets
      -- of 4096 bits, one fewer than a lane step reaches back
      (2 ^ (23 :: Int) `div` 66 :: Int) `shouldSatisfy` (< 32 * 4096)
      signalReads lanesNetlist src `shouldBe` []
    itWithTools ["nvc"] "[vhd-waterfill] wide lanes beside a 63112-net chain pass under nvc" $ do
      length (modDecls lanesNetlist) `shouldBe` 65002
      checkRunRows 8 lanesNetlist
    itWithTools ["nvc"] "16 interleaved chains of 8-bit nets in 66 processes pass" $ do
      length (modDecls interleavedNetlist) `shouldBe` maxNormalBinds
      checkRunRows 4 interleavedNetlist

  describe "long vector sets" $ do
    itWithTools ["nvc"] "[vhd-long] a 25000-cycle counter run passes" $ do
      payloadBits longVectors `shouldSatisfy` (<= maxVectorBits)
      checkRun counterNetlist longVectors
    itWithTools ["nvc"] "[vhd-long] a corrupted final cycle of 25000 is still checked" $ do
      let bad = corrupt 24999 0 longVectors
          expected = showValue (lastOutput bad)
          got = showValue (lastOutput longVectors)
      simulate counterNetlist bad
        >>= shouldReportOnly
          [ "GIN-MISMATCH cycle=24999 port=count expected=" <> expected <> " got=" <> got
          , "GIN-FAIL mismatches=1"
          ]

  describe "unused ports" $ do
    itWithTools ["nvc"] "[vhd-unused] a register-free module analyzes and passes" $ do
      analyze combNetlist >>= shouldAnalyze
      checkRun combNetlist (vectorsFor combNetlist (inputRows 19 16 combNetlist))
    itWithTools ["nvc"] "[vhd-unused] a module with an unread input analyzes and passes" $ do
      analyze idleInputNetlist >>= shouldAnalyze
      checkRun idleInputNetlist (vectorsFor idleInputNetlist (inputRows 23 16 idleInputNetlist))
    itWithTools ["nvc"] "a module without inputs analyzes and passes" $ do
      analyze freeRunNetlist >>= shouldAnalyze
      checkRun freeRunNetlist (vectorsFor freeRunNetlist (replicate 20 []))
  where
    for_ xs f = mapM_ f xs

----------------------------------------------------------------------
-- Running nvc (the analysis and run commands of the VHDL backend)

nvcFlags :: [String]
nvcFlags = ["-M", "1g", "--std=2008"]

designFile, testbenchFile :: Module -> FilePath
designFile m = Text.unpack (unIdent (modName m)) <> "." <> backendFileExt vhdl
testbenchFile m = Text.unpack (unIdent (modName m)) <> "_tb." <> backendFileExt vhdl

writeUtf8 :: FilePath -> Text -> IO ()
writeUtf8 path = ByteString.writeFile path . Text.encodeUtf8

type ToolResult = (ExitCode, Text, Text)

-- | Analyse the design file alone.
analyze :: Module -> IO ToolResult
analyze m = withTempDir $ \dir -> do
  writeUtf8 (dir </> designFile m) (backendRender vhdl m)
  runTool dir "nvc" (nvcFlags <> ["-a", designFile m])

-- | Analyse design and testbench, elaborate the testbench and run it.
simulate :: Module -> Vectors -> IO ToolResult
simulate m vs = withTempDir $ \dir -> do
  writeUtf8 (dir </> designFile m) (backendRender vhdl m)
  writeUtf8 (dir </> testbenchFile m) (backendTestbench vhdl m vs)
  runTool
    dir
    "nvc"
    (nvcFlags <> ["-a", designFile m, testbenchFile m, "-e", tbName, "-r"])
  where
    tbName = Text.unpack (unIdent (modName m)) <> "_tb"

checkRun :: Module -> Vectors -> Expectation
checkRun m vs = simulate m vs >>= shouldPassCycles (length (vecCycles vs))

-- | 'checkRun' with @n@ generated input rows, within the vector payload limit.
checkRunRows :: Int -> Module -> Expectation
checkRunRows n m = do
  let vs = vectorsFor m (inputRows 37 n m)
  payloadBits vs `shouldSatisfy` (<= maxVectorBits)
  checkRun m vs

-- | Fail instead of running on when a check takes longer than the given
-- number of seconds. The pure checks over the largest test netlists take
-- a few seconds even when built without optimization.
withinSeconds :: Int -> Expectation -> Expectation
withinSeconds seconds check =
  timeout (seconds * 1000000) check
    >>= maybe (expectationFailure ("took more than " <> show seconds <> " s")) pure

-- | Lines carrying a testbench protocol marker.
markerLines :: Text -> [Text]
markerLines = filter hasMarker . Text.lines
  where
    hasMarker l = any (`Text.isInfixOf` l) [passMarker, failMarker, mismatchMarker]

describeRun :: String -> ToolResult -> String
describeRun what (code, out, err) =
  unlines
    [ what
    , "exit: " <> show code
    , "stdout:"
    , Text.unpack (Text.take 3000 out)
    , "stderr:"
    , Text.unpack (Text.take 3000 err)
    ]

-- | Exit 0 and nothing at all on standard error.
shouldAnalyze :: ToolResult -> Expectation
shouldAnalyze r@(code, _, err) =
  unless (code == ExitSuccess && Text.null (Text.strip err)) $
    expectationFailure (describeRun "nvc analysis failed" r)

-- | The pass criterion of @docs/semantics.md@: exit 0, exactly one marker
-- line on standard output and it is the pass line for @n@ cycles; no
-- marker on standard error.
shouldPassCycles :: Int -> ToolResult -> Expectation
shouldPassCycles n r@(code, out, err) =
  unless ok $ expectationFailure (describeRun ("expected " <> Text.unpack passLine) r)
  where
    passLine = passMarker <> " cycles=" <> Text.pack (show n)
    ok = code == ExitSuccess && markerLines out == [passLine] && null (markerLines err)

-- | Exactly these marker lines on standard output (case-insensitively, as
-- the hex digits may be either case) and none on standard error.
shouldReportOnly :: [Text] -> ToolResult -> Expectation
shouldReportOnly expected r@(_, out, err) =
  unless ok $ expectationFailure (describeRun ("expected " <> show expected) r)
  where
    ok =
      fmap Text.toLower (markerLines out) == fmap Text.toLower expected
        && null (markerLines err)

----------------------------------------------------------------------
-- Source-level checks

-- | Characters that must never reach a generated file: controls other than
-- the newline, format characters (bidirectional overrides) and line or
-- paragraph separators.
isSuspicious :: Char -> Bool
isSuspicious c =
  c /= '\n' && generalCategory c `elem` [Control, Format, LineSeparator, ParagraphSeparator]

-- | Lines of source outside full-line comments.
codeLines :: Text -> [Text]
codeLines = filter (not . ("--" `Text.isPrefixOf`) . Text.stripStart) . Text.lines

-- | Bit literals not written as @std_logic'('b')@ and string literals not
-- written as @unsigned'("bits")@.
unqualifiedLiterals :: Text -> [Text]
unqualifiedLiterals src = concatMap check (codeLines src)
  where
    check l =
      [l | (prefix, _) <- Text.breakOnAll "'0'" l <> Text.breakOnAll "'1'" l, not (bitOk prefix)]
        <> [l | outside <- stringPrefixes l, not ("unsigned'(" `Text.isSuffixOf` outside)]
    bitOk prefix = "std_logic'(" `Text.isSuffixOf` prefix
    -- the text before each string literal on the line
    stringPrefixes l = everyOther (Text.splitOn "\"" l)
    everyOther = \case
      outside : _ : rest@(_ : _) -> outside : everyOther rest
      _ -> []

-- | The combinational processes, each as its declarations and its
-- statements (stripped lines).
combinationalProcesses :: Text -> [([Text], [Text])]
combinationalProcesses = go . fmap Text.strip . codeLines
  where
    go ls = case break (== "process (all)") ls of
      (_, _ : rest) ->
        let (decls, body) = break (== "begin") rest
            (stmts, remaining) = break (== "end process;") (drop 1 body)
         in (decls, stmts) : go remaining
      (_, []) -> []

-- | Statements that read a variable not assigned on an earlier line of the
-- same process. Variables keep their values between activations of a
-- process, so such a read would see a stale value.
readsBeforeAssigned :: Text -> [Text]
readsBeforeAssigned src = concatMap (check Set.empty . snd) (combinationalProcesses src)
  where
    check _ [] = []
    check assigned (l : ls) = case Text.breakOn " := " l of
      (lhs, rhs)
        | not (Text.null rhs) ->
            [l | any (`Set.notMember` assigned) (variables rhs)]
              <> check (Set.insert (Text.takeWhile isWordChar lhs) assigned) ls
        | otherwise -> [l | any (`Set.notMember` assigned) (variables l)] <> check assigned ls
    variables = filter ("gin_v" `Text.isPrefixOf`) . Text.split (not . isWordChar)
    isWordChar c = isAlphaNum c || c == '_'

-- | The number of nets each process computes: its statements other than
-- copies into a signal of the variable assigned on the line before. No test
-- netlist has a net that merely forwards the net computed just before it,
-- which would look like such a copy.
processSizes :: Text -> [Int]
processSizes src = [length stmts - copies stmts | (_, stmts) <- combinationalProcesses src]
  where
    copies stmts = length (filter isCopy (zip stmts (drop 1 stmts)))
    isCopy (prev, l) = case (Text.breakOn " := " prev, Text.breakOn " <= " l) of
      ((lhs, rhs), (_, copied)) ->
        not (Text.null rhs) && Text.drop 4 copied == lhs <> ";"

-- | The elements (bits) of each variable each process declares.
processVariables :: Text -> [[Int]]
processVariables src = [mapMaybe elements decls | (decls, _) <- combinationalProcesses src]
  where
    elements l
      | "variable " `Text.isPrefixOf` l && " : std_logic;" `Text.isSuffixOf` l = Just 1
      | "variable " `Text.isPrefixOf` l =
          case Text.breakOn "unsigned(" l of
            (_, rest) -> case TextRead.decimal (Text.drop 9 rest) of
              Right (hi, _) -> Just (hi + 1)
              Left _ -> Nothing
      | otherwise = Nothing

-- | Statements of a combinational process that read a combinational net
-- the same process computes through its signal.
signalReads :: Module -> Text -> [Text]
signalReads m src = concatMap check (combinationalProcesses src)
  where
    combinationalNets = Set.fromList [unIdent (netName n) | DAssign n _ <- modDecls m]
    check (_, stmts) =
      let computed = Set.fromList (mapMaybe target stmts) `Set.intersection` combinationalNets
       in [l | l <- stmts, any (`Set.member` computed) (readNames l)]
    target l = case Text.breakOn " <= " l of
      (lhs, rhs) | not (Text.null rhs) -> Just lhs
      _ -> Nothing
    readNames l = case Text.breakOn " <= " l of
      (_, rhs) | not (Text.null rhs) -> names (Text.drop 4 rhs)
      _ -> names (snd (Text.breakOn " := " l))
    names = Text.split (not . isWordChar)
    isWordChar c = isAlphaNum c || c == '_'

-- | Identifiers outside comments and string literals that are neither nets,
-- ports, the module or testbench name, @gin_@ names, nor in 'reservedWords'.
unexpectedIdentifiers :: Module -> Text -> Set Text
unexpectedIdentifiers m src =
  Set.filter (not . allowed) (Set.fromList (concatMap idents (codeLines src)))
  where
    known =
      Set.fromList . fmap unIdent $
        [modName m, modClock m, modReset m]
          <> fmap netName (modInputs m <> fmap outNet (modOutputs m) <> fmap declNet (modDecls m))
    allowed i =
      i `Set.member` known
        || i `Set.member` reservedWords
        || i == unIdent (modName m) <> "_tb"
        || "gin_" `Text.isPrefixOf` i
    idents l = [Text.toLower w | w <- Text.split (not . isWordChar) (dropStrings l), startsAlpha w]
    dropStrings = Text.concat . everyOther . Text.splitOn "\""
    everyOther = \case
      outside : _ : rest -> outside : everyOther rest
      rest -> rest
    isWordChar c = isAlphaNum c || c == '_'
    startsAlpha w = maybe False (isAlpha . fst) (Text.uncons w)

-- | Identifier legality, case-insensitive distinctness, resolvable
-- references and every declared net read (invariants 1, 2, 3 and 8).
invariantViolations :: Module -> [String]
invariantViolations m =
  [ "illegal identifier " <> show i | i <- idents, not (isLegalIdent (unIdent i))]
    <> ["duplicate identifiers" | Set.size (Set.fromList lowered) /= length lowered]
    <> ["dangling reference " <> show i | ORef i <- operands, i `Map.notMember` nets]
    <> [ "unread net " <> show n
       | n <- fmap (netName . declNet) (modDecls m)
       , n `Set.notMember` read'
       ]
  where
    -- built once: rebuilding it per reference is quadratic without optimization
    nets = moduleNets m
    idents =
      modName m
        : modClock m
        : modReset m
        : fmap netName (modInputs m <> fmap outNet (modOutputs m) <> fmap declNet (modDecls m))
    lowered = fmap (Text.map toLower . unIdent) idents
    operands = fmap outDriver (modOutputs m) <> concatMap declOperands (modDecls m)
    read' = Set.fromList [i | ORef i <- operands]
    declOperands = \case
      DReg _ _ o -> [o]
      DAssign _ e -> exprOperands e
    exprOperands = \case
      HOperand o -> [o]
      HUn _ o -> [o]
      HBin _ a b -> [a, b]
      HMux c t e -> [c, t, e]
      HShl _ o -> [o]
      HLshr _ o -> [o]
      HSlice _ _ o -> [o]
      HConcat a b -> [a, b]
      HZext _ o -> [o]
      HBitToVec o -> [o]

----------------------------------------------------------------------
-- Reference evaluator (docs/semantics.md)

-- | Output rows of a netlist driven by the given input rows: registers start
-- at their reset values, everything else is combinational within a cycle.
evalModule :: Module -> [[Value]] -> [[Value]]
evalModule m = go (Map.fromList [(netName n, litValue v) | DReg n v _ <- modDecls m])
  where
    go _ [] = []
    go regs (row : rows) =
      let env = Map.unions [Map.fromList (zip (fmap netName (modInputs m)) row), regs, wires]
          wires = Map.fromList [(netName n, evalExpr env e) | DAssign n e <- modDecls m]
          next = Map.fromList [(netName n, operandValue env o) | DReg n _ o <- modDecls m]
       in fmap (operandValue env . outDriver) (modOutputs m) : go next rows

litValue :: HLit -> Value
litValue = \case
  HLitBit b -> VBool b
  HLitVec w x -> VBV w x

operandValue :: Map Ident Value -> Operand -> Value
operandValue env = \case
  ORef i -> Map.findWithDefault (VBool False) i env
  OConst l -> litValue l

-- | Width and payload of a vector value (a bit counts as width 1).
asVec :: Value -> (Natural, Integer)
asVec = \case
  VBV w x -> (w, x)
  VBool b -> (1, if b then 1 else 0)
  VTuple _ -> (0, 0)

asBit :: Value -> Bool
asBit = \case
  VBool b -> b
  VBV _ x -> odd x
  VTuple _ -> False

wrap :: Natural -> Integer -> Value
wrap w x = VBV w (x `mod` (2 ^ w))

evalExpr :: Map Ident Value -> HExpr -> Value
evalExpr env = \case
  HOperand o -> val o
  HUn UNot o -> case val o of
    VBool b -> VBool (not b)
    v -> let (w, x) = asVec v in VBV w (2 ^ w - 1 - x)
  HUn UNeg o -> let (w, x) = asVec (val o) in wrap w (negate x)
  HBin op a b -> evalBin op (val a) (val b)
  HMux c t e -> if asBit (val c) then val t else val e
  HShl k o -> let (w, x) = asVec (val o) in wrap w (x * 2 ^ k)
  HLshr k o -> let (w, x) = asVec (val o) in VBV w (x `div` 2 ^ k)
  HSlice hi lo o -> wrap (hi - lo + 1) (snd (asVec (val o)) `div` 2 ^ lo)
  HConcat a b ->
    let (wa, xa) = asVec (val a)
        (wb, xb) = asVec (val b)
     in VBV (wa + wb) (xa * 2 ^ wb + xb)
  HZext m o -> VBV m (snd (asVec (val o)))
  HBitToVec o -> VBV 1 (if asBit (val o) then 1 else 0)
  where
    val = operandValue env

evalBin :: BinOp -> Value -> Value -> Value
evalBin op a b = case (a, b) of
  (VBool x, VBool y) -> case op of
    BAnd -> VBool (x && y)
    BOr -> VBool (x || y)
    BXor -> VBool (x /= y)
    _ -> VBool (x == y)
  _ ->
    let (w, x) = asVec a
        y = snd (asVec b)
     in case op of
          BAnd -> VBV w (x .&. y)
          BOr -> VBV w (x .|. y)
          BXor -> VBV w (x `xor` y)
          BAdd -> wrap w (x + y)
          BSub -> wrap w (x - y)
          BMul -> wrap w (x * y)
          BEq -> VBool (x == y)
          BUlt -> VBool (x < y)
          BUle -> VBool (x <= y)

----------------------------------------------------------------------
-- Vector sets

hwTy :: HwType -> Ty
hwTy = \case
  HBit -> TBool
  HVec w -> TBitVec w

-- | Vectors for a module: the given input rows and the reference outputs.
vectorsFor :: Module -> [[Value]] -> Vectors
vectorsFor m rows =
  Vectors
    { vecTop = unIdent (modName m)
    , vecInputs = fmap port (modInputs m)
    , vecOutputs = fmap (port . outNet) (modOutputs m)
    , vecCycles = zipWith Cycle rows (evalModule m rows)
    }
  where
    port n = Port (unIdent (netName n)) (hwTy (netType n))

-- | Cycles times the summed port widths.
payloadBits :: Vectors -> Integer
payloadBits vs =
  fromIntegral (length (vecCycles vs))
    * sum [toInteger (width (portTy p)) | p <- vecInputs vs <> vecOutputs vs]
  where
    width = \case
      TBitVec w -> w
      _ -> 1

-- | @n@ deterministic input rows: all zeros, all ones, then pseudo-random
-- values from a 64-bit linear congruential generator seeded with @seed@.
inputRows :: Integer -> Int -> Module -> [[Value]]
inputRows seed n m = take n ([fill 0, fill (-1)] <> unfoldr (Just . swap . row) (lcg seed))
  where
    ins = fmap netType (modInputs m)
    fill x = fmap (`valueOf` x) ins
    row g = mapAccumL (\g' ty -> let (x, g'') = draw ty g' in (g'', valueOf ty x)) g ins
    swap (a, b) = (b, a)

valueOf :: HwType -> Integer -> Value
valueOf ty x = case ty of
  HBit -> VBool (odd x)
  HVec w -> wrap w x

-- | Enough 32-bit words from the stream to fill the type's width.
draw :: HwType -> [Integer] -> (Integer, [Integer])
draw ty g = (foldr (\w acc -> acc * 2 ^ (32 :: Int) + w) 0 ws, rest)
  where
    (ws, rest) = splitAt (fromIntegral ((hwWidth ty + 31) `div` 32)) g

lcg :: Integer -> [Integer]
lcg = fmap (`shiftR` 32) . drop 1 . iterate step
  where
    step x = (6364136223846793005 * x + 1442695040888963407) `mod` 2 ^ (64 :: Int)

-- | Flip the least significant bit of output @j@ in cycle @t@.
corrupt :: Int -> Int -> Vectors -> Vectors
corrupt t j vs = vs {vecCycles = zipWith fix [0 ..] (vecCycles vs)}
  where
    fix i c
      | i == t = c {cycOutputs = zipWith flipAt [0 ..] (cycOutputs c)}
      | otherwise = c
    flipAt k v
      | k == j = flipValue v
      | otherwise = v
    flipValue = \case
      VBool b -> VBool (not b)
      VBV w x -> VBV w (x `xor` 1)
      v -> v

-- | Change cycle @t@ of a vector set.
editRow :: Int -> (Cycle -> Cycle) -> Vectors -> Vectors
editRow t f vs = vs {vecCycles = zipWith edit [0 ..] (vecCycles vs)}
  where
    edit i c = if i == t then f c else c

-- | Bits of all combinational nets together: what their variables would
-- hold if every net had its own.
combinationalBits :: Module -> Int
combinationalBits m = sum [fromIntegral (hwWidth (netType n)) | DAssign n _ <- modDecls m]

-- | Hex digits (one per four bits) for vectors, @0@/@1@ for bits.
showValue :: Value -> Text
showValue = \case
  VBool b -> if b then "1" else "0"
  VBV w x -> Text.justifyRight (fromIntegral ((w + 3) `div` 4)) '0' (Text.pack (showHex x ""))
  VTuple _ -> ""

lastOutput :: Vectors -> Value
lastOutput vs = case reverse (vecCycles vs) of
  Cycle _ (o : _) : _ -> o
  _ -> VBool False

longVectors :: Vectors
longVectors = vectorsFor counterNetlist (inputRows 29 25000 counterNetlist)

----------------------------------------------------------------------
-- Test netlists

fixtures :: [(String, Module, Vectors)]
fixtures =
  [ ("counter", counterNetlist, counterVectors)
  , ("mac", macNetlist, macVectors)
  , ("detector", detectorNetlist, detectorVectors)
  ]

allDesigns :: [Module]
allDesigns =
  [counterNetlist, macNetlist, detectorNetlist]
    <> [coverageNetlist, wideNetlist, literalNetlist, narrowNetlist]
    <> [combNetlist, idleInputNetlist, freeRunNetlist, tbNamedPort, chainNetlist 8 40]
    <> [layeredNetlist 8 6 4]

-- | The netlists of the depth and variable storage tests.
largeDesigns :: [Module]
largeDesigns =
  [ chainNetlist 4096 5000
  , shallowDag
  , crowdedNetlist
  , chainNetlist 2048 12000
  , chainNetlist 4096 65535
  , interleavedNetlist
  , windowNetlist
  , lanesNetlist
  ]

ref :: Text -> Operand
ref = ORef . Ident

kvec :: Natural -> Integer -> Operand
kvec w = OConst . HLitVec w

kbit :: Bool -> Operand
kbit = OConst . HLitBit

net :: Text -> HwType -> Net
net = Net . Ident

assign :: Text -> HwType -> HExpr -> Decl
assign n ty = DAssign (net n ty)

register :: Text -> HwType -> HLit -> Operand -> Decl
register n ty = DReg (net n ty)

-- | A module in which every declared net also drives an output @o_<net>@,
-- so every operator's result is compared in every cycle.
observed :: Text -> [Net] -> [Decl] -> Module
observed name ins decls =
  Module
    { modName = Ident name
    , modHeader = ["generated by the gin test suite"]
    , modClock = Ident "clk"
    , modReset = Ident "rst"
    , modInputs = ins
    , modOutputs =
        [ Output (net ("o_" <> unIdent (netName n)) (netType n)) (ORef (netName n))
        | n <- fmap declNet decls
        ]
    , modDecls = decls
    }

opName :: BinOp -> Text
opName = \case
  BAnd -> "and"
  BOr -> "or"
  BXor -> "xor"
  BAdd -> "add"
  BSub -> "sub"
  BMul -> "mul"
  BEq -> "eq"
  BUlt -> "ult"
  BUle -> "ule"

binResult :: BinOp -> HwType -> HwType
binResult op ty
  | op `elem` [BEq, BUlt, BUle] = HBit
  | otherwise = ty

-- | Operand positions: both references, constant left, constant right, both
-- constants.
positions :: Operand -> Operand -> Operand -> Operand -> [(Text, Operand, Operand)]
positions x y kx ky = [("rr", x, y), ("kr", kx, y), ("rk", x, ky), ("kk", kx, ky)]

-- | Every 'HExpr', 'UnOp' and 'BinOp' constructor, on bits and vectors, with
-- a constant in every operand position the netlist invariants allow, plus
-- registers with reference and constant next values. Outputs driven by a
-- constant and by an input directly are added as well.
coverageNetlist :: Module
coverageNetlist =
  base {modOutputs = modOutputs base <> extra}
  where
    base = observed "coverage" ins (unary <> binary <> muxes <> shifts <> structural <> registers)
    extra = [Output (net "o_const" v8) k8, Output (net "o_input" HBit) (ref "q")]
    ins = [net "a" v8, net "b" v8, net "c" (HVec 5), net "p" HBit, net "q" HBit]
    v8 = HVec 8
    k8 = kvec 8 0xA5
    k8' = kvec 8 0x3C
    unary =
      [ assign "pass_ref" v8 (HOperand (ref "a"))
      , assign "pass_vec" v8 (HOperand k8)
      , assign "pass_bit" HBit (HOperand (kbit True))
      , assign "not_bit_r" HBit (HUn UNot (ref "p"))
      , assign "not_bit_k" HBit (HUn UNot (kbit False))
      , assign "not_vec_r" v8 (HUn UNot (ref "a"))
      , assign "not_vec_k" v8 (HUn UNot k8)
      , assign "neg_vec_r" v8 (HUn UNeg (ref "a"))
      , assign "neg_vec_k" v8 (HUn UNeg k8)
      , assign "neg_odd_r" (HVec 5) (HUn UNeg (ref "c"))
      ]
    binary =
      [ assign (opName op <> "_bit_" <> pos) HBit (HBin op x y)
      | op <- [BAnd, BOr, BXor, BEq]
      , (pos, x, y) <- positions (ref "p") (ref "q") (kbit True) (kbit False)
      ]
        <> [ assign (opName op <> "_vec_" <> pos) (binResult op v8) (HBin op x y)
           | op <- [minBound .. maxBound]
           , (pos, x, y) <- positions (ref "a") (ref "b") k8 k8'
           ]
        <> [ assign (opName op <> "_odd") (binResult op (HVec 5)) (HBin op (ref "c") (kvec 5 0x13))
           | op <- [BAdd, BSub, BMul, BUlt, BUle]
           ]
    muxes =
      [ assign "mux_vec_rrr" v8 (HMux (ref "p") (ref "a") (ref "b"))
      , assign "mux_vec_krr" v8 (HMux (kbit True) (ref "a") (ref "b"))
      , assign "mux_vec_rkr" v8 (HMux (ref "p") k8 (ref "b"))
      , assign "mux_vec_rrk" v8 (HMux (ref "p") (ref "a") k8)
      , assign "mux_vec_kkk" v8 (HMux (kbit False) k8 k8')
      , assign "mux_bit_rrr" HBit (HMux (ref "p") (ref "q") (ref "not_bit_r"))
      , assign "mux_bit_rkk" HBit (HMux (ref "q") (kbit True) (kbit False))
      , assign "mux_bit_kkr" HBit (HMux (kbit True) (kbit False) (ref "p"))
      ]
    shifts =
      [assign ("shl_" <> tshow k) v8 (HShl k (ref "a")) | k <- [0, 3, 7]]
        <> [assign ("lshr_" <> tshow k) v8 (HLshr k (ref "a")) | k <- [0, 3, 7]]
        <> [assign "shl_k" v8 (HShl 2 k8), assign "lshr_k" v8 (HLshr 2 k8)]
    structural =
      [ assign "slice_all" v8 (HSlice 7 0 (ref "a"))
      , assign "slice_bit" (HVec 1) (HSlice 3 3 (ref "a"))
      , assign "slice_mid" (HVec 5) (HSlice 6 2 (ref "b"))
      , assign "slice_net" (HVec 4) (HSlice 4 1 (ref "add_vec_rr"))
      , assign "cat_rr" (HVec 16) (HConcat (ref "a") (ref "b"))
      , assign "cat_kr" (HVec 13) (HConcat k8 (ref "c"))
      , assign "cat_rk" (HVec 13) (HConcat (ref "c") k8)
      , assign "cat_kk" (HVec 5) (HConcat (kvec 3 5) (kvec 2 1))
      , assign "zext_same" v8 (HZext 8 (ref "a"))
      , assign "zext_r" (HVec 13) (HZext 13 (ref "c"))
      , assign "zext_k" (HVec 16) (HZext 16 k8)
      , assign "tovec_r" (HVec 1) (HBitToVec (ref "p"))
      , assign "tovec_k" (HVec 1) (HBitToVec (kbit True))
      ]
    registers =
      [ register "reg_vec" v8 (HLitVec 8 0x5A) (ref "add_vec_rr")
      , register "reg_bit" HBit (HLitBit True) (ref "xor_bit_rr")
      , register "reg_kvec" v8 (HLitVec 8 0x22) (kvec 8 0x11)
      , register "reg_kbit" HBit (HLitBit False) (kbit True)
      , register "reg_in" (HVec 5) (HLitVec 5 0x1F) (ref "c")
      , register "reg_self" v8 (HLitVec 8 0x81) (ref "reg_self")
      ]

-- | 4096-bit ports, arithmetic at full width, a 4096-bit literal and a
-- 4096-bit register.
wideNetlist :: Module
wideNetlist =
  Module
    { modName = Ident "wide"
    , modHeader = ["generated by the gin test suite"]
    , modClock = Ident "clk"
    , modReset = Ident "rst"
    , modInputs = [net "a" v, net "b" v]
    , modOutputs = [Output (net ("o_" <> n) ty) (ref n) | (n, ty) <- observedNets]
    , modDecls =
        [ assign "sum" v (HBin BAdd (ref "a") (ref "b"))
        , assign "prod" v (HBin BMul (ref "a") (ref "b"))
        , assign "neg" v (HUn UNeg (ref "a"))
        , assign "top" v (HShl 4095 (ref "a"))
        , assign "low" v (HLshr 4095 (ref "b"))
        , assign "lt" HBit (HBin BUlt (ref "a") (ref "b"))
        , assign "hi" (HVec 2048) (HSlice 2047 0 (ref "a"))
        , assign "lo" (HVec 2048) (HSlice 4095 2048 (ref "b"))
        , assign "swap" v (HConcat (ref "hi") (ref "lo"))
        , assign "mask" v (HBin BXor (ref "a") (kvec 4096 k4096))
        , register "acc" v (HLitVec 4096 k4096) (ref "sum")
        ]
    }
  where
    v = HVec 4096
    -- every third bit from bit 0, and the top bit (4095 is itself a multiple
    -- of 3, so it is left out of the sum: the literal must stay below 2^4096)
    k4096 = sum [2 ^ i | i <- [0, 3 .. 4094 :: Int]] + 2 ^ (4095 :: Int)
    observedNets =
      [ ("sum", v)
      , ("prod", v)
      , ("neg", v)
      , ("top", v)
      , ("low", v)
      , ("lt", HBit)
      , ("swap", v)
      , ("mask", v)
      , ("acc", v)
      ]

-- | Literals of 33, 64 and 100 bits in arithmetic, comparison, mux and
-- register positions, and an output driven by a wide constant.
literalNetlist :: Module
literalNetlist =
  base {modOutputs = modOutputs base <> [Output (net "o_const" (HVec 100)) k100]}
  where
    base =
      observed
        "literals"
        [net "x" (HVec 100), net "p" HBit]
        [ assign "add_k" (HVec 100) (HBin BAdd (ref "x") k100)
        , assign "mul_k" (HVec 100) (HBin BMul k100 (ref "x"))
        , assign "k_only" (HVec 100) (HOperand k100)
        , assign "low64" (HVec 64) (HSlice 63 0 (ref "x"))
        , assign "eq64" HBit (HBin BEq (ref "low64") (kvec 64 (2 ^ (64 :: Int) - 1)))
        , assign "low33" (HVec 33) (HSlice 32 0 (ref "x"))
        , assign "add33" (HVec 33) (HBin BAdd (ref "low33") (kvec 33 (2 ^ (32 :: Int) + 7)))
        , assign "ule33" HBit (HBin BUle (kvec 33 (2 ^ (32 :: Int) + 7)) (ref "low33"))
        , assign "mux_k" (HVec 100) (HMux (ref "p") k100 (ref "x"))
        , register "reg100" (HVec 100) (HLitVec 100 (2 ^ (99 :: Int) + 1)) (ref "add_k")
        ]
    k100 = kvec 100 (2 ^ (99 :: Int) + 0xDEADBEEFCAFEBABE12345)

-- | Every operator on width-1 vectors.
narrowNetlist :: Module
narrowNetlist =
  observed
    "narrow"
    [net "v" v1, net "w" v1, net "p" HBit]
    ( [ assign (opName op <> "_1") (binResult op v1) (HBin op (ref "v") (ref "w"))
      | op <- [minBound .. maxBound]
      ]
        <> [ assign "add_k" v1 (HBin BAdd (ref "v") (kvec 1 1))
           , assign "neg_1" v1 (HUn UNeg (ref "v"))
           , assign "not_1" v1 (HUn UNot (ref "v"))
           , assign "shl_1" v1 (HShl 0 (ref "v"))
           , assign "lshr_1" v1 (HLshr 0 (ref "v"))
           , assign "slice_1" v1 (HSlice 0 0 (ref "v"))
           , assign "cat_1" (HVec 2) (HConcat (ref "v") (ref "w"))
           , assign "zext_1" (HVec 4) (HZext 4 (ref "v"))
           , assign "tovec_1" v1 (HBitToVec (ref "p"))
           , assign "mux_1" v1 (HMux (ref "p") (ref "v") (ref "w"))
           , register "reg_1" v1 (HLitVec 1 1) (ref "add_1")
           ]
    )
  where
    v1 = HVec 1

-- | No registers: the clock and reset are unread.
combNetlist :: Module
combNetlist =
  observed
    "comb"
    [net "a" (HVec 4), net "b" (HVec 4)]
    [ assign "diff" (HVec 4) (HBin BXor (ref "a") (ref "b"))
    , assign "same" HBit (HBin BEq (ref "a") (ref "b"))
    ]

-- | The counter with an extra input that nothing reads.
idleInputNetlist :: Module
idleInputNetlist =
  counterNetlist
    { modName = Ident "idle_input"
    , modInputs = modInputs counterNetlist <> [net "spare" (HVec 3)]
    }

-- | A free-running counter without inputs.
freeRunNetlist :: Module
freeRunNetlist =
  observed
    "free_run"
    []
    [ register "s" (HVec 4) (HLitVec 4 9) (ref "inc")
    , assign "inc" (HVec 4) (HBin BAdd (ref "s") (kvec 4 1))
    ]

-- | An input whose name is the testbench entity's name.
tbNamedPort :: Module
tbNamedPort =
  observed "mirror" [net "mirror_tb" HBit] [assign "q" HBit (HUn UNot (ref "mirror_tb"))]

-- | Header entries with embedded line breaks and control characters.
hostileHeader :: Module
hostileHeader =
  counterNetlist
    { modName = Ident "hostile"
    , modHeader =
        [ "plain"
        , "two\nlines"
        , "carriage\rreturn"
        , "windows\r\nending"
        , "form\ffeed"
        , "vertical\vtab end entity hostile;"
        , "bidi \8238 override and nul \0 and tab\t"
        , "unicode stays: \8704 x, f x = g x"
        ]
    }

-- | @depth@ combinational nets @n1@ … @n<depth>@ of @width@ bits in a
-- chain: @n1 = a + r@, each later net combines the one before it with the
-- input @a@ (add, xor and sub in turn), and the last drives the output @o@
-- and the register @r@. Declared deepest net first, so the declarations
-- arrive in reverse dependency order.
chainNetlist :: Natural -> Int -> Module
chainNetlist width depth =
  Module
    { modName = Ident "chain"
    , modHeader = ["generated by the gin test suite"]
    , modClock = Ident "clk"
    , modReset = Ident "rst"
    , modInputs = [net "a" v]
    , modOutputs = [Output (net "o" v) (ref (link depth))]
    , modDecls =
        reverse $
          register "r" v (HLitVec width 0x5A) (ref (link depth))
            : assign (link 1) v (HBin BAdd (ref "a") (ref "r"))
            : fmap step [2 .. depth]
    }
  where
    v = HVec width
    link :: Int -> Text
    link k = "n" <> tshow k
    step k = assign (link k) v (HBin (cycleOp k) (ref (link (k - 1))) (ref "a"))

-- | Add, xor and sub in turn.
cycleOp :: Int -> BinOp
cycleOp k = case k `mod` 3 of
  0 -> BAdd
  1 -> BXor
  _ -> BSub

-- | @layers@ layers of @lanes@ nets of @width@ bits, then a tree of xors
-- reducing the last layer to one net, which drives the output @o@ and the
-- register @r@. Layer 0 combines the input @a@ with @r@; net @i@ of a later
-- layer combines nets @i@ and @lanes - 1 - i@ of the layer before (add, xor
-- and sub in turn). Declared in dependency order, layer by layer.
--
-- With 500 lanes every process of 1000 nets holds two whole layers, and the
-- 500 values computed in the first are all still to be read by the second:
-- one variable per value would need 2 MB per process.
layeredNetlist :: Natural -> Int -> Int -> Module
layeredNetlist width lanes layers =
  Module
    { modName = Ident "layered"
    , modHeader = ["generated by the gin test suite"]
    , modClock = Ident "clk"
    , modReset = Ident "rst"
    , modInputs = [net "a" v]
    , modOutputs = [Output (net "o" v) (ref root)]
    , modDecls = register "r" v (HLitVec width 1) (ref root) : layerDecls <> treeDecls
    }
  where
    v = HVec width
    x :: Int -> Int -> Text
    x l i = "x" <> tshow l <> "_" <> tshow i
    layerDecls =
      [ assign (x 0 i) v (HBin (cycleOp i) (ref "a") (ref "r")) | i <- [0 .. lanes - 1]]
        <> [ assign (x l i) v (HBin (cycleOp (i + l)) (ref (x (l - 1) i)) (ref (x (l - 1) mirror)))
           | l <- [1 .. layers - 1]
           , i <- [0 .. lanes - 1]
           , let mirror = lanes - 1 - i
           ]
    (root, treeDecls) = reduce (0 :: Int) [x (layers - 1) i | i <- [0 .. lanes - 1]]
    reduce k = \case
      [n] -> (n, [])
      ns ->
        let (pairs, rest) = pairUp ns
            names = ["t" <> tshow (k + j) | j <- [0 .. length pairs - 1]]
            decls = [assign t v (HBin BXor (ref p) (ref q)) | (t, (p, q)) <- zip names pairs]
            (r, more) = reduce (k + length pairs) (names <> rest)
         in (r, decls <> more)
    pairUp = \case
      p : q : ns -> let (ps, rest) = pairUp ns in ((p, q) : ps, rest)
      ns -> ([], ns)

-- | 40 layers of 500 nets of 4096 bits and a 499-net reduction tree: 20499
-- nets, 21 processes, about 49 nets deep.
shallowDag :: Module
shallowDag = layeredNetlist 4096 500 40

-- | 15 blocks of 1000 nets of 4096 bits, one process each. Block @b@
-- computes 140 values @v<b>_<j>@ from the previous block's result, then a
-- chain @c<b>_1@ … @c<b>_720@, then folds the values into the chain end one
-- by one (@s<b>_1@ … @s<b>_140@, the block's result). All 140 values are
-- still to be read while the chain is computed; reading the chain's nets
-- through signals as well would put 15 * 720 signal reads on one path, past
-- nvc's 10000 delta cycles.
crowdedNetlist :: Module
crowdedNetlist =
  Module
    { modName = Ident "crowded"
    , modHeader = ["generated by the gin test suite"]
    , modClock = Ident "clk"
    , modReset = Ident "rst"
    , modInputs = [net "a" v]
    , modOutputs = [Output (net "o" v) (ref (result (blocks - 1)))]
    , modDecls =
        register "r" v (HLitVec 4096 3) (ref (result (blocks - 1)))
          : concatMap block [0 .. blocks - 1]
    }
  where
    v = HVec 4096
    blocks = 15 :: Int
    values = 140 :: Int
    chain = 720 :: Int
    name :: Text -> Int -> Int -> Text
    name p b j = p <> tshow b <> "_" <> tshow j
    result b = name "s" b values
    block b =
      [ assign (name "v" b j) v (HBin (cycleOp j) (ref (input b)) (ref "a"))
      | j <- [0 .. values - 1]
      ]
        <> [assign (name "c" b 1) v (HBin BAdd (ref (input b)) (ref "a"))]
        <> [ assign (name "c" b k) v (HBin (cycleOp k) (ref (name "c" b (k - 1))) (ref "a"))
           | k <- [2 .. chain]
           ]
        <> [assign (name "s" b 1) v (HBin BXor (ref (name "c" b chain)) (ref (name "v" b 0)))]
        <> [ assign (name "s" b j) v (HBin BXor (ref (name "s" b (j - 1))) (ref (name "v" b i)))
           | j <- [2 .. values]
           , let i = j - 1
           ]
    input b = if b == 0 then "r" else result (b - 1)

-- | 16000 nets, so 16 processes. The first holds 130 nets of 4096 bits
-- and 870 narrower ones; the other 15 hold a chain of 4096-bit nets, so
-- together they need far more than 2^23 elements, and the first, needing
-- the least, gets an equal share, 2^23 / 16 = 524288. Its window is
-- therefore 128 nets: net @k@ goes to @gin_v<k mod 128>@ and is read from
-- there for 127 positions. @x@ (position 0) is read 127, 128 and 129 nets
-- later, by which time @z@ (position 128) has taken its variable.
-- Positions 130 to 139 put narrower vectors and bits into the variables of
-- 4096-bit nets and read them through every kind of operator, and a chain
-- of 8-bit nets fills the rest of the first process. Declared in
-- dependency order, so positions are as listed.
windowNetlist :: Module
windowNetlist =
  Module
    { modName = Ident "window"
    , modHeader = ["generated by the gin test suite"]
    , modClock = Ident "clk"
    , modReset = Ident "rst"
    , modInputs = [net "a" wide, net "b" v8]
    , modOutputs =
        [ Output (net ("o_" <> o) ty) (ref o)
        | (o, ty) <-
            [("w", wide), ("c12", HVec 12), ("h", HBit), ("g", HBit), (u narrow, v8), ("vo", v8)]
        ]
    , modDecls =
        register "r" wide (HLitVec 4096 0x5A) (ref "w")
          : [ assign "x" wide (HBin BXor (ref "a") (ref "r")) -- 0
            , assign (f 1) wide (HBin BAdd (ref "a") (ref "r")) -- 1
            ]
          <> [assign (f k) wide (HBin (cycleOp k) (ref (f (k - 1))) (ref "a")) | k <- [2 .. 126]]
          <> [ assign "y" wide (HBin BAdd (ref (f 126)) (ref "x")) -- 127
             , assign "z" wide (HBin BSub (ref "y") (ref "x")) -- 128
             , assign "w" wide (HBin BXor (ref "z") (ref "x")) -- 129
             , assign "s8" v8 (HSlice 7 0 (ref "w")) -- 130
             , assign "g" HBit (HBin BUlt (ref "s8") (ref "b")) -- 131
             , assign "m8" v8 (HMux (ref "g") (ref "s8") (ref "b")) -- 132
             , assign "q" (HVec 1) (HBitToVec (ref "g")) -- 133
             , assign "s4" (HVec 4) (HSlice 5 2 (ref "m8")) -- 134
             , assign "e16" v16 (HZext 16 (ref "s4")) -- 135
             , assign "c12" (HVec 12) (HConcat (ref "s8") (ref "s4")) -- 136
             , assign "h" HBit (HBin BEq (ref "q") (kvec 1 1)) -- 137
             , assign "sh" v16 (HShl 3 (ref "e16")) -- 138
             , assign "p16" v16 (HBin BMul (ref "e16") (ref "sh")) -- 139
             , assign (u 1) v8 (HSlice 11 4 (ref "p16")) -- 140
             ]
          <> [assign (u k) v8 (HBin (cycleOp k) (ref (u (k - 1))) (ref "b")) | k <- [2 .. narrow]]
          <> [assign (v 1) wide (HBin BAdd (ref "w") (ref "a"))] -- 1000
          <> [assign (v k) wide (HBin (cycleOp k) (ref (v (k - 1))) (ref "a")) | k <- [2 .. deep]]
          <> [assign "vo" v8 (HSlice 7 0 (ref (v deep)))] -- 15999
    }
  where
    wide = HVec 4096
    v8 = HVec 8
    v16 = HVec 16
    narrow = 860 :: Int
    deep = 14999 :: Int
    f, u, v :: Int -> Text
    f k = "f" <> tshow k
    u k = "u" <> tshow k
    v k = "v" <> tshow k

-- | 32 lanes of 58 nets of 4096 bits, interleaved so that net @x<k>@ reads
-- @x<k-32>@, then a tree of xors joining their ends into the register
-- @r@; next to them an independent chain of 63112 8-bit nets: 65001
-- combinational nets in 66 processes, declared in dependency order.
-- Together they have 1888 * 4096 + 63113 * 8 = 8238152 bits, within 2^23,
-- so every process gets its whole need: the two wide processes about 4 MB
-- each, far more than an equal share, and every lane step reads a
-- variable.
lanesNetlist :: Module
lanesNetlist =
  Module
    { modName = Ident "lanes"
    , modHeader = ["generated by the gin test suite"]
    , modClock = Ident "clk"
    , modReset = Ident "rst"
    , modInputs = [net "a" v8]
    , modOutputs = [Output (net "o" v8) (ref "o_low"), Output (net "p" v8) (ref (c chain))]
    , modDecls =
        [register "r" wide (HLitVec 4096 0x5A) (ref root), assign "aw" wide (HZext 4096 (ref "a"))]
          <> lanes
          <> tree
          <> [assign "o_low" v8 (HSlice 7 0 (ref root)), assign (c 1) v8 (HUn UNot (ref "a"))]
          <> [assign (c k) v8 (HBin (cycleOp k) (ref (c (k - 1))) (ref "a")) | k <- [2 .. chain]]
    }
  where
    wide = HVec 4096
    v8 = HVec 8
    width = 32 :: Int
    steps = 58 :: Int
    chain = 63112 :: Int
    x, c :: Int -> Text
    x k = "x" <> tshow k
    c k = "c" <> tshow k
    lanes =
      [assign (x k) wide (HShl (fromIntegral k) (ref "r")) | k <- [0 .. width - 1]]
        <> [ assign (x k) wide (HBin (cycleOp k) (ref (x (k - width))) (ref "aw"))
           | k <- [width .. width * steps - 1]
           ]
    (root, tree) = joinAll (0 :: Int) [x k | k <- [width * (steps - 1) .. width * steps - 1]]
    joinAll k = \case
      [n] -> (n, [])
      n1 : n2 : ns ->
        let t = "t" <> tshow k
            (r, more) = joinAll (k + 1) (ns <> [t])
         in (r, assign t wide (HBin BXor (ref n1) (ref n2)) : more)
      [] -> ("aw", [])

-- | 16 chains of 4095 nets of 8 bits, interleaved so that net @k@ reads net
-- @k - 16@, then a tree of xors joining their ends: 65535 nets in 66
-- processes, declared in dependency order. Narrow nets fit their process's
-- variables whole, so every step, 16 positions long, reads a variable and
-- a path makes a signal read only between processes.
interleavedNetlist :: Module
interleavedNetlist =
  Module
    { modName = Ident "interleaved"
    , modHeader = ["generated by the gin test suite"]
    , modClock = Ident "clk"
    , modReset = Ident "rst"
    , modInputs = [net "a" v8]
    , modOutputs = [Output (net "o" v8) (ref root)]
    , modDecls = register "r" v8 (HLitVec 8 0x3C) (ref root) : chains <> tree
    }
  where
    v8 = HVec 8
    lanes = 16 :: Int
    depth = 4095 :: Int
    x :: Int -> Text
    x k = "x" <> tshow k
    chains =
      [assign (x k) v8 (HBin (cycleOp k) (ref "a") (ref "r")) | k <- [0 .. lanes - 1]]
        <> [ assign (x k) v8 (HBin (cycleOp k) (ref (x (k - lanes))) (ref "a"))
           | k <- [lanes .. lanes * depth - 1]
           ]
    ends = [x k | k <- [lanes * (depth - 1) .. lanes * depth - 1]]
    (root, tree) = joinAll (0 :: Int) ends
    joinAll k = \case
      [n] -> (n, [])
      n1 : n2 : ns ->
        let t = "t" <> tshow k
            (r, more) = joinAll (k + 1) (ns <> [t])
         in (r, assign t v8 (HBin BXor (ref n1) (ref n2)) : more)
      [] -> ("a", [])

-- | Invariant 6 forbids slicing a constant; the backend folds it anyway.
constantSlice :: Module
constantSlice =
  Module
    { modName = Ident "folded"
    , modHeader = []
    , modClock = Ident "clk"
    , modReset = Ident "rst"
    , modInputs = []
    , modOutputs = [Output (net "o" (HVec 4)) (ref "s")]
    , modDecls = [assign "s" (HVec 4) (HSlice 5 2 (kvec 8 0xB4))]
    }

tshow :: (Show a) => a -> Text
tshow = Text.pack . show
