-- | Tests for the VHDL-2008 backend.
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
import Data.List (mapAccumL, nub, unfoldr)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe (isNothing)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Text.Encoding qualified as Text
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
import Gin.Netlist.Types
import Gin.TestUtil (goldenText, itWithTools, runTool, withTempDir)
import Gin.Vectors (Cycle (..), Vectors (..))
import Numeric (showHex)
import Numeric.Natural (Natural)
import System.Exit (ExitCode (..))
import System.FilePath ((</>))
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
        `shouldSatisfy` Text.isInfixOf "gin_v_s := unsigned'(\"1101\");"

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

  describe "operators" $ do
    it "the reference evaluator reproduces the hand-written fixture vectors" $
      for_ fixtures $ \(_, m, vs) ->
        vectorsFor m (fmap cycInputs (vecCycles vs)) `shouldBe` vs
    it "the test netlists satisfy the netlist identifier and reference invariants" $
      for_ allDesigns $ \m -> invariantViolations m `shouldBe` []
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

  describe "combinational depth" $ do
    it "assigns every combinational net once, after the nets it reads" $
      for_ (chainNetlist 40 : allDesigns) $ \m -> do
        let src = backendRender vhdl m
        readsBeforeAssigned src `shouldBe` []
        Set.fromList (assignedVariables src) `shouldBe` combinationalVariables m
        length (assignedVariables src) `shouldBe` Set.size (combinationalVariables m)
    it "splits deep logic into processes of at most 1000 nets each" $ do
      let sizes = processSizes (backendRender vhdl (chainNetlist 12000))
      sum sizes `shouldBe` 12000
      length sizes `shouldBe` 12
      sizes `shouldSatisfy` all (<= 1000)
    itWithTools ["nvc"] "a chain 12000 nets deep (past nvc's 10000 delta cycles) passes" $ do
      let deep = chainNetlist 12000
      length (modDecls deep) `shouldSatisfy` (<= maxNormalBinds)
      checkRun deep (vectorsFor deep (inputRows 37 4 deep))

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

-- | Variables of the combinational processes in assignment order: the
-- targets of @:=@ on lines that start with a @gin_v_@ name.
assignedVariables :: Text -> [Text]
assignedVariables src =
  [ lhs
  | l <- codeLines src
  , let (lhs, rest) = Text.breakOn " := " (Text.strip l)
  , "gin_v_" `Text.isPrefixOf` lhs
  , not (Text.null rest)
  ]

-- | Assignments to a @gin_v_@ variable that read a @gin_v_@ variable not
-- assigned on an earlier line of the same process.
readsBeforeAssigned :: Text -> [Text]
readsBeforeAssigned = go Set.empty . codeLines
  where
    go _ [] = []
    go assigned (l : ls) = case Text.breakOn " := " (Text.strip l) of
      (lhs, rhs)
        | "gin_v_" `Text.isPrefixOf` lhs && not (Text.null rhs) ->
            [l | any (`Set.notMember` assigned) (variables rhs)]
              <> go (Set.insert lhs assigned) ls
      _
        | Text.strip l == "end process;" -> go Set.empty ls
        | otherwise -> go assigned ls
    variables = filter ("gin_v_" `Text.isPrefixOf`) . Text.split (not . isWordChar)
    isWordChar c = isAlphaNum c || c == '_'

-- | The number of variable assignments in each process, in order.
processSizes :: Text -> [Int]
processSizes = go . codeLines
  where
    go ls = case break (== "process (all)") (fmap Text.strip ls) of
      (_, _ : rest) ->
        let (body, remaining) = break (== "end process;") rest
         in length [l | l <- body, " := " `Text.isInfixOf` l] : go remaining
      (_, []) -> []

-- | The variable names the combinational processes should assign: one per
-- combinational net.
combinationalVariables :: Module -> Set Text
combinationalVariables m =
  Set.fromList ["gin_v_" <> unIdent (netName n) | DAssign n _ <- modDecls m]

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
    <> ["duplicate identifiers" | length (nub lowered) /= length lowered]
    <> ["dangling reference " <> show i | ORef i <- operands, isNothing (operandType m (ORef i))]
    <> [ "unread net " <> show n
       | n <- fmap (netName . declNet) (modDecls m)
       , ORef n `notElem` operands
       ]
  where
    idents =
      modName m
        : modClock m
        : modReset m
        : fmap netName (modInputs m <> fmap outNet (modOutputs m) <> fmap declNet (modDecls m))
    lowered = fmap (Text.map toLower . unIdent) idents
    operands = fmap outDriver (modOutputs m) <> concatMap declOperands (modDecls m)
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
    <> [combNetlist, idleInputNetlist, freeRunNetlist, tbNamedPort, chainNetlist 40]

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
    k4096 = sum [2 ^ i | i <- [0, 3 .. 4095 :: Int]] + 2 ^ (4095 :: Int)
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

-- | @depth@ combinational nets @n1@ … @n<depth>@ in a chain: @n1 = a + r@,
-- each later net combines the one before it with a constant (add, xor and
-- sub in turn), and the last drives the output @o@ and the register @r@.
-- Declared deepest net first, so the declarations arrive in reverse
-- dependency order.
chainNetlist :: Int -> Module
chainNetlist depth =
  Module
    { modName = Ident "chain"
    , modHeader = ["generated by the gin test suite"]
    , modClock = Ident "clk"
    , modReset = Ident "rst"
    , modInputs = [net "a" v8]
    , modOutputs = [Output (net "o" v8) (ref (link depth))]
    , modDecls =
        reverse $
          register "r" v8 (HLitVec 8 0x5A) (ref (link depth))
            : assign (link 1) v8 (HBin BAdd (ref "a") (ref "r"))
            : fmap step [2 .. depth]
    }
  where
    v8 = HVec 8
    link :: Int -> Text
    link k = "n" <> tshow k
    step k = assign (link k) v8 (HBin (stepOp k) (ref (link (k - 1))) (kvec 8 (stepConst k)))
    stepConst k = toInteger k `mod` 256
    stepOp k = case k `mod` 3 of
      0 -> BAdd
      1 -> BXor
      _ -> BSub

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
