-- | Tests for "Gin.Netlist.Build". Every netlist the builder produces is
-- checked against the invariants documented in "Gin.Netlist.Types" by
-- 'validate', a validator local to this module.
module Gin.Netlist.BuildSpec (spec) where

import Control.Monad (guard)
import Data.Bits (testBit)
import Data.Char (isAsciiLower, toUpper)
import Data.Foldable (for_)
import Data.Graph (SCC (..), flattenSCC, stronglyConnComp)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (isJust)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as Text
import Gin.Core.Normal
import Gin.Core.Syntax
import Gin.Error (GinError (..), Stage (..))
import Gin.Examples
import Gin.Netlist.Build (buildNetlist, sanitize)
import Gin.Netlist.Types
import Numeric.Natural (Natural)
import Test.Hspec
  ( Expectation
  , Spec
  , describe
  , expectationFailure
  , it
  , shouldBe
  , shouldSatisfy
  )
import Test.Hspec.QuickCheck (modifyMaxSuccess, prop)
import Test.QuickCheck
  ( Gen
  , Property
  , arbitrary
  , arbitraryUnicodeChar
  , checkCoverage
  , chooseInt
  , chooseInteger
  , conjoin
  , counterexample
  , cover
  , elements
  , forAll
  , frequency
  , listOf
  , oneof
  , shuffle
  , sublistOf
  , vectorOf
  , (===)
  )
import Text.Read (readMaybe)

spec :: Spec
spec = do
  describe "sanitize" sanitizeSpec
  describe "lowering" loweringSpec
  describe "example circuits" examplesSpec
  describe "port names" portsSpec
  describe "top name" topNameSpec
  describe "folding" foldSpec
  describe "invariants" invariantsSpec
  describe "precondition violations" preconditionSpec

----------------------------------------------------------------------
-- sanitize

sanitizeSpec :: Spec
sanitizeSpec = do
  describe "without collisions" $ for_ sanitizeCases $ \(raw, expected) ->
    it ("[nl-sanitize] " <> show raw <> " becomes " <> show expected) $ do
      sanitize Set.empty raw `shouldBe` expected
      expected `shouldSatisfy` isLegalIdent
  describe "with collisions" $ for_ collisionCases $ \(label, taken, raw, expected) ->
    it ("[nl-sanitize] " <> label) $ do
      sanitize (Set.fromList taken) raw `shouldBe` expected
      expected `shouldSatisfy` isLegalIdent
  modifyMaxSuccess (const 2000) $ do
    prop "[nl-sanitize] always returns a legal identifier" $
      forAll genSanitizeInput $ \(taken, raw) ->
        let r = sanitize taken raw in counterexample (show r) (isLegalIdent r)
    prop "[nl-sanitize] never returns a taken name, compared case-insensitively" $
      forAll genSanitizeInput $ \(taken, raw) ->
        let r = sanitize taken raw
         in counterexample (show r) (Text.toLower r `Set.notMember` Set.map Text.toLower taken)
    prop "[nl-sanitize] is deterministic: the base name when free, else its least free suffix" $
      checkCoverage . forAll genSanitizeInput $ \(taken, raw) ->
        let collided = sanitize taken raw /= sanitize Set.empty raw
         in cover 40 collided "collision" . cover 10 (not collided) "no collision" $
              leastFreeSuffix taken raw
    prop "[nl-sanitize] ignores the ASCII case of taken names" $
      forAll genSanitizeInput $ \(taken, raw) ->
        sanitize (Set.map asciiUpper taken) raw === sanitize taken raw
    prop "[nl-sanitize] keeps legal names of at most 56 characters other than gin" $
      forAll genShortLegal $ \raw -> sanitize Set.empty raw === raw

-- | Inputs and their sanitized forms when nothing is taken.
sanitizeCases :: [(Text, Text)]
sanitizeCases =
  [ ("x", "x")
  , ("_x", "x")
  , ("x_", "x")
  , ("", "n")
  , ("___", "n")
  , ("\252", "n")
  , ("\220nit", "nit")
  , ("Counter.counter", "counter_counter")
  , ("acc'", "acc")
  , ("s.next", "s_next")
  , ("a__b", "a_b")
  , ("a-.-b", "a_b")
  , ("MiXeD", "mixed")
  , ("x_1", "x_1")
  , ("1x", "n_1x")
  , ("9", "n_9")
  , ("gin", "n_gin")
  , ("gin_x", "n_gin_x")
  , ("GIN_X", "n_gin_x")
  , ("gin.x", "n_gin_x")
  , ("ginx", "ginx")
  , ("module", "n_module")
  , ("Module", "n_module")
  , ("entity", "n_entity")
  , ("logic", "n_logic")
  , ("std_logic_1164", "n_std_logic_1164")
  , ("SIGNAL", "n_signal")
  , ("n", "n")
  , ("n_module", "n_module")
  , (Text.replicate 70 "a", Text.replicate 56 "a")
  , (Text.replicate 55 "a" <> "_" <> Text.replicate 14 "b", Text.replicate 55 "a")
  , ("1" <> Text.replicate 69 "a", "n_1" <> Text.replicate 53 "a")
  ]

-- | Collisions: label, taken names, input, result.
collisionCases :: [(String, [Text], Text, Text)]
collisionCases =
  [ ("a taken name gets the suffix _1", ["x"], "x", "x_1")
  , ("the suffix counts up past taken suffixes", ["x", "x_1", "x_2"], "x", "x_3")
  , ("the least free suffix is used", ["x", "x_2"], "x", "x_1")
  , ("collisions are case-insensitive", ["X"], "x", "x_1")
  , ("the sanitized name is what collides", ["x"], "X'", "x_1")
  , ("a free base name ignores taken suffixed names", ["x_1", "x_2"], "x", "x")
  , ("the clock name is avoided", ["clk"], "CLK", "clk_1")
  , ("the empty name collides as n", ["n"], "", "n_1")
  , ("a prefixed reserved word collides too", ["n_module"], "module", "n_module_1")
  , ( "a 70-character name collides after truncation"
    , [long56]
    , Text.replicate 70 "a"
    , long56 <> "_1"
    )
  , ("suffixes go past one digit", "y" : ["y_" <> tshow k | k <- [1 .. 10 :: Int]], "y", "y_11")
  ]
  where
    long56 = Text.replicate 56 "a"

-- | The result is the base name ('sanitize' with nothing taken) when that
-- is free; otherwise it is the base name with the least suffix @_k@ that
-- is free and legal.
leastFreeSuffix :: Set Text -> Text -> Property
leastFreeSuffix taken raw =
  counterexample ("result: " <> show r) $
    if free base
      then r === base
      else case Text.stripPrefix (base <> "_") r >>= readSuffix of
        Just k ->
          conjoin
            [ counterexample "suffix below 1" (k >= 1)
            , counterexample "result not free" (free r)
            , counterexample "a smaller suffix was free" $
                not (any (free . suffixed) [1 .. k - 1])
            ]
        Nothing -> counterexample "not the base name with a numeric suffix" False
  where
    r = sanitize taken raw
    base = sanitize Set.empty raw
    lowered = Set.map Text.toLower taken
    free c = Text.toLower c `Set.notMember` lowered && isLegalIdent c
    suffixed k = base <> "_" <> tshow k
    readSuffix ks = case readMaybe (Text.unpack ks) of
      Just k | tshow k == ks -> Just (k :: Int)
      _ -> Nothing

genSanitizeInput :: Gen (Set Text, Text)
genSanitizeInput = do
  raw <- genRawName
  taken <- genTaken raw
  pure (taken, raw)

-- | Names of every shape the IR may carry: arbitrary Unicode, ASCII
-- punctuation, reserved words, @gin@ prefixes and long names.
genRawName :: Gen Text
genRawName =
  frequency
    [ (3, Text.pack <$> listOf arbitraryUnicodeChar)
    , (4, Text.pack <$> listOf (elements "aAzZ09_-.'$ \220\x202E"))
    , (2, elements (Set.toList reservedWords))
    , (1, Text.toUpper <$> elements (Set.toList reservedWords))
    , (1, ("gin" <>) . Text.pack <$> listOf (elements "_xG."))
    , (1, Text.pack <$> (chooseInt (50, 80) >>= \n -> vectorOf n (elements "ab_.")))
    ]

-- | Taken names, biased towards collisions with @raw@'s base name and its
-- suffixed variants.
genTaken :: Text -> Gen (Set Text)
genTaken raw = do
  let base = sanitize Set.empty raw
  upper <- arbitrary
  k <- frequency [(1, pure 0), (3, chooseInt (1, 12))]
  ks <- sublistOf [1 .. k]
  unrelated <- listOf genRawName
  let related = [base | k > 0] <> [base <> "_" <> tshow i | i <- ks]
  pure (Set.fromList (fmap (if upper then asciiUpper else id) related <> unrelated))

-- | Legal identifiers of at most 56 characters, other than @gin@.
genShortLegal :: Gen Text
genShortLegal = do
  first <- elements ['a' .. 'z']
  rest <- listOf (elements "abgin019_")
  let t = Text.pack (first : take 55 rest)
  if isLegalIdent t && t /= "gin" then pure t else genShortLegal

asciiUpper :: Text -> Text
asciiUpper = Text.map (\c -> if isAsciiLower c then toUpper c else c)

tshow :: (Show a) => a -> Text
tshow = Text.pack . show

----------------------------------------------------------------------
-- lowering

loweringSpec :: Spec
loweringSpec = do
  for_ loweringCases $ \(label, t, rhs, expected) ->
    it ("lowers " <> label) $ do
      let nm = singleBind t rhs
      modDecls <$> buildNetlist nm `shouldBe` Right [DAssign (Net (Ident "r") (hwOf t)) expected]
      validate <$> buildNetlist nm `shouldBe` Right []
  it "lowers a bit-vector register to a register with its initial value as reset value" $
    modDecls <$> buildNetlist (singleBind (bv 8) (NReg (VBV 8 7) a8))
      `shouldBe` Right [DReg (Net (Ident "r") (HVec 8)) (HLitVec 8 7) (ref "a")]
  it "lowers a Bool register to a single-bit register" $
    modDecls <$> buildNetlist (singleBind TBool (NReg (VBool True) pB))
      `shouldBe` Right [DReg (Net (Ident "r") HBit) (HLitBit True) (ref "p")]
  it "keeps the top name and the ports, in order, and adds clk and rst" $ do
    let result = buildNetlist (singleBind (bv 8) (NPrim BvAdd [a8, b8]))
    modName <$> result `shouldBe` Right (Ident "single")
    modClock <$> result `shouldBe` Right (Ident "clk")
    modReset <$> result `shouldBe` Right (Ident "rst")
    modInputs <$> result
      `shouldBe` Right
        [ Net (Ident "a") (HVec 8)
        , Net (Ident "b") (HVec 8)
        , Net (Ident "p") HBit
        , Net (Ident "q") HBit
        ]
    modOutputs <$> result `shouldBe` Right [Output (Net (Ident "o") (HVec 8)) (ref "r")]
  it "drives outputs directly from inputs and literals" $ do
    let nm =
          (singleBind TBool (NAtom pB))
            { nmOutputs =
                [ NOutput "o" TBool (AVar "p")
                , NOutput "c" (bv 8) (ALit (VBV 8 3))
                ]
            , nmBinds = []
            }
    modOutputs <$> buildNetlist nm
      `shouldBe` Right
        [ Output (Net (Ident "o") HBit) (ref "p")
        , Output (Net (Ident "c") (HVec 8)) (OConst (HLitVec 8 3))
        ]
    modDecls <$> buildNetlist nm `shouldBe` Right []
    validate <$> buildNetlist nm `shouldBe` Right []
  it "[nl-sanitize] names binds in order around the top name, clock, reset and ports" $ do
    let result = buildNetlist renamingModule
        x = ref "x"
    modDecls <$> result
      `shouldBe` Right
        [ DAssign (vec8 "x_1") (HUn UNot x)
        , DAssign (vec8 "x_2") (HBin BAdd (ref "x_1") x)
        , DAssign (vec8 "clk_1") (HBin BXor (ref "x_2") (ref "x_1"))
        , DAssign (vec8 "rename_1") (HBin BAnd (ref "clk_1") x)
        , DAssign (vec8 "y_1") (HBin BOr (ref "rename_1") (ref "x_2"))
        ]
    modOutputs <$> result `shouldBe` Right [Output (vec8 "y") (ref "y_1")]
    validate <$> result `shouldBe` Right []

-- | Label, bind type, right-hand side and the expression it lowers to, in
-- 'singleBind'.
loweringCases :: [(String, Ty, NRhs, HExpr)]
loweringCases =
  [ ("bool.and", TBool, NPrim BoolAnd [pB, qB], HBin BAnd (ref "p") (ref "q"))
  , ("bool.or", TBool, NPrim BoolOr [pB, qB], HBin BOr (ref "p") (ref "q"))
  , ("bool.xor", TBool, NPrim BoolXor [pB, qB], HBin BXor (ref "p") (ref "q"))
  , ("bool.not", TBool, NPrim BoolNot [pB], HUn UNot (ref "p"))
  , ("bool.eq", TBool, NPrim BoolEq [pB, qB], HBin BEq (ref "p") (ref "q"))
  , ("bv.add", bv 8, NPrim BvAdd [a8, b8], HBin BAdd (ref "a") (ref "b"))
  , ("bv.sub", bv 8, NPrim BvSub [a8, b8], HBin BSub (ref "a") (ref "b"))
  , ("bv.mul", bv 8, NPrim BvMul [a8, b8], HBin BMul (ref "a") (ref "b"))
  , ("bv.and", bv 8, NPrim BvAnd [a8, b8], HBin BAnd (ref "a") (ref "b"))
  , ("bv.or", bv 8, NPrim BvOr [a8, b8], HBin BOr (ref "a") (ref "b"))
  , ("bv.xor", bv 8, NPrim BvXor [a8, b8], HBin BXor (ref "a") (ref "b"))
  , ("bv.neg", bv 8, NPrim BvNeg [a8], HUn UNeg (ref "a"))
  , ("bv.not", bv 8, NPrim BvNot [a8], HUn UNot (ref "a"))
  , ("bv.shl", bv 8, NPrim (BvShl 3) [a8], HShl 3 (ref "a"))
  , ("bv.lshr", bv 8, NPrim (BvLshr 3) [a8], HLshr 3 (ref "a"))
  , ("bv.eq", TBool, NPrim BvEq [a8, b8], HBin BEq (ref "a") (ref "b"))
  , ("bv.ult", TBool, NPrim BvUlt [a8, b8], HBin BUlt (ref "a") (ref "b"))
  , ("bv.ule", TBool, NPrim BvUle [a8, b8], HBin BUle (ref "a") (ref "b"))
  , ("bv.concat", bv 16, NPrim BvConcat [a8, b8], HConcat (ref "a") (ref "b"))
  , ("bv.extract", bv 4, NPrim (BvExtract 5 2) [a8], HSlice 5 2 (ref "a"))
  , ("bv.zext", bv 16, NPrim (BvZext 16) [a8], HZext 16 (ref "a"))
  , ("bv.ofBool", bv 1, NPrim BvOfBool [pB], HBitToVec (ref "p"))
  , ("a mux", bv 8, NMux pB a8 b8, HMux (ref "p") (ref "a") (ref "b"))
  , ("a Bool literal", TBool, NPrim BoolAnd [pB, ALit (VBool True)], HBin BAnd (ref "p") true)
  , ("a bit-vector literal", bv 8, NPrim BvAdd [a8, lit8 200], HBin BAdd (ref "a") (vconst 8 200))
  , ("an atom", bv 8, NAtom (lit8 9), HOperand (vconst 8 9))
  ]
  where
    true = OConst (HLitBit True)

-- | Inputs a, b : BitVec 8 and p, q : Bool; one bind r of the given type
-- and right-hand side; one output o reading r.
singleBind :: Ty -> NRhs -> NModule
singleBind t rhs =
  NModule
    { nmName = "single"
    , nmDomain = sysDomain
    , nmInputs = [("a", bv 8), ("b", bv 8), ("p", TBool), ("q", TBool)]
    , nmOutputs = [NOutput "o" t (AVar "r")]
    , nmBinds = [NBind "r" t rhs]
    , nmCertificate = testCertificate "Single.single_correct"
    }

-- | Bind names that collide, once sanitized, with the input x, the output
-- y, the clock and the top name, and with each other.
renamingModule :: NModule
renamingModule =
  NModule
    { nmName = "rename"
    , nmDomain = sysDomain
    , nmInputs = [("x", bv 8)]
    , nmOutputs = [NOutput "y" (bv 8) (AVar "y")]
    , nmBinds =
        [ NBind "X" (bv 8) (NPrim BvNot [AVar "x"])
        , NBind "x'" (bv 8) (NPrim BvAdd [AVar "X", AVar "x"])
        , NBind "clk" (bv 8) (NPrim BvXor [AVar "x'", AVar "X"])
        , NBind "rename" (bv 8) (NPrim BvAnd [AVar "clk", AVar "x"])
        , NBind "y" (bv 8) (NPrim BvOr [AVar "rename", AVar "x'"])
        ]
    , nmCertificate = testCertificate "Rename.rename_correct"
    }

a8, b8, pB, qB :: Atom
a8 = AVar "a"
b8 = AVar "b"
pB = AVar "p"
qB = AVar "q"

lit8 :: Integer -> Atom
lit8 = ALit . VBV 8

ref :: Text -> Operand
ref = ORef . Ident

vconst :: Natural -> Integer -> Operand
vconst w = OConst . HLitVec w

vec8 :: Text -> Net
vec8 n = Net (Ident n) (HVec 8)

hwOf :: Ty -> HwType
hwOf = \case
  TBitVec w -> HVec w
  _ -> HBit

----------------------------------------------------------------------
-- example circuits

examplesSpec :: Spec
examplesSpec =
  for_ examples $ \(name, normal, expected) -> do
    it ("[nl-examples] " <> name <> " lowers to the hand-written netlist, header aside") $
      withoutHeader <$> buildNetlist normal `shouldBe` Right (withoutHeader expected)
    it ("[nl-invariants] " <> name <> " lowers to a netlist that satisfies every invariant") $
      validate <$> buildNetlist normal `shouldBe` Right []
  where
    withoutHeader m = m {modHeader = []}

examples :: [(String, NModule, Module)]
examples =
  [ ("counter", counterNormal, counterNetlist)
  , ("mac", macNormal, macNetlist)
  , ("detector", detectorNormal, detectorNetlist)
  ]

----------------------------------------------------------------------
-- port and top names

portsSpec :: Spec
portsSpec = do
  for_ badPorts $ \(label, ins, outs, culprit) ->
    it ("[nl-ports] rejects " <> label) $
      buildNetlist (portsModule "top" ins outs) `shouldFailNaming` culprit
  it "[nl-ports] accepts legal, distinct port names" $ do
    let result = buildNetlist (portsModule "top" ["a", "b_2"] ["o", "count"])
    fmap netName . modInputs <$> result `shouldBe` Right [Ident "a", Ident "b_2"]
    fmap (netName . outNet) . modOutputs <$> result `shouldBe` Right [Ident "o", Ident "count"]
    validate <$> result `shouldBe` Right []

-- | Label, input port names, output port names, the name to blame.
badPorts :: [(String, [Text], [Text], Text)]
badPorts =
  [ ("an input Count next to an output count", ["Count"], ["count"], "Count")
  , ("an output Count next to an input count", ["count"], ["Count"], "Count")
  , ("the reserved word out", ["a"], ["out"], "out")
  , ("the reserved word signal", ["signal"], ["o"], "signal")
  , ("a name starting with a digit", ["1x"], ["o"], "1x")
  , ("an input named clk", ["clk"], ["o"], "clk")
  , ("an output named rst", ["a"], ["rst"], "rst")
  , ("an input named CLK", ["CLK"], ["o"], "CLK")
  , ("two inputs named a", ["a", "a"], ["o"], "a")
  , ("an input and an output named a", ["a"], ["a"], "a")
  , ("two outputs named o", [], ["o", "o"], "o")
  , ("the gin_ prefix", ["gin_a"], ["o"], "gin_a")
  , ("a 65-character name", [Text.replicate 65 "a"], ["o"], Text.replicate 65 "a")
  , ("an empty name", [""], ["o"], "")
  , ("a trailing underscore", ["a_"], ["o"], "a_")
  , ("a double underscore", ["a__b"], ["o"], "a__b")
  ]

topNameSpec :: Spec
topNameSpec = do
  for_ badTopNames $ \(label, top, culprit) ->
    it ("[nl-modname] rejects " <> label) $
      buildNetlist (portsModule top ["en"] ["count"]) `shouldFailNaming` culprit
  it "[nl-modname] accepts a legal top name distinct from the ports" $
    modName <$> buildNetlist (portsModule "counter_2" ["en"] ["count"])
      `shouldBe` Right (Ident "counter_2")

-- | Label, top name (next to the input en and the output count), the name
-- to blame.
badTopNames :: [(String, Text, Text)]
badTopNames =
  [ ("a top name equal to an input port", "en", "en")
  , ("a top name equal to an output port", "count", "count")
  , ("a top name differing from a port only in case", "Count", "Count")
  , ("an uppercase top name", "Counter", "Counter")
  , ("a qualified Lean name", "Counter.counter", "Counter.counter")
  , ("a reserved top name", "module", "module")
  , ("the top name clk", "clk", "clk")
  , ("the top name rst", "rst", "rst")
  , ("the gin_ prefix", "gin_top", "gin_top")
  , ("an empty top name", "", "")
  ]

-- | A module without binds whose Bool outputs are constant.
portsModule :: Text -> [Text] -> [Text] -> NModule
portsModule top ins outs =
  NModule
    { nmName = top
    , nmDomain = sysDomain
    , nmInputs = [(Name i, TBool) | i <- ins]
    , nmOutputs = [NOutput o TBool (ALit (VBool False)) | o <- outs]
    , nmBinds = []
    , nmCertificate = testCertificate "Ports.ports_correct"
    }

-- | The build fails in the netlist stage, and the message quotes @culprit@.
shouldFailNaming :: Either GinError Module -> Text -> Expectation
shouldFailNaming result culprit = case result of
  Left e -> do
    errStage e `shouldBe` StNetlist
    errMessage e `shouldSatisfy` Text.isInfixOf (tshow culprit)
  Right m -> expectationFailure ("expected a netlist error, got " <> show m)

----------------------------------------------------------------------
-- folding

foldSpec :: Spec
foldSpec = do
  it "[nl-fold] folds bv.shl by the operand width to zero" $
    foldModule [NBind "r" (bv 8) (NPrim (BvShl 8) [x8])] `foldsTo` [assign8 "r" zero8]
  it "[nl-fold] folds bv.lshr by the operand width to zero" $
    foldModule [NBind "r" (bv 8) (NPrim (BvLshr 8) [x8])] `foldsTo` [assign8 "r" zero8]
  it "[nl-fold] folds shifts far beyond the operand width to zero" $ do
    foldModule [NBind "r" (bv 8) (NPrim (BvShl 1000) [x8])] `foldsTo` [assign8 "r" zero8]
    foldModule [NBind "r" (bv 8) (NPrim (BvLshr 4096) [x8])] `foldsTo` [assign8 "r" zero8]
  it "[nl-fold] keeps shifts by one less than the operand width" $ do
    foldModule [NBind "r" (bv 8) (NPrim (BvShl 7) [x8])]
      `foldsTo` [DAssign (vec8 "r") (HShl 7 (ref "x"))]
    foldModule [NBind "r" (bv 8) (NPrim (BvLshr 7) [x8])]
      `foldsTo` [DAssign (vec8 "r") (HLshr 7 (ref "x"))]
  it "[nl-fold] folds a shift of a literal by the operand width to zero" $
    foldModule [NBind "r" (bv 8) (NPrim (BvShl 8) [lit8 255])] `foldsTo` [assign8 "r" zero8]
  it "[nl-fold] folds bv.extract of a literal to the selected bits" $ do
    -- 180 = 0b1011_0100: bits 5..2 are 0b1101 = 13.
    foldModuleOf (bv 4) [NBind "r" (bv 4) (NPrim (BvExtract 5 2) [lit8 180])]
      `foldsTo` [DAssign (Net (Ident "r") (HVec 4)) (HOperand (vconst 4 13))]
    foldModuleOf (bv 1) [NBind "r" (bv 1) (NPrim (BvExtract 7 7) [lit8 128])]
      `foldsTo` [DAssign (Net (Ident "r") (HVec 1)) (HOperand (vconst 1 1))]
    foldModule [NBind "r" (bv 8) (NPrim (BvExtract 7 0) [lit8 200])]
      `foldsTo` [assign8 "r" (HOperand (vconst 8 200))]
  it "[nl-fold] keeps bv.extract of a variable as a slice" $
    foldModuleOf (bv 4) [NBind "r" (bv 4) (NPrim (BvExtract 5 2) [x8])]
      `foldsTo` [DAssign (Net (Ident "r") (HVec 4)) (HSlice 5 2 (ref "x"))]
  it "[nl-fold] drops a bind that only a folded shift read" $
    foldModule
      [ NBind "t" (bv 8) (NPrim BvAdd [x8, x8])
      , NBind "r" (bv 8) (NPrim (BvShl 8) [AVar "t"])
      ]
      `foldsTo` [assign8 "r" zero8]
  it "[nl-fold] drops declarations until every declared net is read" $
    foldModule
      [ NBind "t1" (bv 8) (NPrim BvAdd [x8, x8])
      , NBind "t2" (bv 8) (NPrim BvNot [AVar "t1"])
      , NBind "t3" (bv 8) (NPrim BvXor [AVar "t2", AVar "t1"])
      , NBind "r" (bv 8) (NPrim (BvLshr 9) [AVar "t3"])
      ]
      `foldsTo` [assign8 "r" zero8]
  it "[nl-fold] keeps a bind that a folded shift and another declaration read" $
    foldModule
      [ NBind "t" (bv 8) (NPrim BvAdd [x8, x8])
      , NBind "u" (bv 8) (NPrim (BvShl 8) [AVar "t"])
      , NBind "r" (bv 8) (NPrim BvXor [AVar "t", AVar "u"])
      ]
      `foldsTo` [ assign8 "t" (HBin BAdd (ref "x") (ref "x"))
                , assign8 "u" zero8
                , assign8 "r" (HBin BXor (ref "t") (ref "u"))
                ]
  it "[nl-fold] keeps a register loop that a folded shift read, since its nets read each other" $
    foldModule
      [ NBind "s" (bv 8) (NReg (VBV 8 0) (AVar "s_next"))
      , NBind "s_next" (bv 8) (NPrim BvAdd [AVar "s", lit8 1])
      , NBind "r" (bv 8) (NPrim (BvShl 8) [AVar "s"])
      ]
      `foldsTo` [ DReg (vec8 "s") (HLitVec 8 0) (ref "s_next")
                , assign8 "s_next" (HBin BAdd (ref "s") (vconst 8 1))
                , assign8 "r" zero8
                ]
  modifyMaxSuccess (const 500) $ do
    prop "[nl-fold] folds bv.extract of any literal to exactly the selected bits" $
      forAll genExtract $ \(w, v, hi, lo) ->
        let width = hi - lo + 1
            r = NBind "r" (bv width) (NPrim (BvExtract hi lo) [ALit (VBV w v)])
         in case modDecls <$> buildNetlist (foldModuleOf (bv width) [r]) of
              Right [DAssign _ (HOperand (OConst (HLitVec w' v')))] ->
                conjoin
                  [ w' === width
                  , counterexample "value out of range" (v' >= 0 && v' < 2 ^ width)
                  , conjoin
                      [ testBit v' i === testBit v (fromIntegral lo + i)
                      | i <- [0 .. fromIntegral width - 1]
                      ]
                  ]
              other -> counterexample (show other) False
    prop "[nl-fold] folds a shift to zero exactly when the amount is at least the width" $
      forAll genShift $ \(w, k, isLeft) ->
        let op = if isLeft then BvShl k else BvLshr k
            nm =
              (foldModuleOf (bv w) [NBind "r" (bv w) (NPrim op [AVar "x"])])
                { nmInputs = [("x", bv w)]
                }
            kept = if isLeft then HShl k (ref "x") else HLshr k (ref "x")
            expected = if k < w then kept else HOperand (vconst w 0)
         in fmap modDecls (buildNetlist nm) === Right [DAssign (Net (Ident "r") (HVec w)) expected]

-- | Input x : BitVec 8, the given binds and an output y : BitVec 8 reading r.
foldModule :: [NBind] -> NModule
foldModule = foldModuleOf (bv 8)

-- | Input x : BitVec 8, the given binds and an output y of the given type
-- reading r.
foldModuleOf :: Ty -> [NBind] -> NModule
foldModuleOf t binds =
  NModule
    { nmName = "fold"
    , nmDomain = sysDomain
    , nmInputs = [("x", bv 8)]
    , nmOutputs = [NOutput "y" t (AVar "r")]
    , nmBinds = binds
    , nmCertificate = testCertificate "Fold.fold_correct"
    }

-- | The module lowers to exactly these declarations, and the result
-- satisfies every invariant.
foldsTo :: NModule -> [Decl] -> Expectation
foldsTo nm decls = do
  modDecls <$> buildNetlist nm `shouldBe` Right decls
  validate <$> buildNetlist nm `shouldBe` Right []

x8 :: Atom
x8 = AVar "x"

zero8 :: HExpr
zero8 = HOperand (vconst 8 0)

assign8 :: Text -> HExpr -> Decl
assign8 n = DAssign (vec8 n)

-- | Width, a literal of that width, and hi >= lo below the width.
genExtract :: Gen (Natural, Integer, Natural, Natural)
genExtract = do
  w <- natIn 1 130
  v <- chooseInteger (0, 2 ^ w - 1)
  lo <- natIn 0 (w - 1)
  hi <- natIn lo (w - 1)
  pure (w, v, hi, lo)

-- | Width, shift amount around the width, shift direction.
genShift :: Gen (Natural, Natural, Bool)
genShift = do
  w <- natIn 1 70
  k <- natIn 0 (2 * w + 1)
  isLeft <- arbitrary
  pure (w, k, isLeft)

natIn :: Natural -> Natural -> Gen Natural
natIn lo hi = fromIntegral <$> chooseInteger (fromIntegral lo, fromIntegral hi)

----------------------------------------------------------------------
-- invariants

invariantsSpec :: Spec
invariantsSpec = do
  it "[nl-invariants] the validator accepts the hand-written example netlists" $ do
    validate counterNetlist `shouldBe` []
    validate macNetlist `shouldBe` []
    validate detectorNetlist `shouldBe` []
    validate (sliceNetlist (ref "s")) `shouldBe` []
  for_ mutants $ \(k, label, m) ->
    it ("[nl-invariants] the validator rejects " <> label <> " (invariant " <> show k <> ")") $
      invariantsBroken m `shouldBe` [k]
  it "[nl-invariants] the validator compares names case-insensitively" $
    invariantsBroken counterNetlist {modName = Ident "EN"} `shouldBe` [1, 2]
  modifyMaxSuccess (const 500) $
    prop "[nl-invariants] buildNetlist satisfies every invariant on random normal forms" $
      checkCoverage . forAll genNormal $ \nm -> case buildNetlist nm of
        Left e -> counterexample (show e) False
        Right m ->
          let bindNames = Set.fromList (fmap (unName . nbName) (nmBinds nm))
              renamed = any ((`Set.notMember` bindNames) . unIdent . netName . declNet) (modDecls m)
           in cover 50 renamed "a bind was renamed"
                . cover 2 (length (modDecls m) < length (nmBinds nm)) "a declaration was dropped"
                . cover 8 (any foldsShift (nmBinds nm)) "a shift was folded"
                . counterexample (show m)
                $ conjoin
                  [ validate m === []
                  , modName m === Ident (nmName nm)
                  , fmap netName (modInputs m) === [Ident (unName n) | (n, _) <- nmInputs nm]
                  , fmap (netName . outNet) (modOutputs m)
                      === [Ident (noName o) | o <- nmOutputs nm]
                  , counterexample "more declarations than binds" $
                      length (modDecls m) <= length (nmBinds nm)
                  ]
  where
    foldsShift b = case (nbRhs b, nbTy b) of
      (NPrim (BvShl k) _, TBitVec w) -> k >= w
      (NPrim (BvLshr k) _, TBitVec w) -> k >= w
      _ -> False

-- | One mutant of a valid netlist per invariant, breaking only that one.
mutants :: [(Int, String, Module)]
mutants =
  [ (1, "an uppercase module name", counterNetlist {modName = Ident "Counter"})
  , (2, "a module name equal to an input", counterNetlist {modName = Ident "en"})
  , (3, "an output driven by the clock", counterNetlist {modOutputs = [clockOutput]})
  , (4, "an 8-bit adder with a 4-bit constant", withInc (HBin BAdd (ref "s") (vconst 4 1)))
  , (5, "a combinational loop", withInc (HBin BAdd (ref "s_next") (vconst 8 1)))
  , (6, "a slice of a constant", sliceNetlist (vconst 8 5))
  , (7, "a shift by the operand width", withInc (HShl 8 (ref "s")))
  , (8, "an unread declared net", counterNetlist {modDecls = modDecls counterNetlist <> [spare]})
  ]
  where
    withInc e = counterNetlist {modDecls = fmap (replaceInc e) (modDecls counterNetlist)}
    replaceInc e d
      | netName (declNet d) == Ident "inc" = DAssign (vec8 "inc") e
      | otherwise = d
    spare = DAssign (Net (Ident "spare") HBit) (HOperand (ref "en"))
    clockOutput = Output (vec8 "count") (ref "clk")

-- | The counter with a 4-bit slice of the given operand driving a second
-- output.
sliceNetlist :: Operand -> Module
sliceNetlist o =
  counterNetlist
    { modOutputs = modOutputs counterNetlist <> [Output (Net (Ident "low") (HVec 4)) (ref "low4")]
    , modDecls = modDecls counterNetlist <> [DAssign (Net (Ident "low4") (HVec 4)) (HSlice 3 0 o)]
    }

-- | The invariants of "Gin.Netlist.Types", by number, that a module breaks,
-- each with a description of the violation.
validate :: Module -> [(Int, String)]
validate m =
  concat
    [ [(1, "illegal identifier " <> show i) | i <- defined <> refs, not (isLegalIdent (unIdent i))]
    , [(2, "duplicate name " <> show n) | n <- duplicates (fmap (Text.toLower . unIdent) defined)]
    , [(3, "dangling reference " <> show i) | i <- refs, i `Map.notMember` moduleNets m]
    , [(4, e) | e <- typeErrors m]
    , [ (5, "combinational cycle through " <> show (flattenSCC c))
      | c <- stronglyConnComp assignGraph
      , isCyclic c
      ]
    , [(6, "slice of a constant " <> show o) | HSlice _ _ o@(OConst _) <- exprs]
    , [ (7, "shift by " <> show k <> " of " <> show o)
      | (k, o) <- concatMap shiftOf exprs
      , Just (HVec w) <- [operandType m o]
      , k >= w
      ]
    , [ (8, "unread net " <> show (netName n))
      | n <- fmap declNet (modDecls m)
      , netName n `notElem` refs
      ]
    ]
  where
    defined =
      [modName m, modClock m, modReset m]
        <> fmap netName (modInputs m <> fmap outNet (modOutputs m) <> fmap declNet (modDecls m))
    refs = [i | ORef i <- moduleOperands m]
    exprs = [e | DAssign _ e <- modDecls m]
    assignGraph = [(n, n, [i | ORef i <- exprOperands e]) | DAssign (Net n _) e <- modDecls m]
    isCyclic = \case
      AcyclicSCC _ -> False
      _ -> True
    shiftOf = \case
      HShl k o -> [(k, o)]
      HLshr k o -> [(k, o)]
      _ -> []
    duplicates xs =
      [x | (x, c) <- Map.toList (Map.fromListWith (+) [(x, 1 :: Int) | x <- xs]), c > 1]

-- | Invariant 4: net widths, literals and the typing table on 'HExpr'.
-- Declarations and outputs with a dangling reference are left to
-- invariant 3.
typeErrors :: Module -> [String]
typeErrors m =
  ["zero-width net " <> show n | n <- nets, netType n == HVec 0]
    <> ["invalid literal " <> show l | l <- literals, not (validLit l)]
    <> [ "ill-typed declaration " <> show d
       | d <- modDecls m
       , resolved (declOperands d)
       , not (declTyped d)
       ]
    <> [ "ill-typed output " <> show o
       | o <- modOutputs m
       , resolved [outDriver o]
       , operandType m (outDriver o) /= Just (netType (outNet o))
       ]
  where
    nets = modInputs m <> fmap outNet (modOutputs m) <> fmap declNet (modDecls m)
    literals = [l | OConst l <- moduleOperands m] <> [l | DReg _ l _ <- modDecls m]
    resolved = all (isJust . operandType m)
    validLit = \case
      HLitBit _ -> True
      HLitVec w v -> w >= 1 && v >= 0 && v < 2 ^ w
    declTyped = \case
      DAssign n e -> exprType m e == Just (netType n)
      DReg n l o -> hlitType l == netType n && operandType m o == Just (netType n)

-- | The result type of a well-typed expression, per the table on 'HExpr'.
exprType :: Module -> HExpr -> Maybe HwType
exprType m = \case
  HOperand o -> ty o
  HUn UNot o -> ty o
  HUn UNeg o -> vec o
  HBin op a b -> do
    t <- ty a
    guard (ty b == Just t)
    case op of
      BAnd -> Just t
      BOr -> Just t
      BXor -> Just t
      BAdd -> t <$ width t
      BSub -> t <$ width t
      BMul -> t <$ width t
      BEq -> Just HBit
      BUlt -> HBit <$ width t
      BUle -> HBit <$ width t
  HMux c a b -> do
    guard (ty c == Just HBit)
    t <- ty a
    t <$ guard (ty b == Just t)
  HShl _ o -> vec o
  HLshr _ o -> vec o
  HSlice hi lo o -> do
    n <- width =<< ty o
    HVec (hi - lo + 1) <$ guard (n > hi && hi >= lo)
  HConcat a b -> do
    x <- width =<< ty a
    y <- width =<< ty b
    Just (HVec (x + y))
  HZext w o -> do
    n <- width =<< ty o
    HVec w <$ guard (w >= n)
  HBitToVec o -> HVec 1 <$ guard (ty o == Just HBit)
  where
    ty = operandType m
    vec o = ty o >>= \t -> t <$ width t
    width = \case
      HVec n -> Just n
      HBit -> Nothing

invariantsBroken :: Module -> [Int]
invariantsBroken = Set.toAscList . Set.fromList . fmap fst . validate

moduleOperands :: Module -> [Operand]
moduleOperands m = fmap outDriver (modOutputs m) <> concatMap declOperands (modDecls m)

declOperands :: Decl -> [Operand]
declOperands = \case
  DReg _ _ o -> [o]
  DAssign _ e -> exprOperands e

exprOperands :: HExpr -> [Operand]
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
-- random normal forms

-- | Modules in normal form: well-typed binds in a topological order,
-- registers that may read any bind, bind names that collide once
-- sanitized, and no bind that no output depends on.
genNormal :: Gen NModule
genNormal = do
  ins <- chooseInt (0, 3)
  outs <- chooseInt (1, 3)
  (inNames, outNames) <- splitAt ins . take (ins + outs) <$> shuffle portPool
  inputs <- traverse (\n -> (Name n,) <$> genTy) inNames
  top <- elements ["top", "dut", "core"]
  raw <- chooseInt (0, 16) >>= (`vectorOf` genBindName)
  binds <- genBinds (scopeOf inputs) (uniquify (Set.fromList (fmap fst inputs)) raw)
  let scope = scopeOf (inputs <> [(nbName b, nbTy b) | b <- binds])
  closed <- traverse (closeRegister scope) binds
  let recent = take 3 (reverse (fmap nbTy binds))
      outputTy = if null recent then genTy else frequency [(4, elements recent), (1, genTy)]
  outputs <- traverse (\o -> outputTy >>= \t -> NOutput o t <$> genAtom scope t) outNames
  pure
    NModule
      { nmName = top
      , nmDomain = sysDomain
      , nmInputs = inputs
      , nmOutputs = outputs
      , nmBinds = pruneDead outputs closed
      , nmCertificate = testCertificate "Random.random_correct"
      }

-- | Legal port names, distinct from the top names 'genNormal' picks.
portPool :: [Text]
portPool = ["a", "b", "x", "y", "en", "count", "data", "valid", "q", "s"]

genBindName :: Gen Text
genBindName = frequency [(3, elements trickyNames), (1, genRawName)]

trickyNames :: [Text]
trickyNames =
  [ ""
  , "_"
  , "x"
  , "X"
  , "x'"
  , "x.y"
  , "x_y"
  , "x__y"
  , "x_1"
  , "s"
  , "s_next"
  , "module"
  , "Module"
  , "gin"
  , "gin_x"
  , "GIN_X"
  , "1x"
  , "\220nit"
  , "clk"
  , "CLK"
  , "rst"
  , "top"
  , "dut"
  , "acc'"
  , "count"
  , "COUNT"
  , "en"
  , "n"
  , "n_1"
  , Text.replicate 70 "a"
  , Text.replicate 70 "a" <> "z"
  ]

-- | Make names unique and distinct from the inputs by appending primes,
-- which sanitizing removes again.
uniquify :: Set Name -> [Text] -> [Name]
uniquify _ [] = []
uniquify used (t : ts) = n : uniquify (Set.insert n used) ts
  where
    n = primed t
    primed c = if Name c `Set.member` used then primed (c <> "'") else Name c

genTy :: Gen Ty
genTy =
  frequency
    [ (3, pure TBool)
    , (4, pure (TBitVec 8))
    , (3, TBitVec <$> elements [1, 3, 16, 33, 64])
    ]

genValue :: Ty -> Gen Value
genValue = \case
  TBitVec w -> VBV w <$> chooseInteger (0, 2 ^ w - 1)
  _ -> VBool <$> arbitrary

-- | Variables in scope, by type.
scopeOf :: [(Name, Ty)] -> Map Ty [Name]
scopeOf vs = Map.fromListWith (<>) [(t, [n]) | (n, t) <- vs]

-- | An atom of the given type, preferring the most recent variables (the
-- scope lists them first) so that chains of binds stay live.
genAtom :: Map Ty [Name] -> Ty -> Gen Atom
genAtom scope t = case Map.findWithDefault [] t scope of
  [] -> ALit <$> genValue t
  vs ->
    frequency
      [ (4, AVar <$> elements (take 2 vs))
      , (2, AVar <$> elements vs)
      , (1, ALit <$> genValue t)
      ]

-- | Binds over the variables in scope and the binds before them.
genBinds :: Map Ty [Name] -> [Name] -> Gen [NBind]
genBinds _ [] = pure []
genBinds scope (n : ns) = do
  t <- genTy
  rhs <- genRhs scope t
  (NBind n t rhs :) <$> genBinds (Map.insertWith (<>) t [n] scope) ns

-- | A right-hand side of the given type. A register's argument is a
-- placeholder until 'closeRegister' picks it from every bind.
genRhs :: Map Ty [Name] -> Ty -> Gen NRhs
genRhs scope t = frequency (shared <> specific)
  where
    atom = genAtom scope
    atoms = traverse atom
    widths = [w | TBitVec w <- Map.keys scope]
    shared =
      [ (2, NMux <$> atom TBool <*> atom t <*> atom t)
      , (2, (`NReg` ALit (VBool False)) <$> genValue t)
      ]
    specific = case t of
      TBitVec w ->
        [ (3, NPrim <$> elements [BvAdd, BvSub, BvMul, BvAnd, BvOr, BvXor] <*> atoms [t, t])
        , (2, NPrim <$> elements [BvNeg, BvNot] <*> atoms [t])
        , (5, shiftAmount w >>= \k -> NPrim <$> elements [BvShl k, BvLshr k] <*> atoms [t])
        , (3, extract w)
        , (2, natIn 1 w >>= \n -> NPrim (BvZext w) <$> atoms [TBitVec n])
        ]
          <> [ (2, natIn 1 (w - 1) >>= \k -> NPrim BvConcat <$> atoms [TBitVec k, TBitVec (w - k)])
             | w >= 2
             ]
          <> [(1, NPrim BvOfBool <$> atoms [TBool]) | w == 1]
      _ ->
        [ (3, NPrim <$> elements [BoolAnd, BoolOr, BoolXor, BoolEq] <*> atoms [TBool, TBool])
        , (1, NPrim BoolNot <$> atoms [TBool])
        , ( 3
          , do
              n <- elements (widths <> [1, 8])
              op <- elements [BvEq, BvUlt, BvUle]
              NPrim op <$> atoms [TBitVec n, TBitVec n]
          )
        ]
    shiftAmount w = oneof [natIn 0 (w - 1), natIn w (w + 2)]
    extract w = do
      n <- elements (filter (>= w) widths <> [w .. w + 4])
      lo <- natIn 0 (n - w)
      NPrim (BvExtract (lo + w - 1) lo) <$> atoms [TBitVec n]

closeRegister :: Map Ty [Name] -> NBind -> Gen NBind
closeRegister scope b = case nbRhs b of
  NReg v _ -> (\a -> b {nbRhs = NReg v a}) <$> genAtom scope (nbTy b)
  _ -> pure b

-- | Keep only the binds some output depends on.
pruneDead :: [NOutput] -> [NBind] -> [NBind]
pruneDead outputs binds = filter ((`Set.member` live) . nbName) binds
  where
    deps = Map.fromList [(nbName b, [n | AVar n <- rhsAtoms (nbRhs b)]) | b <- binds]
    live = reach Set.empty [n | NOutput _ _ (AVar n) <- outputs]
    reach seen = \case
      [] -> seen
      n : rest
        | n `Set.member` seen -> reach seen rest
        | otherwise -> reach (Set.insert n seen) (Map.findWithDefault [] n deps <> rest)

rhsAtoms :: NRhs -> [Atom]
rhsAtoms = \case
  NPrim _ as -> as
  NMux c t e -> [c, t, e]
  NReg _ a -> [a]
  NAtom a -> [a]

----------------------------------------------------------------------
-- precondition violations

preconditionSpec :: Spec
preconditionSpec = do
  for_ violations $ \(label, nm, culprit) ->
    it ("reports " <> label <> " as a netlist error") $
      buildNetlist nm `shouldFailMentioning` culprit
  it "names the offending bind in the error context" $
    errContext <$> either Just (const Nothing) (buildNetlist (singleBind (bv 8) (NPrim BvAdd [a8])))
      `shouldBe` Just ["in bind " <> tshow ("r" :: Text)]

-- | Label, a module that breaks the builder's precondition, and a word the
-- error message must contain.
violations :: [(String, NModule, Text)]
violations =
  [ ("an unknown variable", singleBind (bv 8) (NPrim BvAdd [AVar "nope", a8]), "nope")
  , ("a non-scalar bind type", singleBind (TProd [bv 8, bv 8]) (NAtom a8), "TProd")
  , ("a zero-width type", singleBind (TBitVec 0) (NAtom a8), "TBitVec 0")
  , ("a signal primitive", singleBind (bv 8) (NPrim (SigRegister (VBV 8 0)) [a8]), "sig.register")
  , ("an unsaturated primitive", singleBind (bv 8) (NPrim BvAdd [a8]), "bv.add")
  , ("bv.extract with hi below lo", singleBind (bv 4) (NPrim (BvExtract 2 5) [a8]), "bv.extract")
  , ("bv.extract past the operand width", singleBind (bv 9) (NPrim (BvExtract 8 0) [a8]), "8 0")
  , ("a shift of a Bool", singleBind TBool (NPrim (BvShl 1) [pB]), "TBool")
  , ("a tuple register value", singleBind TBool (NReg pair pB), "Tuple")
  , ("an out-of-range literal", singleBind (bv 8) (NAtom (lit8 256)), "256")
  , ("a duplicated bind name", (singleBind (bv 8) (NAtom a8)) {nmBinds = [rBind, rBind]}, "\"r\"")
  , ("a bind named like an input", (singleBind (bv 8) (NAtom a8)) {nmBinds = [aBind]}, "\"a\"")
  ]
  where
    rBind = NBind "r" (bv 8) (NAtom a8)
    aBind = NBind "a" (bv 8) (NAtom b8)
    pair = VTuple [VBool True, VBool False]

-- | The build fails in the netlist stage with a message containing the
-- given text.
shouldFailMentioning :: Either GinError Module -> Text -> Expectation
shouldFailMentioning result needle = case result of
  Left e -> do
    errStage e `shouldBe` StNetlist
    errMessage e `shouldSatisfy` Text.isInfixOf needle
  Right m -> expectationFailure ("expected a netlist error, got " <> show m)
