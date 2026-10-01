-- | Tests for the reference simulators ('Gin.Sim') and the primitive
-- semantics ('Gin.Sim.Prim') specified in @docs/semantics.md@.
module Gin.SimSpec (spec) where

import Data.Foldable (for_)
import Data.Text (Text)
import Data.Text qualified as Text
import Gin.Core.Syntax
import Gin.Error (GinError (..), Stage (..), renderError)
import Gin.Sim.Prim (evalPrim)
import Numeric.Natural (Natural)
import Test.Hspec
import Test.QuickCheck

spec :: Spec
spec =
  describe "evalPrim" $ do
    primTableSpec
    primRejectSpec
    primLawSpec

----------------------------------------------------------------------
-- Primitive table

-- | One case: description, operation, arguments, expected result.
type PrimCase = (String, PrimOp, [Value], Value)

-- | Every row of the primitive table in @docs/semantics.md@ that
-- 'evalPrim' implements, with its edge cases.
primTable :: [(String, [PrimCase])]
primTable =
  [
    ( "bool.and/or/xor/not follow their truth tables"
    , truthTable "and" BoolAnd [False, False, False, True]
        <> truthTable "or" BoolOr [False, True, True, True]
        <> truthTable "xor" BoolXor [False, True, True, False]
        <> [ ("not False", BoolNot, [VBool False], VBool True)
           , ("not True", BoolNot, [VBool True], VBool False)
           ]
    )
  , ("bool.eq is equality on Bool", truthTable "eq" BoolEq [True, False, False, True])
  ,
    ( "bv.add is (a + b) mod 2^n"
    ,
      [ ("3 + 4", BvAdd, [b8 3, b8 4], b8 7)
      , ("200 + 100 wraps", BvAdd, [b8 200, b8 100], b8 44)
      , ("255 + 1 wraps to 0", BvAdd, [b8 255, b8 1], b8 0)
      , ("width 1: 1 + 1 = 0", BvAdd, [VBV 1 1, VBV 1 1], VBV 1 0)
      , ("width 65 carries past 64 bits", BvAdd, [VBV 65 (2 ^ i64 - 1), VBV 65 1], VBV 65 (2 ^ i64))
      , ("max width: all ones + 1 = 0", BvAdd, [VBV 4096 (2 ^ i4096 - 1), VBV 4096 1], VBV 4096 0)
      ]
    )
  ,
    ( "bv.sub is (a - b) mod 2^n"
    ,
      [ ("7 - 3", BvSub, [b8 7, b8 3], b8 4)
      , ("3 - 7 wraps", BvSub, [b8 3, b8 7], b8 252)
      , ("0 - 1 is all ones", BvSub, [b8 0, b8 1], b8 255)
      , ("x - x = 0", BvSub, [b8 200, b8 200], b8 0)
      , ("width 1: 0 - 1 = 1", BvSub, [VBV 1 0, VBV 1 1], VBV 1 1)
      ]
    )
  ,
    ( "bv.mul is (a * b) mod 2^n"
    ,
      [ ("3 * 4", BvMul, [b8 3, b8 4], b8 12)
      , ("16 * 16 wraps to 0", BvMul, [b8 16, b8 16], b8 0)
      , ("255 * 255 wraps to 1", BvMul, [b8 255, b8 255], b8 1)
      , ("width 16: 255 * 255", BvMul, [VBV 16 255, VBV 16 255], VBV 16 65025)
      , ("width 1: 1 * 1", BvMul, [VBV 1 1, VBV 1 1], VBV 1 1)
      ]
    )
  ,
    ( "bv.neg is (2^n - a) mod 2^n"
    ,
      [ ("neg 0 = 0", BvNeg, [b8 0], b8 0)
      , ("neg 1 = 255", BvNeg, [b8 1], b8 255)
      , ("neg 128 = 128", BvNeg, [b8 128], b8 128)
      , ("neg 255 = 1", BvNeg, [b8 255], b8 1)
      , ("width 1: neg 1 = 1", BvNeg, [VBV 1 1], VBV 1 1)
      ]
    )
  ,
    ( "bv.and/or/xor are bitwise"
    ,
      [ ("1100 and 1010", BvAnd, [VBV 4 12, VBV 4 10], VBV 4 8)
      , ("1100 or 1010", BvOr, [VBV 4 12, VBV 4 10], VBV 4 14)
      , ("1100 xor 1010", BvXor, [VBV 4 12, VBV 4 10], VBV 4 6)
      , ("x and 0", BvAnd, [b8 255, b8 0], b8 0)
      , ("x xor x", BvXor, [b8 165, b8 165], b8 0)
      ,
        ( "width 100: or of top and bottom bits"
        , BvOr
        , [VBV 100 (2 ^ i99), VBV 100 1]
        , VBV 100 (2 ^ i99 + 1)
        )
      ]
    )
  ,
    ( "bv.not is 2^n - 1 - a"
    ,
      [ ("not 0", BvNot, [b8 0], b8 255)
      , ("not 255", BvNot, [b8 255], b8 0)
      , ("width 4: not 1010", BvNot, [VBV 4 10], VBV 4 5)
      , ("width 1: not 0", BvNot, [VBV 1 0], VBV 1 1)
      ]
    )
  ,
    ( "bv.shl k is (a * 2^k) mod 2^n, and 0 when k >= n"
    ,
      [ ("width 4: 1001 << 1 drops the top bit", BvShl 1, [VBV 4 9], VBV 4 2)
      , ("<< 0 is the identity", BvShl 0, [b8 165], b8 165)
      , ("0xff << 3", BvShl 3, [b8 255], b8 248)
      , ("1 << 7 reaches the top bit", BvShl 7, [b8 1], b8 128)
      , ("<< n is 0", BvShl 8, [b8 255], b8 0)
      , ("<< 1000 is 0", BvShl 1000, [b8 255], b8 0)
      , ("<< 2^40 is 0", BvShl (2 ^ i40), [b8 255], b8 0)
      ]
    )
  ,
    ( "bv.lshr k is a div 2^k, and 0 when k >= n"
    ,
      [ ("width 4: 1001 >> 1", BvLshr 1, [VBV 4 9], VBV 4 4)
      , (">> 0 is the identity", BvLshr 0, [b8 165], b8 165)
      , ("0x80 >> 1 does not extend the sign", BvLshr 1, [b8 128], b8 64)
      , ("0xff >> 7", BvLshr 7, [b8 255], b8 1)
      , (">> n is 0", BvLshr 8, [b8 255], b8 0)
      , (">> 1000 is 0", BvLshr 1000, [b8 255], b8 0)
      , (">> 2^40 is 0", BvLshr (2 ^ i40), [b8 255], b8 0)
      ]
    )
  ,
    ( "bv.eq/ult/ule are unsigned comparisons"
    ,
      [ ("3 == 3", BvEq, [b8 3, b8 3], VBool True)
      , ("3 == 4", BvEq, [b8 3, b8 4], VBool False)
      , ("3 < 4", BvUlt, [b8 3, b8 4], VBool True)
      , ("4 < 3", BvUlt, [b8 4, b8 3], VBool False)
      , ("3 < 3", BvUlt, [b8 3, b8 3], VBool False)
      , ("255 < 0 is false (unsigned)", BvUlt, [b8 255, b8 0], VBool False)
      , ("0 < 255 is true (unsigned)", BvUlt, [b8 0, b8 255], VBool True)
      , ("3 <= 3", BvUle, [b8 3, b8 3], VBool True)
      , ("3 <= 4", BvUle, [b8 3, b8 4], VBool True)
      , ("4 <= 3", BvUle, [b8 4, b8 3], VBool False)
      ]
    )
  ,
    ( "bv.concat a b is a * 2^(width b) + b"
    ,
      [ ("the first argument supplies the high bits", BvConcat, [VBV 4 10, b8 91], VBV 12 2651)
      , ("1 ++ 0", BvConcat, [VBV 1 1, VBV 1 0], VBV 2 2)
      , ("0 ++ 1", BvConcat, [VBV 1 0, VBV 1 1], VBV 2 1)
      , ("zero high half", BvConcat, [b8 0, b8 255], VBV 16 255)
      , ("result at the maximum width", BvConcat, [VBV 4095 0, VBV 1 1], VBV 4096 1)
      ]
    )
  ,
    ( "bv.extract hi lo is (a div 2^lo) mod 2^(hi - lo + 1)"
    ,
      [ ("high nibble of 0xa5", BvExtract 7 4, [b8 165], VBV 4 10)
      , ("low nibble of 0xa5", BvExtract 3 0, [b8 165], VBV 4 5)
      , ("every bit", BvExtract 7 0, [b8 165], b8 165)
      , ("bit 0 alone", BvExtract 0 0, [b8 1], VBV 1 1)
      , ("the top bit alone", BvExtract 7 7, [b8 128], VBV 1 1)
      , ("a middle field", BvExtract 6 1, [b8 126], VBV 6 63)
      ]
    )
  ,
    ( "bv.zext m keeps the value at width m"
    ,
      [ ("8 to 16 bits", BvZext 16, [b8 255], VBV 16 255)
      , ("to the same width", BvZext 8, [b8 255], b8 255)
      , ("1 to the maximum width", BvZext 4096, [VBV 1 1], VBV 4096 1)
      ]
    )
  ,
    ( "bv.ofBool is 1 or 0 at width 1"
    ,
      [ ("True", BvOfBool, [VBool True], VBV 1 1)
      , ("False", BvOfBool, [VBool False], VBV 1 0)
      ]
    )
  ]
  where
    i40, i64, i99, i4096 :: Int
    i40 = 40
    i64 = 64
    i99 = 99
    i4096 = 4096

truthTable :: String -> PrimOp -> [Bool] -> [PrimCase]
truthTable name op outs =
  [ (name <> " " <> show a <> " " <> show b, op, [VBool a, VBool b], VBool o)
  | ((a, b), o) <- zip [(False, False), (False, True), (True, False), (True, True)] outs
  ]

primTableSpec :: Spec
primTableSpec =
  for_ primTable $ \(row, cases) ->
    it ("[sim-prim-table] " <> row) $
      [(name, evalPrim op args) | (name, op, args, _) <- cases]
        `shouldBe` [(name, Right expected) | (name, _, _, expected) <- cases]

primRejectSpec :: Spec
primRejectSpec = do
  it "[sim-prim-table] bv.extract rejects bounds outside the operand" $ do
    evalPrim (BvExtract 8 0) [b8 1] `shouldBeSimError` "bv.extract"
    evalPrim (BvExtract 2 3) [b8 1] `shouldBeSimError` "bv.extract"
  it "[sim-prim-table] bv.zext rejects a narrower or over-wide target" $ do
    evalPrim (BvZext 4) [b8 1] `shouldBeSimError` "bv.zext"
    evalPrim (BvZext 4097) [b8 1] `shouldBeSimError` "bv.zext"
  it "[sim-prim-table] bv.concat rejects a result wider than the maximum width" $
    evalPrim BvConcat [VBV 4096 0, VBV 1 0] `shouldBeSimError` "bv.concat"
  it "rejects signal primitives, which are not combinational" $ do
    evalPrim SigPure [b8 1] `shouldBeSimError` "sig.pure"
    evalPrim (SigLift 1) [b8 1, b8 1] `shouldBeSimError` "sig.lift"
    evalPrim (SigRegister (b8 0)) [b8 1] `shouldBeSimError` "sig.register"
    evalPrim (SigMealy (b8 0)) [b8 0, b8 1] `shouldBeSimError` "sig.mealy"
  it "rejects the wrong number of arguments" $ do
    evalPrim BvAdd [b8 1] `shouldBeSimError` "bv.add"
    evalPrim BvAdd [b8 1, b8 2, b8 3] `shouldBeSimError` "bv.add"
    evalPrim BoolNot [] `shouldBeSimError` "bool.not"
    evalPrim BvNot [b8 1, b8 1] `shouldBeSimError` "bv.not"
  it "rejects ill-typed arguments" $ do
    evalPrim BvAdd [b8 1, VBV 4 1] `shouldBeSimError` "bv.add"
    evalPrim BvEq [b8 1, VBV 9 1] `shouldBeSimError` "bv.eq"
    evalPrim BoolAnd [VBV 1 1, VBool True] `shouldBeSimError` "bool.and"
    evalPrim BvAdd [VBool True, VBool False] `shouldBeSimError` "bv.add"
    evalPrim BvOfBool [VBV 1 1] `shouldBeSimError` "bv.ofBool"
    evalPrim BvNot [VTuple [b8 1, b8 2]] `shouldBeSimError` "bv.not"
    evalPrim BvConcat [VBool True, b8 1] `shouldBeSimError` "bv.concat"
  it "rejects values that break the representation invariant" $ do
    evalPrim BvAdd [VBV 8 256, b8 1] `shouldBeSimError` "bv.add"
    evalPrim BvNot [VBV 8 (-1)] `shouldBeSimError` "bv.not"
    evalPrim BvNeg [VBV 0 0] `shouldBeSimError` "bv.neg"
    evalPrim BvXor [VBV 4097 0, VBV 4097 0] `shouldBeSimError` "bv.xor"

----------------------------------------------------------------------
-- Primitive laws

chooseNat :: (Natural, Natural) -> Gen Natural
chooseNat (lo, hi) = fromInteger <$> chooseInteger (toInteger lo, toInteger hi)

-- | Mostly small widths, some wider than a machine word, and the maximum.
genWidth :: Gen Natural
genWidth =
  frequency
    [(6, chooseNat (1, 8)), (3, chooseNat (9, 130)), (1, elements [maxWidth - 1, maxWidth])]

-- | A payload of the given width, biased towards the boundaries.
genPayload :: Natural -> Gen Integer
genPayload n = frequency [(1, elements [0, 1, top, 2 ^ (n - 1)]), (3, chooseInteger (0, top))]
  where
    top = 2 ^ n - 1

genBV :: Natural -> Gen Value
genBV n = VBV n <$> genPayload n

-- | A well-typed application of a combinational prim and its result type.
genPrimCase :: Gen (PrimOp, [Value], Ty)
genPrimCase = do
  n <- genWidth
  let vec = genBV n
      bool = VBool <$> arbitrary
  oneof
    [ do
        op <- elements [BoolAnd, BoolOr, BoolXor, BoolEq]
        args <- vectorOf 2 bool
        pure (op, args, TBool)
    , (\a -> (BoolNot, [a], TBool)) <$> bool
    , do
        op <- elements [BvAdd, BvSub, BvMul, BvAnd, BvOr, BvXor]
        args <- vectorOf 2 vec
        pure (op, args, TBitVec n)
    , do
        op <- elements [BvNeg, BvNot]
        a <- vec
        pure (op, [a], TBitVec n)
    , do
        k <- chooseNat (0, n + 3)
        op <- elements [BvShl k, BvLshr k]
        a <- vec
        pure (op, [a], TBitVec n)
    , do
        op <- elements [BvEq, BvUlt, BvUle]
        args <- vectorOf 2 vec
        pure (op, args, TBool)
    , do
        m <- chooseNat (1, 130)
        a <- genBV (min n 130)
        b <- genBV m
        pure (BvConcat, [a, b], TBitVec (min n 130 + m))
    , do
        lo <- chooseNat (0, n - 1)
        hi <- chooseNat (lo, n - 1)
        a <- vec
        pure (BvExtract hi lo, [a], TBitVec (hi - lo + 1))
    , do
        m <- chooseNat (n, min maxWidth (n + 70))
        a <- vec
        pure (BvZext m, [a], TBitVec m)
    , (\a -> (BvOfBool, [a], TBitVec 1)) <$> bool
    ]

primLawSpec :: Spec
primLawSpec = do
  it "[sim-prim-laws] bv.sub undoes bv.add" $
    property $
      forAll genWidth $ \n -> forAll (genBV n) $ \a -> forAll (genBV n) $ \b ->
        (evalPrim BvAdd [a, b] >>= \s -> evalPrim BvSub [s, b]) === Right a
  it "[sim-prim-laws] bv.add undoes bv.sub" $
    property $
      forAll genWidth $ \n -> forAll (genBV n) $ \a -> forAll (genBV n) $ \b ->
        (evalPrim BvSub [a, b] >>= \d -> evalPrim BvAdd [d, b]) === Right a
  it "[sim-prim-laws] a value plus its bv.neg is zero" $
    property $
      forAll genWidth $ \n -> forAll (genBV n) $ \a ->
        (evalPrim BvNeg [a] >>= \m -> evalPrim BvAdd [a, m]) === Right (VBV n 0)
  it "[sim-prim-laws] bv.extract recovers both halves of a bv.concat" $
    property $
      forAll (chooseNat (1, 200)) $ \na -> forAll (chooseNat (1, 200)) $ \nb ->
        forAll (genBV na) $ \a -> forAll (genBV nb) $ \b ->
          let halves c =
                traverse
                  (\(hi, lo) -> evalPrim (BvExtract hi lo) [c])
                  [(na + nb - 1, nb), (nb - 1, 0)]
           in (evalPrim BvConcat [a, b] >>= halves) === Right [a, b]
  it "[sim-prim-laws] bv.concat of the two fields of a split restores the value" $
    property $
      forAll (chooseNat (2, 300)) $ \n -> forAll (chooseNat (1, n - 1)) $ \k ->
        forAll (genBV n) $ \x ->
          let field (hi, lo) = evalPrim (BvExtract hi lo) [x]
              fields = traverse field [(n - 1, k), (k - 1, 0)]
           in (fields >>= evalPrim BvConcat) === Right x
  it "[sim-prim-laws] bv.zext preserves the value" $
    property $
      forAll genWidth $ \n -> forAll (chooseNat (n, maxWidth)) $ \m ->
        forAll (genPayload n) $ \a ->
          evalPrim (BvZext m) [VBV n a] === Right (VBV m a)
  it "[sim-prim-laws] every result is a valid value of the result type" $
    property $
      forAll genPrimCase $ \(op, args, ty) -> case evalPrim op args of
        Right r -> counterexample (show r) (validValue r .&&. valueTy r === ty)
        Left e -> counterexample (Text.unpack (renderError e)) False

----------------------------------------------------------------------
-- Building blocks for small programs

b8 :: Integer -> Value
b8 = VBV 8

-- | The result is a simulation error whose rendering mentions @needle@.
shouldBeSimError :: (Show a) => Either GinError a -> Text -> Expectation
shouldBeSimError result needle = case result of
  Left e -> do
    errStage e `shouldBe` StSim
    renderError e `shouldSatisfy` Text.isInfixOf needle
  Right r -> expectationFailure ("expected a simulation error, got " <> show r)
