-- | Tests for the reference simulators ('Gin.Sim') and the primitive
-- semantics ('Gin.Sim.Prim') specified in @docs/semantics.md@.
module Gin.SimSpec (spec) where

import Control.Exception (evaluate)
import Data.Either (isRight)
import Data.Foldable (for_)
import Data.Text (Text)
import Data.Text qualified as Text
import Gin.Core.Check (checkProgram)
import Gin.Core.Normal
import Gin.Core.Syntax
import Gin.Error (GinError (..), Stage (..), renderError)
import Gin.Examples
import Gin.Sim (isBudgetError, simulateCore, simulateNormal)
import Gin.Sim.Prim (evalPrim)
import Gin.Vectors (Cycle (..), Vectors (..), maxCycles)
import Numeric.Natural (Natural)
import System.Timeout (timeout)
import Test.Hspec
import Test.QuickCheck

spec :: Spec
spec = do
  describe "evalPrim" $ do
    primTableSpec
    primRejectSpec
    primLawSpec
  describe "simulateCore" $ do
    coreExampleSpec
    coreSemanticsSpec
    coreLetRecSpec
    coreLimitSpec
  describe "simulateNormal" normalSpec
  describe "both simulators" $ do
    multiOutputSpec
    zeroInputSpec
    rowsRejectSpec

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
-- Example circuits

examples :: [(String, Program, NModule, Vectors)]
examples =
  [ ("counter", counterProgram, counterNormal, counterVectors)
  , ("mac", macProgram, macNormal, macVectors)
  , ("detector", detectorProgram, detectorNormal, detectorVectors)
  ]

inputRows, outputRows :: Vectors -> [[Value]]
inputRows = fmap cycInputs . vecCycles
outputRows = fmap cycOutputs . vecCycles

coreExampleSpec :: Spec
coreExampleSpec = do
  for_ examples $ \(name, prog, _, vs) ->
    it ("[sim-core-examples] reproduces the " <> name <> " vectors") $
      simulateCore prog (inputRows vs) `shouldBe` Right (outputRows vs)
  it "[sim-core-examples] simulates exactly one cycle per input row" $
    for_ [0 .. 8] $ \k ->
      simulateCore counterProgram (take k (inputRows counterVectors))
        `shouldBe` Right (take k (outputRows counterVectors))

----------------------------------------------------------------------
-- Building blocks for small programs

prim :: PrimOp -> [Ty] -> Ty -> Expr
prim op args res = EPrim op (tFuns args res)

var :: Text -> Expr
var = EVar . Name

b4, b8 :: Integer -> Value
b4 = VBV 4
b8 = VBV 8

-- | A binary bit-vector prim of width @n@ applied to two operands.
bvBin :: PrimOp -> Natural -> Expr -> Expr -> Expr
bvBin op n a b = EApp (prim op [bv n, bv n] (bv n)) [a, b]

bvEq8 :: Expr -> Expr -> Expr
bvEq8 a b = EApp (prim BvEq [bv 8, bv 8] TBool) [a, b]

-- | @bv.add@ at width @n@, unapplied.
addPrim :: Natural -> Expr
addPrim n = prim BvAdd [bv n, bv n] (bv n)

-- | @bv.add 1@ at width @n@: a partially applied prim.
incr :: Natural -> Expr
incr n = EApp (addPrim n) [ELit (VBV n 1)]

-- | @sig.lift k f s1 .. sk@ with element types @args@ and result @res@.
liftE :: [Ty] -> Ty -> Expr -> [Expr] -> Expr
liftE args res f ss =
  EApp
    (prim (SigLift (fromIntegral (length args))) (tFuns args res : fmap sig args) (sig res))
    (f : ss)

registerE :: Value -> Expr -> Expr
registerE v s = EApp (prim (SigRegister v) [sig t] (sig t)) [s]
  where
    t = valueTy v

pureE :: Ty -> Expr -> Expr
pureE t x = EApp (prim SigPure [t] (sig t)) [x]

-- | @sig.mealy v f s@ with input type @i@ and output type @o@.
mealyE :: Value -> Ty -> Ty -> Expr -> Expr -> Expr
mealyE v i o f s = EApp (prim (SigMealy v) [tFuns [st, i] (TProd [st, o]), sig i] (sig o)) [f, s]
  where
    st = valueTy v

-- | Right-nested product of the output types, as a top entity returns it.
outputSpine :: [Ty] -> Ty
outputSpine = \case
  [t] -> t
  t : ts -> TProd [t, outputSpine ts]
  [] -> TProd []

-- | A program whose top entity @t@ is the def @T.top@ with the given body.
programWith :: [Port] -> [Port] -> Expr -> [Def] -> Program
programWith ins outs body defs =
  Program
    { progProducer = Producer "gin-sim-spec" "n/a"
    , progTop =
        TopEntity
          { topName = "t"
          , topDomain = sysDomain
          , topInputs = ins
          , topOutputs = outs
          , topDef = "T.top"
          }
    , progDefs = Def "T.top" topTy body : defs
    , progCertificate = testCertificate "T.top_correct"
    }
  where
    topTy = tFuns (fmap (sig . portTy) ins) (sig (outputSpine (fmap portTy outs)))

topProgram :: [Port] -> [Port] -> Expr -> Program
topProgram ins outs body = programWith ins outs body []

-- | Lambda over the input signals of the given ports.
overPorts :: [Port] -> Expr -> Expr
overPorts ps = ELam [(Name (portName p), sig (portTy p)) | p <- ps]

normalModule :: [(Name, Ty)] -> [NOutput] -> [NBind] -> NModule
normalModule ins outs binds =
  NModule
    { nmName = "t"
    , nmDomain = sysDomain
    , nmInputs = ins
    , nmOutputs = outs
    , nmBinds = binds
    , nmCertificate = testCertificate "T.top_correct"
    }

-- | The result is a simulation error whose rendering mentions @needle@.
shouldBeSimError :: (Show a) => Either GinError a -> Text -> Expectation
shouldBeSimError result needle = case result of
  Left e -> do
    errStage e `shouldBe` StSim
    renderError e `shouldSatisfy` Text.isInfixOf needle
  Right r -> expectationFailure ("expected a simulation error, got " <> show r)

-- | Evaluate a result completely within 'timeLimit', so a simulator that
-- loops fails the test instead of hanging the suite.
settled :: (Show a) => a -> IO a
settled x =
  timeout (timeLimit * 1000000) (evaluate (length (show x))) >>= \case
    Just _ -> pure x
    Nothing ->
      x <$ expectationFailure ("simulation did not finish within " <> show timeLimit <> " s")

-- | Seconds a simulation in these tests may take. The slowest takes a few
-- seconds when built without optimization and far less with it; the bound
-- is generous so that only a simulation that does not end, or one that
-- became far slower, fails, even on a loaded machine.
timeLimit :: Int
timeLimit = 60

----------------------------------------------------------------------
-- Core IR semantics

bv8Ports :: [Text] -> [Port]
bv8Ports = fmap (`Port` bv 8)

ifPorts :: [Port]
ifPorts = [Port "c" TBool, Port "a" (bv 8), Port "b" (bv 8)]

ifProgram :: Program
ifProgram =
  topProgram ifPorts [Port "o" (bv 8)] . overPorts ifPorts $
    liftE
      [TBool, bv 8, bv 8]
      (bv 8)
      (ELam [("x", TBool), ("y", bv 8), ("z", bv 8)] (EIf (var "x") (var "y") (var "z")))
      [var "c", var "a", var "b"]

ifRows, ifOutputs :: [[Value]]
ifRows =
  [ [VBool True, b8 1, b8 2]
  , [VBool False, b8 1, b8 2]
  , [VBool True, b8 255, b8 0]
  , [VBool False, b8 255, b8 0]
  ]
ifOutputs = [[b8 1], [b8 2], [b8 255], [b8 0]]

-- | Higher-order global applied inside a lifted function.
twiceProgram :: Program
twiceProgram =
  programWith
    (bv8Ports ["x"])
    (bv8Ports ["o"])
    ( overPorts (bv8Ports ["x"]) $
        liftE
          [bv 8]
          (bv 8)
          (ELam [("v", bv 8)] (EApp (EGlobal "T.twice") [incr 8, var "v"]))
          [var "x"]
    )
    [Def "T.twice" (tFuns [TFun (bv 8) (bv 8), bv 8] (bv 8)) twice]
  where
    twice =
      ELam [("f", TFun (bv 8) (bv 8)), ("y", bv 8)] $
        EApp (var "f") [EApp (var "f") [var "y"]]

coreSemanticsSpec :: Spec
coreSemanticsSpec = do
  it "[sim-prim-table] if c t e is t when c holds and e otherwise" $
    simulateCore ifProgram ifRows `shouldBe` Right ifOutputs
  it "[sim-prim-table] sig.pure x is x at every cycle" $ do
    let prog = topProgram [] (bv8Ports ["o"]) (pureE (bv 8) (ELit (b8 42)))
    simulateCore prog (replicate 3 []) `shouldBe` Right (replicate 3 [b8 42])
  it "[sim-prim-table] sig.lift 3 f applies f to the three inputs of each cycle" $ do
    let ports = bv8Ports ["a", "b", "c"]
        f =
          ELam [("x", bv 8), ("y", bv 8), ("z", bv 8)] $
            bvBin BvAdd 8 (var "x") (bvBin BvMul 8 (var "y") (var "z"))
        prog =
          topProgram ports (bv8Ports ["o"]) . overPorts ports $
            liftE [bv 8, bv 8, bv 8] (bv 8) f [var "a", var "b", var "c"]
    simulateCore prog [[b8 2, b8 3, b8 4], [b8 255, b8 16, b8 16], [b8 1, b8 255, b8 255]]
      `shouldBe` Right [[b8 14], [b8 255], [b8 2]]
  it "[sim-prim-table] sig.lift accepts a bare or partially applied prim as the function" $ do
    let ports = bv8Ports ["x", "y"]
        bare =
          topProgram ports (bv8Ports ["o"]) . overPorts ports $
            liftE [bv 8, bv 8] (bv 8) (addPrim 8) [var "x", var "y"]
        partial =
          topProgram ports (bv8Ports ["o"]) . overPorts ports $
            liftE [bv 8] (bv 8) (incr 8) [var "y"]
    simulateCore bare [[b8 3, b8 4], [b8 255, b8 1]] `shouldBe` Right [[b8 7], [b8 0]]
    simulateCore partial [[b8 3, b8 4], [b8 255, b8 255]] `shouldBe` Right [[b8 5], [b8 0]]
  it "sig.register v is v at cycle 0 and the previous input afterwards" $ do
    let prog =
          topProgram (bv8Ports ["x"]) (bv8Ports ["o"]) . overPorts (bv8Ports ["x"]) $
            registerE (b8 7) (var "x")
    simulateCore prog [[b8 1], [b8 2], [b8 3]] `shouldBe` Right [[b8 7], [b8 1], [b8 2]]
  it "applies a higher-order global inside a lifted function" $
    simulateCore twiceProgram [[b8 0], [b8 254]] `shouldBe` Right [[b8 2], [b8 0]]
  it "passes a tuple of signals through a non-recursive let" $ do
    let ports = bv8Ports ["a", "b"]
        prog =
          topProgram ports (bv8Ports ["o"]) . overPorts ports $
            ELet
              False
              [ Bind "p" (TProd [sig (bv 8), sig (bv 8)]) (ETuple [var "a", var "b"])
              , Bind "q" (sig (bv 8)) (EProj 1 (var "p"))
              ]
              ( liftE
                  [bv 8, bv 8]
                  (bv 8)
                  (addPrim 8)
                  [EProj 0 (var "p"), registerE (b8 0) (var "q")]
              )
    simulateCore prog [[b8 1, b8 10], [b8 2, b8 20]] `shouldBe` Right [[b8 1], [b8 12]]
  it "rejects a program whose top def is missing" $
    simulateCore counterProgram {progDefs = []} [[VBool True]] `shouldBeSimError` "Counter.counter"
  it "rejects a top def whose result does not match the output ports" $ do
    let prog = topProgram (bv8Ports ["x"]) [Port "o" TBool] (overPorts (bv8Ports ["x"]) (var "x"))
    simulateCore prog [[b8 1]] `shouldBeSimError` "cycle 0"
  it "reports an ill-typed lifted function in the cycle that evaluates it" $ do
    let f =
          ELam [("v", bv 8)] $
            EIf
              (bvEq8 (var "v") (ELit (b8 3)))
              (bvBin BvAdd 8 (var "v") (ELit (VBool True)))
              (var "v")
        prog =
          topProgram (bv8Ports ["x"]) (bv8Ports ["o"]) . overPorts (bv8Ports ["x"]) $
            liftE [bv 8] (bv 8) f [var "x"]
    simulateCore prog [[b8 1], [b8 2]] `shouldBe` Right [[b8 1], [b8 2]]
    simulateCore prog [[b8 1], [b8 2], [b8 3]] `shouldBeSimError` "cycle 2"

----------------------------------------------------------------------
-- Recursive lets

-- | @acc = register 0 (acc + x)@, with the binds in the given order.
accumulator :: [Bind] -> Program
accumulator binds =
  topProgram (bv8Ports ["x"]) (bv8Ports ["acc"]) . overPorts (bv8Ports ["x"]) $
    ELet True binds (var "acc")

accReg, accNext :: Bind
accReg = Bind "acc" (sig (bv 8)) (registerE (b8 0) (var "next"))
accNext = Bind "next" (sig (bv 8)) (liftE [bv 8, bv 8] (bv 8) (addPrim 8) [var "acc", var "x"])

accRows, accOutputs :: [[Value]]
accRows = fmap (pure . b8) [1, 2, 3, 250, 0]
accOutputs = fmap (pure . b8) [0, 1, 3, 6, 0]

-- | @p = (register 0 (snd p), fst p + 1)@: feedback through a tuple.
pairCounterProgram :: Program
pairCounterProgram =
  topProgram [] [Port "count" (bv 4)] $
    ELet
      True
      [ Bind "p" (TProd [sig (bv 4), sig (bv 4)]) $
          ETuple
            [ registerE (b4 0) (EProj 1 (var "p"))
            , liftE [bv 4] (bv 4) (incr 4) [EProj 0 (var "p")]
            ]
      ]
      (EProj 0 (var "p"))

-- | An inner recursive let whose binds read the outer bind @a@:
-- @a = register 0 b@, @b = a + c@, @c = register 1 b@, so @a@ doubles.
doublingProgram :: Program
doublingProgram =
  topProgram [] (bv8Ports ["a"]) $
    ELet True [Bind "a" (sig (bv 8)) (registerE (b8 0) inner)] (var "a")
  where
    inner =
      ELet
        True
        [ Bind "b" (sig (bv 8)) (liftE [bv 8, bv 8] (bv 8) (addPrim 8) [var "a", var "c"])
        , Bind "c" (sig (bv 8)) (registerE (b8 1) (var "b"))
        ]
        (var "b")

-- | A recursive signal next to a non-recursive constant it reads.
stepProgram :: Program
stepProgram =
  topProgram [] (bv8Ports ["s"]) $
    ELet
      True
      [ Bind "s" (sig (bv 8)) . registerE (b8 0) $
          liftE [bv 8] (bv 8) (ELam [("v", bv 8)] (bvBin BvAdd 8 (var "v") (var "step"))) [var "s"]
      , Bind "step" (bv 8) (ELit (b8 3))
      ]
      (var "s")

-- | A zero-input top with one recursive Bool signal @s@.
boolLoop :: Expr -> Program
boolLoop rhs = topProgram [] [Port "o" TBool] (ELet True [Bind "s" (sig TBool) rhs] (var "s"))

-- | A counter that saturates at 3 because its own output, fed back,
-- enables it: @c = mealy step 0 (lift (\v -> v < 3) c)@. The output of
-- @step@ is its state, so it does not depend on the enable it computes.
saturatingProgram :: Expr -> Program
saturatingProgram step =
  topProgram [] (bv8Ports ["c"]) $
    ELet
      True
      [ Bind "c" (sig (bv 8)) . mealyE (b8 0) TBool (bv 8) step $
          liftE [bv 8] TBool (ELam [("v", bv 8)] (bvUlt8 (var "v") (ELit (b8 3)))) [var "c"]
      ]
      (var "c")
  where
    bvUlt8 a b = EApp (prim BvUlt [bv 8, bv 8] TBool) [a, b]

-- | @\s e -> (if e then s + 1 else s, s)@.
stepInside :: Expr
stepInside =
  ELam [("s", bv 8), ("e", TBool)] $
    ETuple [EIf (var "e") (EApp (incr 8) [var "s"]) (var "s"), var "s"]

-- | @\s e -> if e then (s + 1, s) else (s, s)@: 'stepInside' with the @if@
-- outside the pair.
stepOutside :: Expr
stepOutside =
  ELam [("s", bv 8), ("e", TBool)] $
    EIf (var "e") (ETuple [EApp (incr 8) [var "s"], var "s"]) (ETuple [var "s", var "s"])

-- | The normal form of 'saturatingProgram'.
saturatingNormal :: NModule
saturatingNormal =
  normalModule
    []
    [NOutput "c" (bv 8) (AVar "s")]
    [ NBind "s" (bv 8) (NReg (b8 0) (AVar "s_next"))
    , NBind "en" TBool (NPrim BvUlt [AVar "s", ALit (b8 3)])
    , NBind "inc" (bv 8) (NPrim BvAdd [AVar "s", ALit (b8 1)])
    , NBind "s_next" (bv 8) (NMux (AVar "en") (AVar "inc") (AVar "s"))
    ]

saturated :: [[Value]]
saturated = fmap (pure . b8) [0, 1, 2, 3, 3, 3]

coreLetRecSpec :: Spec
coreLetRecSpec = do
  it "[sim-letrec] feeds a register back into its own input" $
    simulateCore (accumulator [Bind "acc" (sig (bv 8)) (registerE (b8 0) (accNext' "acc"))]) accRows
      `shouldBe` Right accOutputs
  it "[sim-letrec] closes a loop over two binds in either order" $ do
    simulateCore (accumulator [accReg, accNext]) accRows `shouldBe` Right accOutputs
    simulateCore (accumulator [accNext, accReg]) accRows `shouldBe` Right accOutputs
  it "[sim-letrec] closes a loop through the components of a recursive tuple" $
    simulateCore pairCounterProgram (replicate 18 [])
      `shouldBe` Right [[b4 (t `mod` 16)] | t <- [0 .. 17]]
  it "[sim-letrec] nests recursive lets that read an enclosing recursive bind" $
    simulateCore doublingProgram (replicate 11 [])
      `shouldBe` Right (fmap (pure . b8) [0, 1, 2, 4, 8, 16, 32, 64, 128, 0, 0])
  it "[sim-letrec] lets a recursive signal read a non-recursive bind of the same let" $
    simulateCore stepProgram (replicate 4 []) `shouldBe` Right (fmap (pure . b8) [0, 3, 6, 9])
  it "[sim-letrec] closes a loop through sig.mealy behind a register" $ do
    let accIn = bvBin BvAdd 8 (var "acc") (var "i")
        step = ELam [("acc", bv 8), ("i", bv 8)] (ETuple [accIn, accIn])
        rhs = registerE (b8 1) (mealyE (b8 0) (bv 8) (bv 8) step (var "s"))
        prog = topProgram [] (bv8Ports ["s"]) (ELet True [Bind "s" (sig (bv 8)) rhs] (var "s"))
    simulateCore prog (replicate 6 []) `shouldBe` Right (fmap (pure . b8) [1, 1, 2, 4, 8, 16])
  it "[sim-letrec] lets a recursive signal use a non-recursive function of the same let" $ do
    let prog =
          topProgram [] (bv8Ports ["s"]) $
            ELet
              True
              [ Bind "s" (sig (bv 8)) (registerE (b8 0) (liftE [bv 8] (bv 8) (var "f") [var "s"]))
              , Bind "f" (TFun (bv 8) (bv 8)) $
                  ELam [("v", bv 8)] (bvBin BvAdd 8 (var "v") (ELit (b8 5)))
              ]
              (var "s")
    simulateCore prog (replicate 4 []) `shouldBe` Right (fmap (pure . b8) [0, 5, 10, 15])
  it "[sim-letrec] follows feedback through a global function" $ do
    let sig8 = sig (bv 8)
        delayInc =
          Def "T.delayInc" (TFun sig8 sig8) . ELam [("x", sig8)] $
            registerE (b8 0) (liftE [bv 8] (bv 8) (incr 8) [var "x"])
        inc =
          Def "T.inc" (TFun sig8 sig8) . ELam [("x", sig8)] $
            liftE [bv 8] (bv 8) (incr 8) [var "x"]
        through g =
          programWith
            []
            (bv8Ports ["s"])
            (ELet True [Bind "s" sig8 (EApp (EGlobal g) [var "s"])] (var "s"))
            [delayInc, inc]
    simulateCore (through "T.delayInc") (replicate 4 [])
      `shouldBe` Right (fmap (pure . b8) [0, 1, 2, 3])
    r <- settled (simulateCore (through "T.inc") (replicate 4 []))
    r `shouldBeSimError` "not productive"
  it "[sim-letrec] rejects a combinational loop through sig.lift" $ do
    r <-
      settled
        ( simulateCore
            (boolLoop (liftE [TBool] TBool (prim BoolNot [TBool] TBool) [var "s"]))
            (replicate 3 [])
        )
    r `shouldBeSimError` "not productive"
  it "[sim-letrec] rejects a signal defined as itself" $ do
    r <- settled (simulateCore (boolLoop (var "s")) (replicate 3 []))
    r `shouldBeSimError` "not productive"
  it "[sim-letrec] rejects a loop through the input of sig.mealy" $ do
    let step = ELam [("st", TBool), ("i", TBool)] (ETuple [var "st", var "i"])
        prog = boolLoop (mealyE (VBool False) TBool TBool step (var "s"))
    r <- settled (simulateCore prog (replicate 3 []))
    r `shouldBeSimError` "not productive"
  it "[sim-letrec] rejects a loop closed through a nested recursive let" $ do
    let inner =
          ELet
            True
            [ Bind "b" (sig (bv 8)) (liftE [bv 8, bv 8] (bv 8) (addPrim 8) [var "a", var "c"])
            , Bind "c" (sig (bv 8)) (registerE (b8 0) (var "b"))
            ]
            (var "b")
        prog = topProgram [] (bv8Ports ["a"]) (ELet True [Bind "a" (sig (bv 8)) inner] (var "a"))
    r <- settled (simulateCore prog (replicate 3 []))
    r `shouldBeSimError` "not productive"
  it "[sim-letrec] rejects a plain value defined in terms of itself" $ do
    let prog =
          topProgram [] (bv8Ports ["o"]) $
            ELet
              True
              [Bind "k" (bv 8) (bvBin BvAdd 8 (var "k") (ELit (b8 1)))]
              (pureE (bv 8) (var "k"))
    r <- settled (simulateCore prog (replicate 3 []))
    r `shouldBeSimError` "not productive: the value of k at cycle 0 depends on itself"
  it "[sim-letrec] lets sig.lift feed back an argument its function ignores" $ do
    let five = ELam [("v", bv 8)] (ELit (b8 5))
        prog =
          topProgram [] (bv8Ports ["s"]) $
            ELet True [Bind "s" (sig (bv 8)) (liftE [bv 8] (bv 8) five [var "s"])] (var "s")
    simulateCore prog (replicate 3 []) `shouldBe` Right (replicate 3 [b8 5])
  it "[sim-letrec] lets a recursive tuple of values read its own components" $ do
    let prog =
          topProgram [] (bv8Ports ["o"]) $
            ELet
              True
              [Bind "p" (TProd [bv 8, bv 8]) (ETuple [ELit (b8 7), EProj 0 (var "p")])]
              (pureE (bv 8) (EProj 1 (var "p")))
    simulateCore prog (replicate 3 []) `shouldBe` Right (replicate 3 [b8 7])
  it "[sim-letrec] feeds back a mealy output that depends only on the state" $ do
    simulateCore (saturatingProgram stepInside) (replicate 6 []) `shouldBe` Right saturated
    simulateNormal saturatingNormal (replicate 6 []) `shouldBe` Right saturated
  it "[sim-letrec] gives an if whose condition is fed back the value its branches agree on" $ do
    simulateCore (saturatingProgram stepOutside) (replicate 6 []) `shouldBe` Right saturated
    let five = ELam [("v", bv 8)] (EIf (bvEq8 (var "v") (ELit (b8 0))) (ELit (b8 5)) (ELit (b8 5)))
        prog =
          topProgram [] (bv8Ports ["s"]) $
            ELet True [Bind "s" (sig (bv 8)) (liftE [bv 8] (bv 8) five [var "s"])] (var "s")
    simulateCore prog (replicate 3 []) `shouldBe` Right (replicate 3 [b8 5])
  it "[sim-letrec] agrees component by component when an if reads its own result" $ do
    -- s = lift (\q -> if q.1 then (3, true) else (4, true)) s: the flag is
    -- true in both branches, so the condition holds and the count is 3.
    let pairTy = TProd [bv 8, TBool]
        pair n = ETuple [ELit (b8 n), ELit (VBool True)]
        f = ELam [("q", pairTy)] (EIf (EProj 1 (var "q")) (pair 3) (pair 4))
        prog =
          topProgram [] (bv8Ports ["o"]) $
            ELet True [Bind "s" (sig pairTy) (liftE [pairTy] pairTy f [var "s"])] $
              liftE [pairTy] (bv 8) (ELam [("q", pairTy)] (EProj 0 (var "q"))) [var "s"]
    simulateCore prog (replicate 3 []) `shouldBe` Right (replicate 3 [b8 3])
  it "[sim-letrec] rejects an if fed back through its condition when its branches differ" $ do
    let f = ELam [("v", bv 8)] (EIf (bvEq8 (var "v") (ELit (b8 0))) (ELit (b8 1)) (ELit (b8 2)))
        prog =
          topProgram [] (bv8Ports ["s"]) $
            ELet True [Bind "s" (sig (bv 8)) (liftE [bv 8] (bv 8) f [var "s"])] (var "s")
    r <- settled (simulateCore prog (replicate 3 []))
    r `shouldBeSimError` "not productive: the value of s at cycle 0 depends on itself"
  it "[sim-letrec] ignores a value that is not productive when no output needs it" $ do
    let prog =
          topProgram [] [Port "o" TBool] $
            ELet True [Bind "x" (sig TBool) notLoop] (pureE TBool (ELit (VBool True)))
    simulateCore prog (replicate 3 []) `shouldBe` Right (replicate 3 [VBool True])
  it "[sim-letrec] reports a loop behind a register in the cycle that reads it" $ do
    let prog =
          topProgram [] [Port "o" TBool] $
            ELet
              True
              [Bind "x" (sig TBool) notLoop, Bind "r" (sig TBool) (registerE (VBool False) (var "x"))]
              (var "r")
    simulateCore prog [[]] `shouldBe` Right [[VBool False]]
    r <- settled (simulateCore prog [[], []])
    r `shouldBeSimError` "not productive: the value of x at cycle 0 depends on itself"
    r `shouldBeSimError` "in cycle 1"
  it "[sim-letrec] evaluates a recursive function that returns" $ do
    -- pop v = if v == 0 then 0 else (v & 1) + pop (v >> 1)
    let lshr1 e = EApp (prim (BvLshr 1) [bv 8] (bv 8)) [e]
        pop =
          ELam [("v", bv 8)] $
            EIf
              (bvEq8 (var "v") (ELit (b8 0)))
              (ELit (b8 0))
              ( bvBin
                  BvAdd
                  8
                  (bvBin BvAnd 8 (var "v") (ELit (b8 1)))
                  (EApp (var "pop") [lshr1 (var "v")])
              )
        prog =
          topProgram (bv8Ports ["x"]) (bv8Ports ["o"]) . overPorts (bv8Ports ["x"]) $
            ELet
              True
              [Bind "pop" (TFun (bv 8) (bv 8)) pop]
              (liftE [bv 8] (bv 8) (var "pop") [var "x"])
    simulateCore prog (fmap (pure . b8) [0, 1, 255, 165, 128])
      `shouldBe` Right (fmap (pure . b8) [0, 1, 8, 4, 1])
  it "[sim-letrec] reports a recursive function that never returns" $ do
    let f = Bind "f" (TFun (bv 8) (bv 8)) (ELam [("v", bv 8)] (EApp (var "f") [var "v"]))
        prog =
          topProgram (bv8Ports ["x"]) (bv8Ports ["o"]) . overPorts (bv8Ports ["x"]) $
            ELet True [f] (liftE [bv 8] (bv 8) (var "f") [var "x"])
    r <- settled (simulateCore prog [[b8 1]])
    r `shouldBeSimError` "nested more than 100000"
  where
    accNext' acc = liftE [bv 8, bv 8] (bv 8) (addPrim 8) [var acc, var "x"]
    notLoop = liftE [TBool] TBool (prim BoolNot [TBool] TBool) [var "x"]

----------------------------------------------------------------------
-- Evaluation limits

-- | @g0 = \v -> v@ and @gi = \v -> g(i-1) (g(i-1) v)@ for @i = 1 .. k@,
-- with @gk@ lifted over the input: the identity, at a cost of
-- @2^(k+1) - 1@ applications, about @9 * 2^k@ evaluation steps, per cycle.
doublingWork :: Int -> Program
doublingWork = doublingOver (var "v")

-- | 'doublingWork' with @g0 v = base@: @2^k@ calls of @g0@ a cycle.
doublingOver :: Expr -> Int -> Program
doublingOver base k =
  programWith
    (bv8Ports ["x"])
    (bv8Ports ["o"])
    (overPorts (bv8Ports ["x"]) (liftE [bv 8] (bv 8) (EGlobal (doubling k)) [var "x"]))
    (doublingDefsWith base k)

-- | The defs @T.g0 .. T.gk@ of 'doublingWork'.
doublingDefs :: Int -> [Def]
doublingDefs = doublingDefsWith (var "v")

-- | The defs @T.g0 .. T.gk@ of 'doublingOver'.
doublingDefsWith :: Expr -> Int -> [Def]
doublingDefsWith base k =
  [Def (doubling i) (TFun (bv 8) (bv 8)) (ELam [("v", bv 8)] (body i)) | i <- [0 .. k]]
  where
    body i
      | i <= 0 = base
      | otherwise = EApp (EGlobal (doubling (i - 1))) [EApp (EGlobal (doubling (i - 1))) [var "v"]]

-- | Bodies for @g0 v@ in 'doublingOver' that bind @w@ operands, each a
-- variable or a literal, and then return @v@, so a call costs about @w@
-- evaluation steps and does nothing else.
operandBodies :: [(String, Int -> Expr)]
operandBodies =
  [ ("component of a tuple of variables", wideTuple (var "v"))
  , ("component of a tuple of literals", wideTuple (ELit (b8 0)))
  , ("bind of a let", \w -> ELet False (binds w) (var "v"))
  , ("bind of a recursive let", \w -> ELet True (binds w) (var "v"))
  ]
  where
    binds w = [Bind (Name (Text.pack ("a" <> show i))) (bv 8) (var "v") | i <- [1 .. w]]

-- | @let t = (e, .., e) in v@, with @w@ components.
wideTuple :: Expr -> Int -> Expr
wideTuple e w =
  ELet False [Bind "t" (TProd (replicate w (bv 8))) (ETuple (replicate w e))] (var "v")

-- | @k = g18 7@ in a recursive let, read through @sig.pure@: a constant
-- that costs about @9 * 2^18@ steps, more than a cycle may take, and is
-- computed when cycle 0 first needs it.
recursiveConstant :: Program
recursiveConstant =
  programWith
    []
    (bv8Ports ["o"])
    (ELet True [Bind "k" (bv 8) constant] (pureE (bv 8) (var "k")))
    (doublingDefs 18)
  where
    constant = EApp (EGlobal (doubling 18)) [ELit (b8 7)]

-- | A global constant @T.k = g18 7@, added to the input inside a lifted
-- function, so it is first needed while cycle 0 is computed.
globalConstant :: Program
globalConstant =
  programWith
    (bv8Ports ["x"])
    (bv8Ports ["o"])
    (overPorts (bv8Ports ["x"]) (liftE [bv 8] (bv 8) addK [var "x"]))
    (Def "T.k" (bv 8) (EApp (EGlobal (doubling 18)) [ELit (b8 7)]) : doublingDefs 18)
  where
    addK = ELam [("v", bv 8)] (bvBin BvAdd 8 (var "v") (EGlobal "T.k"))

-- | Five global signals @T.sj = r16 (sig.pure j)@, each built from @2^16@
-- registers ('registerDoubling'), and a lifted function that is the
-- identity but binds @T.sj@ in the cycles where its input is @j@. A
-- global is computed once, so each of these signals is built the first
-- time a cycle needs it and kept for the rest of the run.
globalSignals :: Program
globalSignals =
  programWith
    (bv8Ports ["x"])
    (bv8Ports ["o"])
    (overPorts (bv8Ports ["x"]) (liftE [bv 8] (bv 8) pick [var "x"]))
    ([Def (signalGlobal j) (sig (bv 8)) (built j) | j <- [0 .. 4]] <> registerDoubling (b8 0) 16)
  where
    built j = EApp (EGlobal (registers 16)) [pureE (bv 8) (ELit (b8 j))]
    pick = ELam [("v", bv 8)] (foldr bindAt (var "v") [0 .. 4])
    bindAt j =
      EIf
        (bvEq8 (var "v") (ELit (b8 j)))
        (ELet False [Bind "s" (sig (bv 8)) (EGlobal (signalGlobal j))] (var "v"))
    signalGlobal j = Name (Text.pack ("T.s" <> show j))

-- | @g0 s = base@ and @gi s = g(i-1) (g(i-1) s)@ on 8-bit signals, with
-- @gk@ applied to the input: building the network calls @g0@ @2^k@ times,
-- although the network is just the input.
signalDoubling :: Expr -> Int -> Program
signalDoubling base k =
  programWith
    (bv8Ports ["x"])
    (bv8Ports ["o"])
    (overPorts (bv8Ports ["x"]) (EApp (EGlobal (h k)) [var "x"]))
    [Def (h i) (TFun sig8 sig8) (ELam [("s", sig8)] (body i)) | i <- [0 .. k]]
  where
    sig8 = sig (bv 8)
    h :: Int -> Name
    h i = Name (Text.pack ("T.h" <> show i))
    body i
      | i <= 0 = base
      | otherwise = EApp (EGlobal (h (i - 1))) [EApp (EGlobal (h (i - 1))) [var "s"]]

-- | @let t = l in x@ for a literal tuple @l@ of @2^n@ Bools: about @2^n@
-- evaluation steps (one for each component), spent far faster than steps
-- that evaluate expressions, so tests can reach the large bounds quickly
-- even when built without optimization.
literalWork :: Int -> Text -> Expr
literalWork n x = ELet False [Bind "t" (valueTy wide) (ELit wide)] (var x)
  where
    wide = VTuple (replicate (2 ^ n) (VBool False))

-- | The name of @gi@ in 'doublingDefs'.
doubling :: Int -> Name
doubling i = Name (Text.pack ("T.g" <> show i))

-- | @h0 v = let s = sig.pure v in v@ and @hi v = h(i-1) (h(i-1) v)@,
-- with @h10@ lifted over the input: the identity, making and dropping
-- @2^10@ signals a cycle.
droppedSignals :: Program
droppedSignals =
  programWith
    (bv8Ports ["x"])
    (bv8Ports ["o"])
    (overPorts (bv8Ports ["x"]) (liftE [bv 8] (bv 8) (EGlobal (h 10)) [var "x"]))
    [Def (h i) (TFun (bv 8) (bv 8)) (ELam [("v", bv 8)] (body i)) | i <- [0 .. 10]]
  where
    h :: Int -> Name
    h i = Name (Text.pack ("T.h" <> show i))
    body i
      | i <= 0 = ELet False [Bind "s" (sig (bv 8)) (pureE (bv 8) (var "v"))] (var "v")
      | otherwise = EApp (EGlobal (h (i - 1))) [EApp (EGlobal (h (i - 1))) [var "v"]]

-- | A counter whose output is its input, computed with @g18@ of
-- 'doublingDefs' (about @9 * 2^18@ steps) in the cycle where the count is
-- 3 and directly in every other cycle.
expensiveAtThree :: Program
expensiveAtThree =
  programWith
    (bv8Ports ["x"])
    (bv8Ports ["o"])
    (overPorts (bv8Ports ["x"]) (mealyE (b8 0) (bv 8) (bv 8) step (var "x")))
    (doublingDefs 18)
  where
    step =
      ELam [("s", bv 8), ("i", bv 8)] $
        ETuple
          [ EApp (incr 8) [var "s"]
          , EIf (bvEq8 (var "s") (ELit (b8 3))) (EApp (EGlobal (doubling 18)) [var "i"]) (var "i")
          ]

-- | @r0 s = register v s@ and @ri s = r(i-1) (r(i-1) s)@: @ri@ delays a
-- signal of the type of @v@ through @2^i@ registers. The defs @T.r0 ..
-- T.rk@.
registerDoubling :: Value -> Int -> [Def]
registerDoubling v k =
  [Def (registers i) (TFun (sig t) (sig t)) (ELam [("s", sig t)] (body i)) | i <- [0 .. k]]
  where
    t = valueTy v
    body i
      | i <= 0 = registerE v (var "s")
      | otherwise = EApp (EGlobal (registers (i - 1))) [EApp (EGlobal (registers (i - 1))) [var "s"]]

-- | The name of @ri@ in 'registerDoubling'.
registers :: Int -> Name
registers i = Name (Text.pack ("T.r" <> show i))

-- | A one-input top whose output is its input delayed by the registers of
-- @rk@, then of @rj@ for each @j@ in the list, from 'registerDoubling'
-- with initial value 0.
delayedBy :: Int -> [Int] -> Program
delayedBy k more =
  programWith
    (bv8Ports ["x"])
    (bv8Ports ["o"])
    (overPorts (bv8Ports ["x"]) (foldr (\j e -> EApp (EGlobal (registers j)) [e]) (var "x") (k : more)))
    (registerDoubling (b8 0) k)

-- | Signals of @n@-component Bool tuples through the @2^k@ registers of
-- @rk@ ('registerDoubling'); the output is the first component.
wideRegisters :: Int -> Int -> Program
wideRegisters n k =
  programWith
    [Port "b" TBool]
    [Port "o" TBool]
    ( overPorts [Port "b" TBool] $
        liftE
          [tupleTy]
          TBool
          (ELam [("p", tupleTy)] (EProj 0 (var "p")))
          [EApp (EGlobal (registers k)) [liftE [TBool] tupleTy (ELam [("v", TBool)] wide) [var "b"]]]
    )
    (registerDoubling (VTuple (replicate n (VBool False))) k)
  where
    tupleTy = TProd (replicate n TBool)
    wide = ETuple (replicate n (var "v"))

-- | Names @prefix1 .. prefixn@ bound in order, each by @step@ applied to
-- the one before (@prefix0@ for the first).
chain :: Text -> Ty -> (Expr -> Expr) -> Int -> Expr -> Expr
chain prefix ty step n =
  ELet False [Bind (name i) ty (step (EVar (name (i - 1)))) | i <- [1 .. n]]
  where
    name i = Name (prefix <> Text.pack (show i))

coreLimitSpec :: Spec
coreLimitSpec = do
  it "[sim-depth] evaluates a chain of let binds longer than the nesting limit" $ do
    let n = 110000
        f = ELam [("x0", bv 8)] (chain "x" (bv 8) (EApp (incr 8) . pure) n (var ("x" <> showText n)))
        prog =
          topProgram (bv8Ports ["x"]) (bv8Ports ["o"]) . overPorts (bv8Ports ["x"]) $
            liftE [bv 8] (bv 8) f [var "x"]
    r <- settled (simulateCore prog [[b8 0], [b8 10]])
    r `shouldBe` Right [[b8 (toInteger n `mod` 256)], [b8 ((toInteger n + 10) `mod` 256)]]
  it "[sim-depth] runs a chain of signals longer than the nesting limit" $ do
    let n = 150000
        next s = liftE [bv 8] (bv 8) (incr 8) [s]
        prog =
          topProgram (bv8Ports ["s0"]) (bv8Ports ["o"]) . overPorts (bv8Ports ["s0"]) $
            chain "s" (sig (bv 8)) next n (var ("s" <> showText n))
    r <- settled (simulateCore prog [[b8 0], [b8 10]])
    r `shouldBe` Right [[b8 (toInteger n `mod` 256)], [b8 ((toInteger n + 10) `mod` 256)]]
  it "[sim-budget] runs a cycle of about 9 * 2^16 steps, within the 2^20 a cycle may take" $
    simulateCore (doublingWork 16) [[b8 7], [b8 9]] `shouldBe` Right [[b8 7], [b8 9]]
  it "[sim-budget] stops a cycle of about 9 * 2^18 steps in cycle 0" $ do
    r <- settled (simulateCore (doublingWork 18) [[b8 7], [b8 9]])
    r `shouldBeSimError` "the cycle needs more than 1048576 evaluation steps"
    r `shouldBeSimError` "in cycle 0"
  it "[sim-budget] stops a program with 2^41 applications per cycle in cycle 0" $ do
    r <- settled (simulateCore (doublingWork 40) [[b8 7]])
    r `shouldBeSimError` "the cycle needs more than 1048576 evaluation steps"
    r `shouldBeSimError` "in cycle 0"
  it "[sim-budget] marks exceeded bounds as inconclusive and other errors as not" $ do
    cycleBudget <- settled (simulateCore (doublingWork 18) [[b8 7]])
    either isBudgetError (const False) cycleBudget `shouldBe` True
    nodeCap <- settled (simulateCore (delayedBy 20 []) [[b8 1]])
    either isBudgetError (const False) nodeCap `shouldBe` True
    badRow <- settled (simulateCore (doublingWork 1) [[b8 7, b8 8]])
    badRow `shouldBeSimError` ""
    either isBudgetError (const True) badRow `shouldBe` False
  it "[sim-budget] gives every cycle the same budget, so only the expensive cycle fails" $ do
    let rows = fmap (pure . b8) [10 .. 15]
    simulateCore expensiveAtThree (take 3 rows) `shouldBe` Right (take 3 rows)
    r <- settled (simulateCore expensiveAtThree rows)
    r `shouldBeSimError` "the cycle needs more than 1048576 evaluation steps"
    r `shouldBeSimError` "in cycle 3"
  it "[sim-budget] rejects the 2^20 registers of the register-doubling program while building" $ do
    r <- settled (simulateCore (delayedBy 20 []) (replicate 3 [b8 1]))
    r `shouldBeSimError` "the signal network has more than 262144 nodes"
    r `shouldBeSimError` "in def T.top"
  it "[sim-budget] runs a network of exactly 2^18 nodes and rejects one more" $ do
    -- One input and 2^17 + 2^16 + .. + 2^0 = 2^18 - 1 registers.
    let atLimit = delayedBy 17 [16, 15 .. 0]
    r <- settled (simulateCore atLimit [[b8 1], [b8 2]])
    r `shouldBe` Right [[b8 0], [b8 0]]
    r' <- settled (simulateCore (delayedBy 17 ([16, 15 .. 0] <> [0])) [[b8 1], [b8 2]])
    r' `shouldBeSimError` "the signal network has more than 262144 nodes"
  it "[sim-budget] charges a cycle for every state component its registers store" $ do
    -- 2^11 registers, each storing 1024 components a cycle.
    simulateCore (wideRegisters 1024 2) [[VBool True]] `shouldBe` Right [[VBool False]]
    r <- settled (simulateCore (wideRegisters 1024 11) [[VBool True]])
    r `shouldBeSimError` "the cycle needs more than 1048576 evaluation steps"
    r `shouldBeSimError` "in cycle 0"
  it "[sim-budget] does not count signals a function makes and drops against the node limit" $ do
    -- 2^10 sig.pure nodes a cycle, for 300 cycles.
    let rows = [[b8 (t `mod` 256)] | t <- [0 .. 299]]
    r <- settled (simulateCore droppedSignals rows)
    r `shouldBe` Right rows
  it "[sim-budget] [o0-fast] runs 10000 cycles of 2^15 steps, more than 2^28 steps in all" $ do
    let rows = [[b8 (t `mod` 256)] | t <- [0 .. 9999]]
        prog =
          topProgram (bv8Ports ["x"]) (bv8Ports ["o"]) . overPorts (bv8Ports ["x"]) $
            liftE [bv 8] (bv 8) (ELam [("v", bv 8)] (literalWork 15 "v")) [var "x"]
    r <- settled (simulateCore prog rows)
    r `shouldBe` Right rows
  it "[sim-build-charge] charges a recursive-let constant to the building budget, not to cycle 0" $ do
    checkProgram recursiveConstant `shouldBe` Right ()
    r <- settled (simulateCore recursiveConstant (replicate 3 []))
    r `shouldBe` Right (replicate 3 [b8 7])
  it "[sim-build-charge] charges a global constant to the building budget, not to cycle 0" $ do
    checkProgram globalConstant `shouldBe` Right ()
    r <- settled (simulateCore globalConstant [[b8 1], [b8 2]])
    r `shouldBe` Right [[b8 8], [b8 9]]
  it "[sim-build-charge] counts the nodes a global builds during a cycle against the node limit" $ do
    -- Each global signal is 2^16 + 1 nodes and the network itself 2, so
    -- three fit within 2^18 nodes and the fourth does not. A global is
    -- built once, so binding it again in a later cycle adds no nodes.
    checkProgram globalSignals `shouldBe` Right ()
    let rows = fmap (pure . b8)
    r <- settled (simulateCore globalSignals (rows [0, 1, 2, 0, 1, 2]))
    r `shouldBe` Right (rows [0, 1, 2, 0, 1, 2])
    r' <- settled (simulateCore globalSignals (rows [0, 1, 2, 3]))
    r' `shouldBeSimError` "the signal network has more than 262144 nodes"
    r' `shouldBeSimError` "in cycle 3"
    either isBudgetError (const False) r' `shouldBe` True
  for_ operandBodies $ \(what, body) ->
    it ("[sim-operand-charge] charges a step for each " <> what) $ do
      -- 2^10 calls a cycle: 512 operands each fit in the 2^20 steps of a
      -- cycle, 1100 do not.
      r <- settled (simulateCore (doublingOver (body 512) 10) [[b8 7]])
      r `shouldBe` Right [[b8 7]]
      r' <- settled (simulateCore (doublingOver (body 1100) 10) [[b8 7]])
      r' `shouldBeSimError` "the cycle needs more than 1048576 evaluation steps"
      r' `shouldBeSimError` "in cycle 0"
  it "[sim-operand-charge] stops the wide-tuple program in cycle 0, long before it would finish" $ do
    -- 2^14 calls a cycle, each binding a tuple of 100000 copies of its
    -- argument: if components were free, a cycle would take minutes.
    let prog = doublingOver (wideTuple (var "v") 100000) 14
    checkProgram prog `shouldBe` Right ()
    r <- settled (simulateCore prog [[b8 7]])
    r `shouldBeSimError` "the cycle needs more than 1048576 evaluation steps"
    r `shouldBeSimError` "in cycle 0"
  it "[sim-operand-charge] charges a step for each component of a literal tuple" $ do
    -- A literal of 2^19 components fits in the 2^20 steps of a cycle; one of
    -- 2^21 does not, though evaluating it is a single expression.
    let lifted n =
          topProgram (bv8Ports ["x"]) (bv8Ports ["o"]) . overPorts (bv8Ports ["x"]) $
            liftE [bv 8] (bv 8) (ELam [("v", bv 8)] (literalWork n "v")) [var "x"]
    checkProgram (lifted 21) `shouldBe` Right ()
    r <- settled (simulateCore (lifted 19) [[b8 7], [b8 8]])
    r `shouldBe` Right [[b8 7], [b8 8]]
    r' <- settled (simulateCore (lifted 21) [[b8 7]])
    r' `shouldBeSimError` "the cycle needs more than 1048576 evaluation steps"
    r' `shouldBeSimError` "in cycle 0"
    either isBudgetError (const False) r' `shouldBe` True
  it "[sim-build-limit] builds a network whose functions are applied 2^17 times" $ do
    r <- settled (simulateCore (signalDoubling (var "s") 16) [[b8 1], [b8 2]])
    r `shouldBe` Right [[b8 1], [b8 2]]
  it "[sim-build-limit] [o0-fast] builds a network that takes 2^27 steps, within 60 s" $ do
    -- 2^11 calls of 2^16 steps each.
    r <- settled (simulateCore (signalDoubling (literalWork 16 "s") 11) [[b8 1]])
    r `shouldBe` Right [[b8 1]]
  it "[sim-build-limit] [o0-fast] stops building after 2^28 steps, within 60 s" $ do
    -- 2^40 calls of 2^16 steps each: building would never finish.
    let prog = signalDoubling (literalWork 16 "s") 40
    checkProgram prog `shouldBe` Right ()
    r <- settled (simulateCore prog [[b8 1]])
    r `shouldBeSimError` "building the signal network needs more than 268435456 evaluation steps"
    r `shouldBeSimError` "in def T.top"
    either isBudgetError (const False) r `shouldBe` True
  where
    showText = Text.pack . show

----------------------------------------------------------------------
-- Normal form

ifNormal :: NModule
ifNormal =
  normalModule
    [("c", TBool), ("a", bv 8), ("b", bv 8)]
    [NOutput "o" (bv 8) (AVar "o_mux")]
    [NBind "o_mux" (bv 8) (NMux (AVar "c") (AVar "a") (AVar "b"))]

-- | Random rows of the given port types.
genRows :: [Ty] -> Gen [[Value]]
genRows tys = do
  n <- chooseInt (0, 64)
  vectorOf n (traverse genValue tys)
  where
    genValue = \case
      TBitVec w -> genBV w
      _ -> VBool <$> arbitrary

normalSpec :: Spec
normalSpec = do
  for_ examples $ \(name, _, nm, vs) ->
    it ("[sim-normal-examples] reproduces the " <> name <> " vectors") $
      simulateNormal nm (inputRows vs) `shouldBe` Right (outputRows vs)
  for_ examples $ \(name, prog, nm, vs) ->
    it ("[sim-normal-examples] " <> name <> ": agrees with simulateCore on random inputs") $
      property $
        forAll (genRows (fmap portTy (vecInputs vs))) $ \rows ->
          let core = simulateCore prog rows
           in counterexample (show core) (isRight core .&&. simulateNormal nm rows === core)
  it "[sim-normal-examples] both simulators run the counter for the maximum number of cycles" $ do
    let rows = replicate maxCycles [VBool True]
        lastTwo = drop (maxCycles - 2) (counts 8 maxCycles)
    core <- settled (drop (maxCycles - 2) <$> simulateCore counterProgram rows)
    core `shouldBe` Right lastTwo
    normal <- settled (drop (maxCycles - 2) <$> simulateNormal counterNormal rows)
    normal `shouldBe` Right lastTwo
  it "[sim-prim-table] a mux selects its then-branch when the condition holds" $
    simulateNormal ifNormal ifRows `shouldBe` Right ifOutputs
  it "rejects a bind that reads a later non-register bind" $ do
    let nm =
          normalModule
            [("x", bv 8)]
            [NOutput "o" (bv 8) (AVar "a")]
            [ NBind "a" (bv 8) (NPrim BvAdd [AVar "b", ALit (b8 1)])
            , NBind "b" (bv 8) (NPrim BvAdd [AVar "x", ALit (b8 1)])
            ]
    simulateNormal nm [[b8 1]] `shouldBeSimError` "not an input or an earlier bind"
  it "rejects a signal prim in a bind" $ do
    let nm =
          normalModule
            [("x", bv 8)]
            [NOutput "o" (bv 8) (AVar "a")]
            [NBind "a" (bv 8) (NPrim (SigRegister (b8 0)) [AVar "x"])]
    simulateNormal nm [[b8 1]] `shouldBeSimError` "sig.register"
  it "rejects a register whose next value has the wrong type" $ do
    let nm =
          normalModule
            [("x", TBool)]
            [NOutput "o" (bv 8) (AVar "r")]
            [NBind "r" (bv 8) (NReg (b8 0) (AVar "x"))]
    simulateNormal nm [[VBool True], [VBool False]] `shouldBeSimError` "register r"

----------------------------------------------------------------------
-- Multiple outputs

abPorts :: [Port]
abPorts = bv8Ports ["a", "b"]

abRows :: [[Value]]
abRows = [[b8 3, b8 4], [b8 5, b8 5], [b8 255, b8 1]]

-- | Outputs @sum = a + b@ and @same = a == b@.
twoOutputProgram :: Program
twoOutputProgram =
  topProgram abPorts [Port "sum" (bv 8), Port "same" TBool] . overPorts abPorts $
    liftE [bv 8, bv 8] (TProd [bv 8, TBool]) f [var "a", var "b"]
  where
    f =
      ELam
        [("x", bv 8), ("y", bv 8)]
        (ETuple [bvBin BvAdd 8 (var "x") (var "y"), bvEq8 (var "x") (var "y")])

-- | Outputs @sum = a + b@, @diff = a - b@ and @same = a == b@ on the
-- right-nested spine @(sum, (diff, same))@.
threeOutputProgram :: Program
threeOutputProgram =
  topProgram abPorts threeOutputPorts . overPorts abPorts $
    liftE [bv 8, bv 8] (TProd [bv 8, TProd [bv 8, TBool]]) f [var "a", var "b"]
  where
    f =
      ELam [("x", bv 8), ("y", bv 8)] $
        ETuple
          [ bvBin BvAdd 8 (var "x") (var "y")
          , ETuple [bvBin BvSub 8 (var "x") (var "y"), bvEq8 (var "x") (var "y")]
          ]

threeOutputPorts :: [Port]
threeOutputPorts = [Port "sum" (bv 8), Port "diff" (bv 8), Port "same" TBool]

twoOutputNormal, threeOutputNormal :: NModule
twoOutputNormal =
  normalModule
    [("a", bv 8), ("b", bv 8)]
    [NOutput "sum" (bv 8) (AVar "s"), NOutput "same" TBool (AVar "e")]
    [ NBind "s" (bv 8) (NPrim BvAdd [AVar "a", AVar "b"])
    , NBind "e" TBool (NPrim BvEq [AVar "a", AVar "b"])
    ]
threeOutputNormal =
  normalModule
    [("a", bv 8), ("b", bv 8)]
    [ NOutput "sum" (bv 8) (AVar "s")
    , NOutput "diff" (bv 8) (AVar "d")
    , NOutput "same" TBool (AVar "e")
    ]
    [ NBind "s" (bv 8) (NPrim BvAdd [AVar "a", AVar "b"])
    , NBind "d" (bv 8) (NPrim BvSub [AVar "a", AVar "b"])
    , NBind "e" TBool (NPrim BvEq [AVar "a", AVar "b"])
    ]

twoOutputs, threeOutputs :: [[Value]]
twoOutputs = [[b8 7, VBool False], [b8 10, VBool True], [b8 0, VBool False]]
threeOutputs = [[b8 7, b8 255, VBool False], [b8 10, b8 0, VBool True], [b8 0, b8 254, VBool False]]

multiOutputSpec :: Spec
multiOutputSpec = do
  it "[sim-multi-output] simulateCore reads two outputs off a pair" $
    simulateCore twoOutputProgram abRows `shouldBe` Right twoOutputs
  it "[sim-multi-output] simulateCore reads three outputs along the right-nested spine" $
    simulateCore threeOutputProgram abRows `shouldBe` Right threeOutputs
  it "[sim-multi-output] simulateCore rejects a flat triple for three outputs" $ do
    let flat =
          topProgram abPorts threeOutputPorts . overPorts abPorts $
            liftE [bv 8, bv 8] (TProd [bv 8, bv 8, TBool]) f [var "a", var "b"]
        f =
          ELam [("x", bv 8), ("y", bv 8)] $
            ETuple
              [ bvBin BvAdd 8 (var "x") (var "y")
              , bvBin BvSub 8 (var "x") (var "y")
              , bvEq8 (var "x") (var "y")
              ]
    simulateCore flat abRows `shouldBeSimError` "cycle 0"
  it "[sim-multi-output] simulateNormal lists two outputs in port order" $
    simulateNormal twoOutputNormal abRows `shouldBe` Right twoOutputs
  it "[sim-multi-output] simulateNormal lists three outputs in port order" $
    simulateNormal threeOutputNormal abRows `shouldBe` Right threeOutputs
  it "[sim-multi-output] simulateNormal outputs may read inputs and literals directly" $ do
    let nm =
          normalModule
            [("a", bv 8), ("b", bv 8)]
            [NOutput "echo" (bv 8) (AVar "b"), NOutput "one" TBool (ALit (VBool True))]
            []
    simulateNormal nm abRows `shouldBe` Right [[b, VBool True] | [_, b] <- abRows]

----------------------------------------------------------------------
-- Zero-input tops

-- | A free-running counter of width @w@: @s = register 0 (s + 1)@.
freeCounterProgram :: Natural -> Program
freeCounterProgram w =
  topProgram [] [Port "count" (bv w)] $
    ELet
      True
      [Bind "s" (sig (bv w)) (registerE (VBV w 0) (liftE [bv w] (bv w) (incr w) [var "s"]))]
      (var "s")

freeCounterNormal :: Natural -> NModule
freeCounterNormal w =
  normalModule
    []
    [NOutput "count" (bv w) (AVar "s")]
    [ NBind "s" (bv w) (NReg (VBV w 0) (AVar "s_next"))
    , NBind "s_next" (bv w) (NPrim BvAdd [AVar "s", ALit (VBV w 1)])
    ]

counts :: Natural -> Int -> [[Value]]
counts w n = [[VBV w (t `mod` 2 ^ w)] | t <- [0 .. toInteger n - 1]]

zeroInputSpec :: Spec
zeroInputSpec = do
  it "[sim-zero-input] simulateCore runs one cycle per empty row" $
    simulateCore (freeCounterProgram 4) (replicate 20 []) `shouldBe` Right (counts 4 20)
  it "[sim-zero-input] simulateNormal runs one cycle per empty row" $
    simulateNormal (freeCounterNormal 4) (replicate 20 []) `shouldBe` Right (counts 4 20)
  it "[sim-zero-input] no rows simulate no cycles" $ do
    simulateCore (freeCounterProgram 4) [] `shouldBe` Right []
    simulateNormal (freeCounterNormal 4) [] `shouldBe` Right []
  it "[sim-zero-input] both simulators run the maximum number of vector cycles" $ do
    let rows = replicate maxCycles []
        lastTwo = drop (maxCycles - 2) (counts 16 maxCycles)
    core <- settled (drop (maxCycles - 2) <$> simulateCore (freeCounterProgram 16) rows)
    core `shouldBe` Right lastTwo
    normal <- settled (drop (maxCycles - 2) <$> simulateNormal (freeCounterNormal 16) rows)
    normal `shouldBe` Right lastTwo

----------------------------------------------------------------------
-- Row validation

-- | Malformed input rows: what is wrong, the circuit in both forms, the
-- rows, and the cycle the error must name.
badRows :: [(String, Program, NModule, [[Value]], Text)]
badRows =
  [ ("a row with too few values", macProgram, macNormal, [[b8 3]], "cycle 0")
  ,
    ( "a row with too many values"
    , counterProgram
    , counterNormal
    , [[VBool True], [VBool True, VBool False]]
    , "cycle 1"
    )
  , ("a Bool on a bit-vector port", macProgram, macNormal, [[VBool True, b8 1]], "cycle 0")
  , ("a bit vector of the wrong width", macProgram, macNormal, [[VBV 4 3, b8 1]], "cycle 0")
  , ("a bit vector on a Bool port", counterProgram, counterNormal, [[VBV 1 1]], "cycle 0")
  , ("a payload that does not fit its width", macProgram, macNormal, [[b8 256, b8 1]], "cycle 0")
  ,
    ( "a tuple on a scalar port"
    , counterProgram
    , counterNormal
    , [[VTuple [VBool True, VBool False]]]
    , "cycle 0"
    )
  ,
    ( "a bad row after good ones"
    , macProgram
    , macNormal
    , replicate 3 [b8 1, b8 2] <> [[b8 1]]
    , "cycle 3"
    )
  ,
    ( "a value for a top with no inputs"
    , freeCounterProgram 4
    , freeCounterNormal 4
    , [[], [VBool True]]
    , "cycle 1"
    )
  ]

rowsRejectSpec :: Spec
rowsRejectSpec = do
  for_ badRows $ \(what, prog, nm, rows, cyc) -> do
    it ("[sim-rows-reject] simulateCore rejects " <> what) $
      simulateCore prog rows `shouldBeSimError` cyc
    it ("[sim-rows-reject] simulateNormal rejects " <> what) $
      simulateNormal nm rows `shouldBeSimError` cyc
  -- Each circuit below fails in cycle 0 if it is run, so only a check of
  -- every row before the first cycle reports the bad row of cycle 2.
  it "[sim-rows-reject] simulateCore checks every row before it simulates a cycle" $ do
    r <- settled (simulateCore (doublingWork 18) [[b8 7], [b8 7], [b8 7, b8 8]])
    r `shouldBeSimError` "expected 1 input values"
    r `shouldBeSimError` "in cycle 2"
  it "[sim-rows-reject] simulateNormal checks every row before it simulates a cycle" $ do
    let readsLater =
          normalModule
            [("x", bv 8)]
            [NOutput "o" (bv 8) (AVar "a")]
            [ NBind "a" (bv 8) (NPrim BvAdd [AVar "b", ALit (b8 1)])
            , NBind "b" (bv 8) (NPrim BvAdd [AVar "x", ALit (b8 1)])
            ]
    simulateNormal readsLater [[b8 1], [b8 1], [b8 1, b8 2]]
      `shouldBeSimError` "expected 1 input values"
    simulateNormal readsLater [[b8 1], [b8 1], [b8 1, b8 2]] `shouldBeSimError` "in cycle 2"
