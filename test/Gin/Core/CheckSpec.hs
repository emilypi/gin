module Gin.Core.CheckSpec (spec) where

import Data.ByteString.Lazy qualified as LBS
import Data.Foldable (for_)
import Data.IntMap.Strict qualified as IntMap
import Data.Text (Text)
import Data.Text qualified as Text
import Gin.Core.Check (checkProgram)
import Gin.Core.Json (decodeProgram, encodeProgram)
import Gin.Core.Syntax
import Gin.Error
import Gin.Examples
import Gin.TestUtil (ifE, tshow)
import System.Timeout (timeout)
import Test.Hspec

----------------------------------------------------------------------
-- Helpers

v :: Text -> Expr Ty Name
v = EVar . Name

lit8 :: Integer -> Expr Ty Name
lit8 = ELit . VBV 8

-- | A prim node at the instantiated type @args -> res@.
prim :: PrimOp -> [Ty] -> Ty -> Expr Ty Name
prim op args res = EPrim op (tFuns args res)

add8 :: Expr Ty Name
add8 = prim BvAdd [bv 8, bv 8] (bv 8)

-- | counterProgram plus extra definitions that the top entity does not use.
withDefs :: [Def Ty Name] -> Program Ty Name
withDefs ds = counterProgram{progDefs = progDefs counterProgram <> ds}

-- | Check an expression at a declared type, as an extra definition.
checkAs :: Ty -> Expr Ty Name -> Either GinError ()
checkAs t e = checkProgram (withDefs [Def "Test.subject" t e])

-- | A prim node checked at exactly its own annotated type.
checkPrim :: PrimOp -> Ty -> Either GinError ()
checkPrim op t = checkAs t (EPrim op t)

withTop :: (TopEntity Ty Name -> TopEntity Ty Name) -> Program Ty Name -> Program Ty Name
withTop f p = p{progTop = f (progTop p)}

-- | A type-checker error whose message mentions the fragment.
rejectedWith :: Text -> Either GinError () -> Expectation
rejectedWith fragment = \case
  Left e -> do
    errStage e `shouldBe` StCheck
    Text.unpack (errMessage e) `shouldContain` Text.unpack fragment
  Right () -> expectationFailure "expected a type error, but the program was accepted"

-- | Some value of a data type.
someValue :: Ty -> Value
someValue = \case
  TBitVec w -> VBV w 0
  TProd ts -> VTuple (fmap someValue ts)
  _ -> VBool False

-- | A top entity with one input @x : bv 8@ and the given output ports,
-- whose definition ignores @x@ and outputs a constant of type @o@.
constantTop :: [Port Ty] -> [Port Ty] -> Ty -> Program Ty Name
constantTop ins outs o =
  Program
    { progProducer = progProducer counterProgram
    , progTop =
        TopEntity
          { topName = "consts"
          , topDomain = sysDomain
          , topInputs = ins
          , topOutputs = outs
          , topDef = "Consts.consts"
          }
    , progDefs = [Def "Consts.consts" defTy body]
    , progCertificate = testCertificate "Consts.consts_correct"
    }
  where
    defTy = tFuns (fmap (sig . portTy) ins) (sig o)
    constant = EApp (prim SigPure [o] (sig o)) [ELit (someValue o)]
    body = case ins of
      [] -> constant
      _ ->
        ELam
          [(Name ("in" <> tshow i), sig (portTy p)) | (i, p) <- zip [0 :: Int ..] ins]
          constant

threeOutputs :: [Port Ty]
threeOutputs = [Port "a" TBool, Port "b" TBool, Port "c" (bv 8)]

-- | Port names that are not legal HDL identifiers: wrong case or
-- characters, empty, a leading digit, double or trailing underscores, the
-- backends' prefix, reserved words of the target languages, too long, and
-- characters that would break an output line.
illegalPortNames :: [Text]
illegalPortNames =
  [ "Count"
  , ""
  , "9lives"
  , "a__b"
  , "x_"
  , "gin_x"
  , "wire"
  , "now"
  , "in"
  , "signal"
  , "a b"
  , Text.replicate 65 "a"
  , "x\n"
  , "x\r"
  , "x\x202E"
  ]

-- | A correctly instantiated type for every primitive.
wellTypedPrims :: [(PrimOp, Ty)]
wellTypedPrims =
  [ (BoolAnd, tFuns [TBool, TBool] TBool)
  , (BoolOr, tFuns [TBool, TBool] TBool)
  , (BoolXor, tFuns [TBool, TBool] TBool)
  , (BoolNot, tFuns [TBool] TBool)
  , (BoolEq, tFuns [TBool, TBool] TBool)
  , (BvAdd, tFuns [bv 8, bv 8] (bv 8))
  , (BvSub, tFuns [bv 8, bv 8] (bv 8))
  , (BvMul, tFuns [bv 16, bv 16] (bv 16))
  , (BvNeg, tFuns [bv 8] (bv 8))
  , (BvAnd, tFuns [bv 1, bv 1] (bv 1))
  , (BvOr, tFuns [bv 4096, bv 4096] (bv 4096))
  , (BvXor, tFuns [bv 3, bv 3] (bv 3))
  , (BvNot, tFuns [bv 8] (bv 8))
  , (BvShl 3, tFuns [bv 8] (bv 8))
  , (BvShl 100, tFuns [bv 8] (bv 8))
  , (BvLshr 0, tFuns [bv 8] (bv 8))
  , (BvEq, tFuns [bv 8, bv 8] TBool)
  , (BvUlt, tFuns [bv 8, bv 8] TBool)
  , (BvUle, tFuns [bv 8, bv 8] TBool)
  , (BvConcat, tFuns [bv 3, bv 5] (bv 8))
  , (BvExtract 7 4, tFuns [bv 8] (bv 4))
  , (BvExtract 0 0, tFuns [bv 1] (bv 1))
  , (BvZext 16, tFuns [bv 8] (bv 16))
  , (BvZext 8, tFuns [bv 8] (bv 8))
  , (BvOfBool, tFuns [TBool] (bv 1))
  , (SigPure, tFuns [TProd [bv 8, TBool]] (sig (TProd [bv 8, TBool])))
  , (SigLift 1, tFuns [tFuns [bv 8] TBool, sig (bv 8)] (sig TBool))
  , (SigLift 2, tFuns [tFuns [bv 8, TBool] (bv 4), sig (bv 8), sig TBool] (sig (bv 4)))
  , (SigRegister (VBV 8 7), tFuns [sig (bv 8)] (sig (bv 8)))
  ,
    ( SigRegister (VTuple [VBool True, VBV 2 3])
    , tFuns [sig (TProd [TBool, bv 2])] (sig (TProd [TBool, bv 2]))
    )
  ,
    ( SigMealy (VBV 2 0)
    , tFuns [tFuns [bv 2, TBool] (TProd [bv 2, bv 8]), sig TBool] (sig (bv 8))
    )
  ]

-- | Primitive nodes whose annotated type breaks the rules in "Gin.Core.Prim".
illTypedPrims :: [(String, PrimOp, Ty)]
illTypedPrims =
  [ ("bool.and at bit vectors", BoolAnd, tFuns [bv 1, bv 1] (bv 1))
  , ("bool.not with two arguments", BoolNot, tFuns [TBool, TBool] TBool)
  , ("bool.eq returning a bit vector", BoolEq, tFuns [TBool, TBool] (bv 1))
  , ("bv.add with mismatched argument widths", BvAdd, tFuns [bv 8, bv 4] (bv 8))
  , ("bv.add with a wider result", BvAdd, tFuns [bv 8, bv 8] (bv 9))
  , ("bv.mul at Bool", BvMul, tFuns [TBool, TBool] TBool)
  , ("bv.neg changing width", BvNeg, tFuns [bv 8] (bv 4))
  , ("bv.shl changing width", BvShl 1, tFuns [bv 8] (bv 9))
  , ("bv.lshr with two arguments", BvLshr 1, tFuns [bv 8, bv 8] (bv 8))
  , ("bv.ult returning a bit vector", BvUlt, tFuns [bv 8, bv 8] (bv 1))
  , ("bv.eq with mismatched widths", BvEq, tFuns [bv 8, bv 7] TBool)
  , ("bv.concat with the wrong result width", BvConcat, tFuns [bv 4, bv 4] (bv 4))
  , ("bv.extract with hi equal to the width", BvExtract 8 0, tFuns [bv 8] (bv 9))
  , ("bv.extract with hi below lo", BvExtract 2 3, tFuns [bv 8] (bv 1))
  , ("bv.extract with the wrong result width", BvExtract 3 0, tFuns [bv 8] (bv 3))
  , ("bv.zext narrowing", BvZext 4, tFuns [bv 8] (bv 4))
  , ("bv.zext to a width other than its parameter", BvZext 16, tFuns [bv 8] (bv 12))
  , ("bv.ofBool producing two bits", BvOfBool, tFuns [TBool] (bv 2))
  , ("sig.pure changing the element type", SigPure, tFuns [TBool] (sig (bv 1)))
  , ("sig.pure of a function", SigPure, tFuns [TFun TBool TBool] (sig TBool))
  , ("sig.pure of a signal", SigPure, tFuns [sig TBool] (sig TBool))
  , ("sig.lift 0", SigLift 0, tFuns [TBool] (sig TBool))
  ,
    ( "sig.lift 2 given one signal"
    , SigLift 2
    , tFuns [tFuns [bv 8, bv 8] (bv 8), sig (bv 8)] (sig (bv 8))
    )
  ,
    ( "sig.lift with a mismatched signal element"
    , SigLift 1
    , tFuns [tFuns [bv 8] TBool, sig (bv 4)] (sig TBool)
    )
  ,
    ( "sig.lift with a mismatched result"
    , SigLift 1
    , tFuns [tFuns [bv 8] TBool, sig (bv 8)] (sig (bv 8))
    )
  ,
    ( "sig.register with an initial value of another type"
    , SigRegister (VBool False)
    , tFuns [sig (bv 8)] (sig (bv 8))
    )
  ,
    ( "sig.register with an invalid initial value"
    , SigRegister (VBV 8 256)
    , tFuns [sig (bv 8)] (sig (bv 8))
    )
  ,
    ( "sig.register changing the element type"
    , SigRegister (VBV 8 0)
    , tFuns [sig (bv 8)] (sig (bv 4))
    )
  ,
    ( "sig.mealy with an initial state of another type"
    , SigMealy (VBV 4 0)
    , tFuns [tFuns [bv 8, TBool] (TProd [bv 8, bv 8]), sig TBool] (sig (bv 8))
    )
  ,
    ( "sig.mealy whose step does not return a (state, output) pair"
    , SigMealy (VBV 8 0)
    , tFuns [tFuns [bv 8, TBool] (bv 8), sig TBool] (sig (bv 8))
    )
  ,
    ( "sig.mealy whose step returns the wrong next-state type"
    , SigMealy (VBV 8 0)
    , tFuns [tFuns [bv 8, TBool] (TProd [bv 4, bv 8]), sig TBool] (sig (bv 8))
    )
  ,
    ( "sig.mealy whose input signal disagrees with the step"
    , SigMealy (VBV 8 0)
    , tFuns [tFuns [bv 8, TBool] (TProd [bv 8, bv 8]), sig (bv 1)] (sig (bv 8))
    )
  ]

-- | Ill-formed types, each with the message fragment it is rejected with
-- and a primitive whose annotation contains it but otherwise follows the
-- rules in "Gin.Core.Prim".
illFormedTypes :: [(String, Ty, Text, Expr Ty Name)]
illFormedTypes =
  [
    ( "a signal in another domain"
    , TSignal "Other" TBool
    , "domain"
    , EPrim SigPure (TFun TBool (TSignal "Other" TBool))
    )
  , ("a zero-width bit vector", bv 0, "width", EPrim BvNot (TFun (bv 0) (bv 0)))
  ,
    ( "a bit vector wider than the maximum width"
    , bv 4097
    , "width"
    , EPrim BvConcat (tFuns [bv 4096, bv 1] (bv 4097))
    )
  ,
    ( "a one-component product"
    , TProd [TBool]
    , "product"
    , EPrim SigPure (TFun (TProd [TBool]) (sig (TProd [TBool])))
    )
  ]

-- | Check an expression as the first component of a pair projected away,
-- so that its type never reaches the declared type of the definition and
-- only the annotations inside the expression can reject it.
checkHidden :: Expr Ty Name -> Either GinError ()
checkHidden e = checkAs (bv 8) (EProj 1 (mkTuple [e, lit8 1]))

-- | Fail if the expectation takes longer than 5 s.
promptly :: Expectation -> Expectation
promptly act =
  timeout 5000000 act >>= \case
    Just () -> pure ()
    Nothing -> expectationFailure "checking took longer than 5 s"

-- | A product of @n@ Bools, about 15 bytes of JSON per component.
bools :: Int -> Ty
bools n = TProd (replicate n TBool)

-- | Components in each hostile program below. Their JSON encodings are
-- 1.5 to 4.5 MB, well under the input limit, yet a checker that walks a
-- type at each use takes about a billion steps on each of them: far longer
-- than 'promptly' allows (or more memory than a test has). That is the
-- checker I want these programs to catch.
hostileSize :: Int
hostileSize = 32000

-- | Programs that use a wide type many times without spelling it out at
-- each use, so that walking the type at every use costs time quadratic in
-- the size of the input. Each comes with whether it type-checks.
hostilePrograms :: [(String, Program Ty Name, Bool)]
hostilePrograms =
  [
    ( "a body whose type repeats a wide binder type"
    , single (TFun wide TBool) (ELam [("x", wide)] (mkTuple (replicate n (v "x"))))
    , False
    )
  ,
    ( "a conditional whose branches repeat a wide binder type"
    , single
        (TFun wide wide)
        ( ELam
            [("x", wide)]
            (EProj 0 (ifE (ELit (VBool True)) (mkTuple copies) (mkTuple copies)))
        )
    , True
    )
  ,
    ( "many applications to an argument of a wide type"
    , single
        (tFuns [wide, TFun wide TBool] (bools n))
        ( ELam
            [("x", wide), ("f", TFun wide TBool)]
            (mkTuple (replicate n (EApp (v "f") [v "x"])))
        )
    , True
    )
  ,
    ( "many projections of the last component of a wide tuple"
    , single
        (TFun wide (bools n))
        (ELam [("x", wide)] (mkTuple (replicate n (EProj (n - 1) (v "x")))))
    , True
    )
  ]
  where
    n = hostileSize
    wide = bools n
    copies = replicate n (v "x")
    single t body = withDefs [Def "Test.subject" t body]

----------------------------------------------------------------------

spec :: Spec
spec = do
  describe "accepted programs" $ do
    it "[check-examples] accepts counterProgram" $
      checkProgram counterProgram `shouldBe` Right ()
    it "[check-examples] accepts macProgram" $
      checkProgram macProgram `shouldBe` Right ()
    it "[check-examples] accepts detectorProgram" $
      checkProgram detectorProgram `shouldBe` Right ()
    it "[check-examples] accepts the decoded counter fixture" $ do
      bytes <- LBS.readFile "test/fixtures/ir/counter.gin.json"
      (decodeProgram bytes >>= checkProgram) `shouldBe` Right ()
    it "[check-examples] accepts a top entity with no inputs" $
      checkProgram (constantTop [] [Port "q" (bv 8)] (bv 8)) `shouldBe` Right ()
    it "[check-examples] accepts two outputs as a binary product" $
      checkProgram (constantTop [Port "x" (bv 8)] (take 2 threeOutputs) (TProd [TBool, TBool]))
        `shouldBe` Right ()
    it "[check-examples] accepts three outputs as a right-nested product" $
      checkProgram
        (constantTop [Port "x" (bv 8)] threeOutputs (TProd [TBool, TProd [TBool, bv 8]]))
        `shouldBe` Right ()
    it "[check-examples] accepts every primitive at a correctly instantiated type" $
      for_ wellTypedPrims $
        \(op, t) -> checkPrim op t `shouldBe` Right ()
    it "[check-examples] accepts partial application of a primitive" $
      checkAs (TFun (bv 8) (bv 8)) (EApp add8 [lit8 1]) `shouldBe` Right ()
    it "[check-examples] accepts a reference to another definition" $
      checkProgram
        ( withDefs
            [ Def "Test.one" (bv 8) (lit8 1)
            , Def "Test.two" (bv 8) (EApp add8 [EGlobal "Test.one", EGlobal "Test.one"])
            ]
        )
        `shouldBe` Right ()

  describe "definitions and globals" $ do
    it "[check-rules] rejects duplicate definition names" $
      rejectedWith "duplicate definition Counter.counter" $
        checkProgram (withDefs (progDefs counterProgram))
    it "[check-rules] rejects a reference to an unknown global" $
      rejectedWith "unknown global Test.missing" $
        checkAs (bv 8) (EGlobal "Test.missing")
    it "[check-rules] rejects a definition that refers to itself" $
      rejectedWith "Test.loop" $
        checkProgram (withDefs [Def "Test.loop" (bv 8) (EApp add8 [EGlobal "Test.loop", lit8 1])])
    it "[check-rules] rejects mutually recursive definitions" $ do
      let result =
            checkProgram
              ( withDefs
                  [ Def "Test.a" (bv 8) (EGlobal "Test.b")
                  , Def "Test.b" (bv 8) (EGlobal "Test.c")
                  , Def "Test.c" (bv 8) (EGlobal "Test.a")
                  ]
              )
      rejectedWith "recursive" result
      rejectedWith "Test.a -> Test.b -> Test.c -> Test.a" result
    it "[check-rules] rejects a body whose type differs from the declared type" $
      rejectedWith "BitVec 4" $
        checkAs (bv 4) (lit8 1)

  describe "scoping" $ do
    it "[check-rules] rejects an unbound variable" $
      rejectedWith "unbound variable x" $
        checkAs (bv 8) (v "x")
    it "[check-rules] rejects a lambda-bound variable used outside its lambda" $
      rejectedWith "unbound variable x" $
        checkAs (TProd [bv 8, bv 8]) (mkTuple [EApp (ELam [("x", bv 8)] (v "x")) [lit8 1], v "x"])
    it "[check-rules] rejects a non-recursive let bind that refers to itself" $
      rejectedWith "unbound variable x" $
        checkAs (bv 8) (ELet [Bind "x" (bv 8) (EApp add8 [v "x", lit8 1])] (v "x"))
    it "[check-rules] rejects a non-recursive let bind that refers to a later bind" $
      rejectedWith "unbound variable y" $
        checkAs (bv 8) (ELet [Bind "x" (bv 8) (v "y"), Bind "y" (bv 8) (lit8 1)] (v "x"))
    it "[check-rules] lets a non-recursive bind see the earlier binds" $
      checkAs (bv 8) (ELet [Bind "x" (bv 8) (lit8 1), Bind "y" (bv 8) (v "x")] (v "y"))
        `shouldBe` Right ()
    it "[check-rules] lets a recursive bind see later binds and itself" $
      checkAs
        (bv 8)
        ( ELetRec
            [Bind "x" (bv 8) (v "y"), Bind "y" (bv 8) (EApp add8 [v "y", lit8 1])]
            (v "x")
        )
        `shouldBe` Right ()
    it "[check-rules] rejects let binds escaping into the enclosing scope" $
      rejectedWith "unbound variable x" $
        checkAs (TProd [bv 8, bv 8]) (mkTuple [ELet [Bind "x" (bv 8) (lit8 1)] (v "x"), v "x"])
    it "[check-rules] rejects duplicate binders in one lambda" $
      rejectedWith "duplicate binder s" $
        checkAs (tFuns [bv 8, bv 8] (bv 8)) (ELam [("s", bv 8), ("s", bv 8)] (v "s"))
    it "[check-rules] rejects duplicate names in one let" $
      rejectedWith "duplicate binder x" $
        checkAs (bv 8) (ELetRec [Bind "x" (bv 8) (lit8 1), Bind "x" (bv 8) (lit8 2)] (v "x"))
    it "[check-rules] allows an inner lambda to shadow an outer binder" $
      checkAs (tFuns [bv 8, TBool] TBool) (ELam [("x", bv 8)] (ELam [("x", TBool)] (v "x")))
        `shouldBe` Right ()
    it "[check-rules] rejects a lambda with no binders" $
      rejectedWith "lambda" $
        checkAs (bv 8) (ELam [] (lit8 1))
    it "[check-rules] rejects a binder whose type annotation differs from its use" $
      rejectedWith "argument 1" $
        checkAs (TFun TBool (bv 8)) (ELam [("b", TBool)] (EApp add8 [v "b", lit8 1]))

  describe "primitives" $ for_ illTypedPrims $ \(name, op, t) ->
    it ("[check-rules] rejects " <> name) $
      rejectedWith (primName op) (checkPrim op t)

  describe "applications" $ do
    it "[check-rules] rejects an argument of the wrong type" $
      rejectedWith "argument 2" $
        checkAs (bv 8) (EApp add8 [lit8 1, ELit (VBool True)])
    it "[check-rules] rejects applying a non-function" $
      rejectedWith "cannot apply" $
        checkAs (bv 8) (EApp (lit8 1) [lit8 2])
    it "[check-rules] rejects too many arguments" $
      rejectedWith "cannot apply" $
        checkAs (bv 8) (EApp add8 [lit8 1, lit8 2, lit8 3])
    it "[check-rules] rejects an application with no arguments" $
      rejectedWith "application" $
        checkAs (tFuns [bv 8, bv 8] (bv 8)) (EApp add8 [])

  describe "conditionals" $ do
    it "[check-rules] rejects a bit-vector condition" $
      rejectedWith "condition" $
        checkAs (bv 8) (ifE (ELit (VBV 1 1)) (lit8 1) (lit8 2))
    it "[check-rules] rejects a signal condition" $
      rejectedWith "condition" $
        checkAs (TFun (sig TBool) (bv 8)) (ELam [("c", sig TBool)] (ifE (v "c") (lit8 1) (lit8 2)))
    it "[check-rules] rejects branches of different types" $
      rejectedWith "branches" $
        checkAs (bv 8) (ifE (ELit (VBool True)) (lit8 1) (ELit (VBV 4 1)))
    it "[check-rules] rejects signal branches" $
      rejectedWith "branches" $
        checkAs
          (tFuns [sig (bv 8), sig (bv 8)] (sig (bv 8)))
          (ELam [("a", sig (bv 8)), ("b", sig (bv 8))] (ifE (ELit (VBool True)) (v "a") (v "b")))
    it "[check-rules] rejects function branches" $
      rejectedWith "branches" $
        checkAs
          (tFuns [bv 8] (bv 8))
          (ifE (ELit (VBool True)) (EApp add8 [lit8 1]) (EApp add8 [lit8 2]))
    it "[check-rules] rejects branches that are products containing a signal" $
      rejectedWith "branches" $
        checkAs
          (TFun (sig (bv 8)) (TProd [sig (bv 8), bv 8]))
          ( ELam
              [("a", sig (bv 8))]
              (ifE (ELit (VBool True)) (mkTuple [v "a", lit8 1]) (mkTuple [v "a", lit8 2]))
          )
    it "[check-rules] accepts a multi-way if" $
      checkAs (bv 8) (EIf [(ELit (VBool False), lit8 1), (ELit (VBool True), lit8 2)] (lit8 3))
        `shouldBe` Right ()
    it "[check-rules] rejects a bit-vector condition after the first" $
      rejectedWith "condition" $
        checkAs (bv 8) (EIf [(ELit (VBool True), lit8 1), (ELit (VBV 1 1), lit8 2)] (lit8 3))
    it "[check-rules] rejects a later branch of a different type" $
      rejectedWith "branches" $
        checkAs (bv 8) (EIf [(ELit (VBool True), lit8 1), (ELit (VBool True), ELit (VBV 4 1))] (lit8 3))
    it "[check-rules] rejects an if with no conditions" $
      rejectedWith "no conditions" $
        checkAs (bv 8) (EIf [] (lit8 1))

  describe "tuples and projections" $ do
    it "[check-rules] accepts the last component of a tuple" $
      checkAs TBool (EProj 1 (mkTuple [lit8 1, ELit (VBool True)])) `shouldBe` Right ()
    it "[check-rules] rejects a projection past the last component" $
      rejectedWith "out of range" $
        checkAs (bv 8) (EProj 2 (mkTuple [lit8 1, lit8 2]))
    it "[check-rules] rejects a negative projection index" $
      rejectedWith "out of range" $
        checkAs (bv 8) (EProj (-1) (mkTuple [lit8 1, lit8 2]))
    it "[check-rules] rejects a projection at the largest key" $
      rejectedWith "out of range" $
        checkAs (bv 8) (EProj maxBound (mkTuple [lit8 1, lit8 2]))
    it "[check-rules] rejects a projection from a non-product" $
      rejectedWith "projection" $
        checkAs (bv 8) (EProj 0 (lit8 1))
    it "[check-rules] rejects a one-component tuple" $
      rejectedWith "tuple" $
        checkAs (TProd [bv 8, bv 8]) (mkTuple [lit8 1])
    it "[check-rules] rejects a tuple whose keys skip a position" $
      rejectedWith "tuple keys" $
        checkAs (TProd [bv 8, bv 8]) (ETuple (IntMap.fromList [(0, lit8 1), (2, lit8 2)]))

  describe "values and types" $ do
    for_
      [ ("a bit vector at its width bound", VBV 8 256)
      , ("a negative bit vector", VBV 8 (-1))
      , ("a zero-width bit vector", VBV 0 0)
      , ("a bit vector wider than the maximum width", VBV 4097 0)
      , ("a one-component tuple", VTuple [VBool True])
      , ("a tuple with an invalid component", VTuple [VBool True, VBV 1 2])
      ]
      $ \(name, value) ->
        it ("[check-rules] rejects " <> name <> " as a literal") $
          rejectedWith "invalid value" (checkAs (bv 8) (EProj 0 (mkTuple [lit8 0, ELit value])))
    it "[check-rules] rejects a zero-width bit-vector type" $
      rejectedWith "width" $
        checkAs (TFun (bv 0) (bv 0)) (ELam [("x", bv 0)] (v "x"))
    it "[check-rules] rejects a bit-vector type wider than the maximum width" $
      rejectedWith "width" $
        checkAs (TFun (bv 4097) (bv 4097)) (ELam [("x", bv 4097)] (v "x"))
    it "[check-rules] rejects a one-component product type" $
      rejectedWith "product" $
        checkAs (TFun (TProd [TBool]) (TProd [TBool])) (ELam [("x", TProd [TBool])] (v "x"))
    it "[check-rules] rejects a signal of functions" $
      rejectedWith "signal" $
        checkAs
          (TFun (sig (TFun TBool TBool)) (sig (TFun TBool TBool)))
          (ELam [("f", sig (TFun TBool TBool))] (v "f"))
    it "[check-rules] rejects a let bind whose value differs from its annotation" $
      rejectedWith "BitVec 4" $
        checkAs (bv 4) (ELet [Bind "x" (bv 4) (lit8 1)] (v "x"))

  describe "annotations inside expressions" $ do
    it "[check-rules] accepts well-formed annotations in a projected-away component" $ do
      checkHidden (EPrim SigPure (TFun TBool (sig TBool))) `shouldBe` Right ()
      checkHidden (ELam [("x", bv 8)] (v "x")) `shouldBe` Right ()
      checkHidden (ELetRec [Bind "x" (sig TBool) (v "x")] (lit8 1)) `shouldBe` Right ()
    for_ illFormedTypes $ \(name, t, fragment, primNode) -> do
      it ("[check-rules] rejects a primitive annotated with " <> name) $
        rejectedWith fragment (checkHidden primNode)
      it ("[check-rules] rejects a lambda binder annotated with " <> name) $
        rejectedWith fragment (checkHidden (ELam [("x", t)] (v "x")))
      it ("[check-rules] rejects a let bind annotated with " <> name) $
        rejectedWith fragment (checkHidden (ELetRec [Bind "x" t (v "x")] (lit8 1)))

  describe "input size" $ do
    it "[check-rules] shortens a wide type in a message, keeping its shape" $ do
      let result = checkAs (TFun (bools 20) (bools 3)) (ELam [("x", bools 20)] (v "x"))
          eight = Text.intercalate ", " (replicate 8 "Bool")
      rejectedWith ("has type (" <> eight <> ", ... 12 more) -> (" <> eight <> ", ...") result
      rejectedWith ("declared (" <> eight <> ", ... 12 more) -> (Bool, Bool, Bool)") result
    for_ hostilePrograms $ \(name, program, accepted) ->
      it ("[check-rules] checks " <> name <> " promptly") $ promptly $ do
        let bytes = encodeProgram program
        LBS.length bytes `shouldSatisfy` (> 1000000)
        case decodeProgram bytes >>= checkProgram of
          Right () -> accepted `shouldBe` True
          Left e -> do
            accepted `shouldBe` False
            errStage e `shouldBe` StCheck
            Text.length (errMessage e) `shouldSatisfy` (< 1000)

  describe "top entity" $ do
    for_ ["Counter", "", "module", "gin_counter", "a__b", "counter_", "9lives", "wire"] $ \name ->
      it ("[check-rules] rejects the illegal top name " <> show name) $
        rejectedWith "top name" $
          checkProgram (withTop (\t -> t{topName = name}) counterProgram)
    for_ illegalPortNames $ \name -> do
      it ("[check-ports] rejects the illegal input port name " <> show name) $
        rejectedWith "illegal port name" $
          checkProgram (constantTop [Port name (bv 8)] [Port "q" TBool] TBool)
      it ("[check-ports] rejects the illegal output port name " <> show name) $
        rejectedWith "illegal port name" $
          checkProgram (constantTop [Port "x" (bv 8)] [Port name TBool] TBool)
    for_ [("clk", "clock"), ("rst", "reset")] $ \(name, what) -> do
      it ("[check-ports] rejects an input port named " <> show name) $
        rejectedWith ("port name " <> name <> " is reserved for the " <> what) $
          checkProgram (constantTop [Port name TBool] [Port "q" TBool] TBool)
      it ("[check-ports] rejects an output port named " <> show name) $
        rejectedWith ("port name " <> name <> " is reserved for the " <> what) $
          checkProgram (constantTop [Port "x" (bv 8)] [Port name TBool] TBool)
    for_ [("clk", "clock"), ("rst", "reset")] $ \(name, what) ->
      it ("[check-ports] rejects a top entity named " <> show name) $
        rejectedWith ("top name " <> name <> " is reserved for the " <> what) $
          checkProgram (withTop (\t -> t{topName = name}) counterProgram)
    it "[check-ports] rejects an input port named like the top entity" $
      rejectedWith "port name consts equals the top name" $
        checkProgram (constantTop [Port "consts" (bv 8)] [Port "q" TBool] TBool)
    it "[check-ports] rejects an output port named like the top entity" $
      rejectedWith "port name counter equals the top name" $
        checkProgram (withTop (\t -> t{topOutputs = [Port "counter" (bv 8)]}) counterProgram)
    it "[check-ports] accepts port names that only contain clk, rst or the top name" $
      checkProgram
        ( constantTop
            [Port "clk_en" TBool, Port "rst_n" TBool, Port "consts_in" (bv 8)]
            [Port "clock" TBool, Port "reset" TBool, Port "consts1" (bv 8)]
            (TProd [TBool, TProd [TBool, bv 8]])
        )
        `shouldBe` Right ()
    it "[check-ports] reports a port name with control characters escaped, in the top entity" $
      case checkProgram (constantTop [Port "x\nsim-core: PASS\ESC[2J" (bv 8)] [Port "q" TBool] TBool) of
        Left e -> do
          errStage e `shouldBe` StCheck
          errContext e `shouldBe` ["in top entity"]
          Text.unpack (errMessage e) `shouldContain` "illegal port name"
          errMessage e `shouldSatisfy` Text.all (\c -> c /= '\n' && c /= '\ESC')
        Right () -> expectationFailure "expected a type error"
    it "[check-rules] rejects an input and an output with the same name" $
      rejectedWith "duplicate port name en" $
        checkProgram (constantTop [Port "en" (bv 8)] [Port "en" TBool] TBool)
    it "[check-rules] rejects two inputs with the same name" $
      rejectedWith "duplicate port name x" $
        checkProgram (constantTop [Port "x" (bv 8), Port "x" TBool] [Port "q" TBool] TBool)
    it "[check-rules] rejects a product-typed port" $
      rejectedWith "scalar" $
        checkProgram (constantTop [] [Port "q" (TProd [TBool, TBool])] (TProd [TBool, TBool]))
    it "[check-rules] rejects a signal-typed port" $
      rejectedWith "scalar" $
        checkProgram (constantTop [Port "x" (sig TBool)] [Port "q" TBool] TBool)
    it "[check-rules] rejects a top entity with no outputs" $
      rejectedWith "output" $
        checkProgram (withTop (\t -> t{topOutputs = []}) counterProgram)
    it "[check-rules] rejects a top definition that does not exist" $
      rejectedWith "Counter.missing" $
        checkProgram (withTop (\t -> t{topDef = "Counter.missing"}) counterProgram)
    it "[check-rules] rejects a top definition whose type differs from the ports" $
      rejectedWith "top definition" $
        checkProgram (withTop (\t -> t{topInputs = [Port "en" (bv 1)]}) counterProgram)
    it "[check-rules] rejects three outputs as a left-nested product" $
      rejectedWith "top definition" $
        checkProgram
          (constantTop [Port "x" (bv 8)] threeOutputs (TProd [TProd [TBool, TBool], bv 8]))
    it "[check-rules] rejects three outputs as a flat product" $
      rejectedWith "top definition" $
        checkProgram (constantTop [Port "x" (bv 8)] threeOutputs (TProd [TBool, TBool, bv 8]))
    it "[check-rules] rejects a top entity in a domain its signals do not use" $
      rejectedWith "domain" $
        checkProgram (withTop (\t -> t{topDomain = Domain "Fast" 5000}) counterProgram)
    it "[check-rules] rejects a signal in another domain in any definition" $
      rejectedWith "domain" $
        checkProgram
          ( withDefs
              [ Def
                  "Test.other"
                  (TFun (TSignal "Other" TBool) (TSignal "Other" TBool))
                  (ELam [("s", TSignal "Other" TBool)] (v "s"))
              ]
          )
    it "[check-rules] names the definition an error occurs in" $
      case checkAs (bv 8) (v "x") of
        Left e -> errContext e `shouldContain` ["in def Test.subject"]
        Right () -> expectationFailure "expected a type error"
