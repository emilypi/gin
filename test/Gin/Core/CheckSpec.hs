module Gin.Core.CheckSpec (spec) where

import Data.ByteString.Lazy qualified as LBS
import Data.Foldable (for_)
import Data.Text (Text)
import Data.Text qualified as Text
import Gin.Core.Check (checkProgram)
import Gin.Core.Json (decodeProgram)
import Gin.Core.Syntax
import Gin.Error
import Gin.Examples
import Numeric.Natural (Natural)
import Test.Hspec

----------------------------------------------------------------------
-- Helpers

v :: Text -> Expr
v = EVar . Name

lit8 :: Integer -> Expr
lit8 = ELit . VBV 8

-- | A prim node at the instantiated type @args -> res@.
prim :: PrimOp -> [Ty] -> Ty -> Expr
prim op args res = EPrim op (tFuns args res)

add8 :: Expr
add8 = prim BvAdd [bv 8, bv 8] (bv 8)

-- | counterProgram plus extra definitions that the top entity does not use.
withDefs :: [Def] -> Program
withDefs ds = counterProgram{progDefs = progDefs counterProgram <> ds}

-- | Check an expression at a declared type, as an extra definition.
checkAs :: Ty -> Expr -> Either GinError ()
checkAs t e = checkProgram (withDefs [Def "Test.subject" t e])

-- | A prim node checked at exactly its own annotated type.
checkPrim :: PrimOp -> Ty -> Either GinError ()
checkPrim op t = checkAs t (EPrim op t)

withTop :: (TopEntity -> TopEntity) -> Program -> Program
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
constantTop :: [Port] -> [Port] -> Ty -> Program
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
          [(Name ("in" <> Text.pack (show i)), sig (portTy p)) | (i, p) <- zip [0 :: Int ..] ins]
          constant

threeOutputs :: [Port]
threeOutputs = [Port "a" TBool, Port "b" TBool, Port "c" (bv 8)]

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
        checkAs (TProd [bv 8, bv 8]) (ETuple [EApp (ELam [("x", bv 8)] (v "x")) [lit8 1], v "x"])
    it "[check-rules] rejects a non-recursive let bind that refers to itself" $
      rejectedWith "unbound variable x" $
        checkAs (bv 8) (ELet False [Bind "x" (bv 8) (EApp add8 [v "x", lit8 1])] (v "x"))
    it "[check-rules] rejects a non-recursive let bind that refers to a later bind" $
      rejectedWith "unbound variable y" $
        checkAs (bv 8) (ELet False [Bind "x" (bv 8) (v "y"), Bind "y" (bv 8) (lit8 1)] (v "x"))
    it "[check-rules] lets a non-recursive bind see the earlier binds" $
      checkAs (bv 8) (ELet False [Bind "x" (bv 8) (lit8 1), Bind "y" (bv 8) (v "x")] (v "y"))
        `shouldBe` Right ()
    it "[check-rules] lets a recursive bind see later binds and itself" $
      checkAs
        (bv 8)
        ( ELet
            True
            [Bind "x" (bv 8) (v "y"), Bind "y" (bv 8) (EApp add8 [v "y", lit8 1])]
            (v "x")
        )
        `shouldBe` Right ()
    it "[check-rules] rejects let binds escaping into the enclosing scope" $
      rejectedWith "unbound variable x" $
        checkAs (TProd [bv 8, bv 8]) (ETuple [ELet False [Bind "x" (bv 8) (lit8 1)] (v "x"), v "x"])
    it "[check-rules] rejects duplicate binders in one lambda" $
      rejectedWith "duplicate binder s" $
        checkAs (tFuns [bv 8, bv 8] (bv 8)) (ELam [("s", bv 8), ("s", bv 8)] (v "s"))
    it "[check-rules] rejects duplicate names in one let" $
      rejectedWith "duplicate binder x" $
        checkAs (bv 8) (ELet True [Bind "x" (bv 8) (lit8 1), Bind "x" (bv 8) (lit8 2)] (v "x"))
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
        checkAs (bv 8) (EIf (ELit (VBV 1 1)) (lit8 1) (lit8 2))
    it "[check-rules] rejects a signal condition" $
      rejectedWith "condition" $
        checkAs (TFun (sig TBool) (bv 8)) (ELam [("c", sig TBool)] (EIf (v "c") (lit8 1) (lit8 2)))
    it "[check-rules] rejects branches of different types" $
      rejectedWith "branches" $
        checkAs (bv 8) (EIf (ELit (VBool True)) (lit8 1) (ELit (VBV 4 1)))
    it "[check-rules] rejects signal branches" $
      rejectedWith "branches" $
        checkAs
          (tFuns [sig (bv 8), sig (bv 8)] (sig (bv 8)))
          (ELam [("a", sig (bv 8)), ("b", sig (bv 8))] (EIf (ELit (VBool True)) (v "a") (v "b")))
    it "[check-rules] rejects function branches" $
      rejectedWith "branches" $
        checkAs
          (tFuns [bv 8] (bv 8))
          (EIf (ELit (VBool True)) (EApp add8 [lit8 1]) (EApp add8 [lit8 2]))
    it "[check-rules] rejects branches that are products containing a signal" $
      rejectedWith "branches" $
        checkAs
          (TFun (sig (bv 8)) (TProd [sig (bv 8), bv 8]))
          ( ELam
              [("a", sig (bv 8))]
              (EIf (ELit (VBool True)) (ETuple [v "a", lit8 1]) (ETuple [v "a", lit8 2]))
          )

  describe "tuples and projections" $ do
    it "[check-rules] accepts the last component of a tuple" $
      checkAs TBool (EProj 1 (ETuple [lit8 1, ELit (VBool True)])) `shouldBe` Right ()
    it "[check-rules] rejects a projection past the last component" $
      rejectedWith "out of range" $
        checkAs (bv 8) (EProj 2 (ETuple [lit8 1, lit8 2]))
    it "[check-rules] rejects a projection with an index beyond any machine integer" $
      rejectedWith "out of range" $
        checkAs (bv 8) (EProj (2 ^ (64 :: Int) :: Natural) (ETuple [lit8 1, lit8 2]))
    it "[check-rules] rejects a projection from a non-product" $
      rejectedWith "projection" $
        checkAs (bv 8) (EProj 0 (lit8 1))
    it "[check-rules] rejects a one-component tuple" $
      rejectedWith "tuple" $
        checkAs (TProd [bv 8, bv 8]) (ETuple [lit8 1])

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
          rejectedWith "invalid value" (checkAs (bv 8) (EProj 0 (ETuple [lit8 0, ELit value])))
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
        checkAs (bv 4) (ELet False [Bind "x" (bv 4) (lit8 1)] (v "x"))

  describe "top entity" $ do
    for_ ["Counter", "", "module", "gin_counter", "a__b", "counter_", "9lives", "wire"] $ \name ->
      it ("[check-rules] rejects the illegal top name " <> show name) $
        rejectedWith "top name" $
          checkProgram (withTop (\t -> t{topName = name}) counterProgram)
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
