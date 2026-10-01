-- | Tests for the normal-form invariant checker.
module Gin.NormalizeSpec (spec) where

import Data.Foldable (for_)
import Data.Text (Text)
import Data.Text qualified as Text
import Gin.Core.Normal
import Gin.Core.Syntax
import Gin.Error (GinError (..), Stage (..))
import Gin.Examples
import Gin.Limits (maxNormalBinds)
import Gin.Normalize (checkNormal)
import Test.Hspec

-- | A module of @k@ chained @bool.not@ binds, valid for @k <= maxNormalBinds@.
notChain :: Int -> NModule
notChain k =
  NModule
    { nmName = "chain"
    , nmDomain = sysDomain
    , nmInputs = [("en", TBool)]
    , nmOutputs = [NOutput "out" TBool (AVar (b (k - 1)))]
    , nmBinds = [NBind (b i) TBool (NPrim BoolNot [AVar (prev i)]) | i <- [0 .. k - 1]]
    , nmCertificate = testCertificate "Chain.chain_correct"
    }
  where
    b :: Int -> Name
    b i = Name ("b" <> Text.pack (show i))
    prev i = if i == 0 then "en" else b (i - 1)

shouldFailWith :: (Show a) => Either GinError a -> Text -> Expectation
shouldFailWith r needle = case r of
  Right a -> expectationFailure ("expected an error mentioning " <> show needle <> ": " <> show a)
  Left e -> do
    errStage e `shouldBe` StNormalize
    Text.unpack (errMessage e) `shouldContain` Text.unpack needle

----------------------------------------------------------------------
-- checkNormal mutants

setRhs :: Name -> NRhs -> NModule -> NModule
setRhs n r m = m {nmBinds = [if nbName b == n then b {nbRhs = r} else b | b <- nmBinds m]}

-- | One or more mutants of 'counterNormal' per invariant of
-- "Gin.Core.Normal", each violating only that invariant, with a fragment of
-- the expected error message.
mutants :: [(String, Text, NModule)]
mutants =
  [
    ( "1: an input of product type"
    , "not scalar"
    , c {nmInputs = nmInputs c <> [("pad", TProd [TBool, TBool])]}
    )
  , ("1: an input of width zero", "not scalar", c {nmInputs = nmInputs c <> [("pad", bv 0)]})
  , ("2: two inputs with the same name", "duplicate", c {nmInputs = [("en", TBool), ("en", TBool)]})
  , ("2: a bind named like an input", "duplicate", c {nmInputs = [("en", TBool), ("inc", bv 8)]})
  , ("2: two binds with the same name", "duplicate", c {nmBinds = [s, inc, inc, sNext]})
  ,
    ( "3: operands of different widths"
    , "ill-typed"
    , setRhs "inc" (NPrim BvAdd [AVar "s", ALit (VBV 4 1)]) c
    )
  , ("3: a signal prim in a bind", "ill-typed", setRhs "inc" (NPrim SigPure [AVar "s"]) c)
  , ("3: an unsaturated prim", "ill-typed", setRhs "inc" (NPrim BvAdd [AVar "s"]) c)
  ,
    ( "3: a tuple literal"
    , "ill-typed"
    , setRhs "inc" (NPrim BvAdd [AVar "s", ALit (VTuple [VBV 4 0, VBV 4 1])]) c
    )
  ,
    ( "3: a mux condition that is not Bool"
    , "ill-typed"
    , setRhs "s_next" (NMux (AVar "inc") (AVar "inc") (AVar "s")) c
    )
  ,
    ( "3: an output atom of another type"
    , "ill-typed"
    , c {nmOutputs = nmOutputs c <> [NOutput "flag" (bv 8) (AVar "en")]}
    )
  ,
    ( "4: a reference to an unbound name"
    , "undefined variable"
    , setRhs "s_next" (NMux (AVar "en") (AVar "inc") (AVar "ghost")) c
    )
  , ("5: a combinational forward reference", "topological", c {nmBinds = [s, sNext, inc]})
  ,
    ( "5: a combinational cycle"
    , "topological"
    , setRhs "inc" (NPrim BvAdd [AVar "s_next", ALit (VBV 8 1)]) c
    )
  ,
    ( "6: a register initial value of another width"
    , "initial value"
    , setRhs "s" (NReg (VBV 16 0) (AVar "s_next")) c
    )
  ,
    ( "6: an out-of-range register initial value"
    , "initial value"
    , setRhs "s" (NReg (VBV 8 256) (AVar "s_next")) c
    )
  ,
    ( "7: a dead bind"
    , "unreachable"
    , c {nmBinds = nmBinds c <> [NBind "dead" TBool (NPrim BoolNot [AVar "en"])]}
    )
  ,
    ( "7: a copy bind"
    , "copy"
    , c
        { nmOutputs = [NOutput "count" (bv 8) (AVar "cp")]
        , nmBinds = nmBinds c <> [NBind "cp" (bv 8) (NAtom (AVar "s"))]
        }
    )
  , ("8: one bind over the limit", "too many binds", notChain (maxNormalBinds + 1))
  ]
  where
    c = counterNormal
    s = NBind "s" (bv 8) (NReg (VBV 8 0) (AVar "s_next"))
    inc = NBind "inc" (bv 8) (NPrim BvAdd [AVar "s", ALit (VBV 8 1)])
    sNext = NBind "s_next" (bv 8) (NMux (AVar "en") (AVar "inc") (AVar "s"))

----------------------------------------------------------------------

fixtures :: [(String, NModule)]
fixtures = [("counter", counterNormal), ("mac", macNormal), ("detector", detectorNormal)]

spec :: Spec
spec = do
  describe "checkNormal" $ do
    for_ fixtures $ \(name, nm) ->
      it ("accepts the " <> name <> " fixture") $
        checkNormal nm `shouldBe` Right ()
    it "accepts exactly maxNormalBinds binds" $
      checkNormal (notChain maxNormalBinds) `shouldBe` Right ()
    for_ mutants $ \(name, needle, m) ->
      it ("[norm-mutants] rejects invariant " <> name) $
        checkNormal m `shouldFailWith` needle
