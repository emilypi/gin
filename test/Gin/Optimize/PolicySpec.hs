{-# LANGUAGE DataKinds #-}

module Gin.Optimize.PolicySpec (spec) where

import Control.Lens (set, view)
import Data.ByteString.Lazy.Char8 qualified as B
import Data.Either (isLeft)
import Data.Map.Strict qualified as M
import Gin.Core.Bounded
import Gin.Core.Prim (PrimOp (..))
import Gin.Core.Type (Ty (..))
import Gin.Optimize.Circuit (CircuitCosts (..), CircuitOptions (..))
import Gin.Optimize.Policy
import Test.Hspec
import Yolk qualified as Y

spec :: Spec
spec = describe "optimization policies" $ do
  it "decodes named objectives and applies width-weighted operator costs" $ do
    let bytes =
          "{\"format\":\"gin-policy/1\",\"objectives\":[{\"name\":\"area\",\"default\":1,\
            \\"widthWeighted\":true,\"operators\":{\"bv.mul\":9}},{\"name\":\"dsp\",\"def\
            \ault\":0,\"operators\":{\"bv.mul\":1}}]}"
    case decodePolicy bytes of
      Left e -> expectationFailure (show e)
      Right p -> do
        circuitPrimitiveCost (policyCosts p) (TBitVec 8) BvMul `shouldBe` [72, 1]
        circuitMuxCost (policyCosts p) TBool `shouldBe` [1, 0]
        decodePolicy (encodePolicy p) `shouldBe` Right p
  it "rejects duplicate keys, negative costs, unknown fields and wrong dimensions" $
    mapM_
      (\s -> decodePolicy (B.pack s) `shouldSatisfy` isLeft)
      [ "{\"format\":\"gin-policy/1\",\"format\":\"gin-policy/1\",\"objectives\":[]}"
      , "{\"format\":\"gin-policy/1\",\"objectives\":[{\"name\":\"x\",\"default\":-1}]}"
      , "{\"format\":\"gin-policy/1\",\"objectives\":[{\"name\":\"x\"}],\"upperBounds\":[\
        \1,2]}"
      , "{\"format\":\"gin-policy/1\",\"objectives\":[{\"name\":\"x\",\"operators\":{\"bv\
        \.mlu\":1}}]}"
      , "{\"format\":\"gin-policy/1\",\"objectives\":[{\"name\":\"x\"}],\"prefer\":[\"unk\
        \nown\"]}"
      , "{\"format\":\"gin-policy/1\",\"objectives\":[{\"name\":\"x\"},{\"name\":\"x\"}]}"
      , "{\"format\":\"gin-policy/1\",\"objectives\":[{\"name\":\"x\"}],\"timeoutSeconds\
        \\":0}"
      ]
  it "accepts a zero search budget without claiming infeasibility" $ do
    case decodePolicy
      "{\"format\":\"gin-policy/1\",\"objectives\":[{\"name\":\"x\"}],\"search\":{\"expan\
        \sions\":0,\"iterations\":0}}" of
      Left e -> expectationFailure (show e)
      Right p -> decodePolicy (encodePolicy p) `shouldBe` Right p
  it "checks every numeric search boundary during decoding" $
    mapM_
      ( \(field, valid, invalid) -> do
          mapM_
            ( \n ->
              decodePolicy (searchPolicy field n) `shouldSatisfy` either (const False)
                (const True)
            )
            valid
          mapM_ (\n -> decodePolicy (searchPolicy field n) `shouldSatisfy` isLeft) invalid
      )
      [ ("iterations", [0, 1000], [-1, 1001])
      , ("nodes", [1, 100000], [0, 100001])
      , ("matches", [0, 100000], [-1, 100001])
      , ("expansions", [0, 10000000], [-1, 10000001])
      , ("archive", [1, 4096], [0, 4097])
      , ("witnesses", [1, 64], [0, 65])
      ]
  it "derives dimensions from edited objective records and composes bounded optics" $
    case ( decodePolicy (searchPolicy "iterations" 8)
         , mkObjective "depth" (boundedIntLiteral @1) M.empty False
         ) of
      (Right p, Right objective) -> do
        let updated =
              set
                policyObjectivesL
                (policyObjectives p <> [objective])
                (set (policySearchL . searchIterationsL) (boundedIntLiteral @0) p)
        validatePolicy updated `shouldBe` Right ()
        view (policySearchL . searchIterationsL . boundedIntValue) updated `shouldBe` 0
        Y.paretoDimensions (circuitExtractionOptions (policyOptions updated)) `shouldBe` 2
        decodePolicy (encodePolicy updated) `shouldBe` Right updated
      result -> expectationFailure (show result)

searchPolicy :: String -> Int -> B.ByteString
searchPolicy field value =
  B.pack
    ( "{\"format\":\"gin-policy/1\",\"objectives\":[{\"name\":\"x\"}],\"search\":{\""
        <> field
        <> "\":"
        <> show value
        <> "}}"
    )
