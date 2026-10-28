module Gin.Optimize.PolicySpec (spec) where

import Data.ByteString.Lazy.Char8 qualified as B
import Data.Either (isLeft)
import Gin.Core.Prim (PrimOp (..))
import Gin.Core.Type (Ty (..))
import Gin.Optimize.Circuit (CircuitCosts (..))
import Gin.Optimize.Policy
import Test.Hspec

spec :: Spec
spec = describe "optimization policies" $ do
  it "decodes named objectives and applies width-weighted operator costs" $ do
    let bytes = "{\"format\":\"gin-policy/1\",\"objectives\":[{\"name\":\"area\",\"default\":1,\"widthWeighted\":true,\"operators\":{\"bv.mul\":9}},{\"name\":\"dsp\",\"default\":0,\"operators\":{\"bv.mul\":1}}]}"
    case decodePolicy bytes of
      Left e -> expectationFailure (show e)
      Right p -> do
        circuitPrimitiveCost (policyCosts p) (TBitVec 8) BvMul `shouldBe` [72,1]
        circuitMuxCost (policyCosts p) TBool `shouldBe` [1,0]
        decodePolicy (encodePolicy p) `shouldBe` Right p
  it "rejects duplicate keys, negative costs, unknown fields and wrong dimensions" $
    mapM_ (\s -> decodePolicy (B.pack s) `shouldSatisfy` isLeft)
      [ "{\"format\":\"gin-policy/1\",\"format\":\"gin-policy/1\",\"objectives\":[]}"
      , "{\"format\":\"gin-policy/1\",\"objectives\":[{\"name\":\"x\",\"default\":-1}]}"
      , "{\"format\":\"gin-policy/1\",\"objectives\":[{\"name\":\"x\"}],\"upperBounds\":[1,2]}"
      , "{\"format\":\"gin-policy/1\",\"objectives\":[{\"name\":\"x\",\"operators\":{\"bv.mlu\":1}}]}"
      , "{\"format\":\"gin-policy/1\",\"objectives\":[{\"name\":\"x\"}],\"prefer\":[\"unknown\"]}"
      , "{\"format\":\"gin-policy/1\",\"objectives\":[{\"name\":\"x\"},{\"name\":\"x\"}]}"
      , "{\"format\":\"gin-policy/1\",\"objectives\":[{\"name\":\"x\"}],\"timeoutSeconds\":0}"
      ]
  it "accepts a zero search budget without claiming infeasibility" $ do
    case decodePolicy "{\"format\":\"gin-policy/1\",\"objectives\":[{\"name\":\"x\"}],\"search\":{\"expansions\":0,\"iterations\":0}}" of
      Left e -> expectationFailure (show e)
      Right p -> decodePolicy (encodePolicy p) `shouldBe` Right p
