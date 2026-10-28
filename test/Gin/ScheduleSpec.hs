module Gin.ScheduleSpec (spec) where

import Data.Either (isLeft)
import Gin.Core.Normal
import Gin.Core.Syntax
import Gin.Examples (counterNormal, sysDomain, testCertificate)
import Gin.Schedule
import Gin.Sim (simulateNormal)
import Test.Hspec

spec :: Spec
spec = describe "fixed latency scheduling" $ do
  it "aligns reconvergent short and long paths for every small input" $ do
    let circuit = NModule "pipeline" sysDomain [("x",TBitVec 3),("y",TBitVec 3)]
          [NOutput "z" (TBitVec 3) (AVar "c"), NOutput "early" (TBitVec 3) (AVar "a")]
          [ NBind "a" (TBitVec 3) (NPrim BvAdd [AVar "x",AVar "y"])
          , NBind "b" (TBitVec 3) (NPrim BvMul [AVar "a",AVar "y"])
          , NBind "c" (TBitVec 3) (NPrim BvXor [AVar "b",AVar "x"]) ]
          (testCertificate "Pipeline.correct")
        rows = [[VBV 3 x,VBV 3 y] | x <- [0..7], y <- [0..7]]
    case pipelineCircuit 1 circuit of
      Left e -> expectationFailure (show e)
      Right scheduled -> do
        scheduledLatency scheduled `shouldBe` 2
        scheduledStageDepth scheduled `shouldBe` 1
        let actual = fmap (drop 2) (simulateNormal (scheduledModule scheduled) (rows <> replicate 2 [VBV 3 0,VBV 3 0]))
        actual `shouldBe` simulateNormal circuit rows
  it "keeps stateful kernels behind the exact-cycle boundary" $
    pipelineCircuit 1 counterNormal `shouldSatisfy` isLeft
  it "rejects invalid depth budgets" $
    pipelineCircuit 0 counterNormal `shouldSatisfy` isLeft
