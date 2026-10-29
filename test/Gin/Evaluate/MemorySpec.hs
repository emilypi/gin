{-# LANGUAGE DataKinds #-}

module Gin.Evaluate.MemorySpec (spec) where

import Gin.Core.Bounded
import Gin.Core.Normal
import Gin.Core.Type (Ty (..))
import Gin.Evaluate.Memory
import Gin.Examples (sysDomain, testCertificate)
import Gin.Memory
import Test.Hspec

spec :: Spec
spec = describe "modeled memory portfolios" $ do
  it "enumerates distinct generated designs and retains a completed frontier" $ do
    case evaluateMemoryPortfolio
      ["operators"]
      [kernel]
      [ MemoryConfig (boundedIntLiteral @1) (boundedIntLiteral @8)
      , MemoryConfig (boundedIntLiteral @2) (boundedIntLiteral @8)
      ]
      [scenario]
      [0 .. 7] of
      Left e -> expectationFailure (show e)
      Right p -> do
        length (memoryDesigns p) `shouldBe` 2
        memoryFrontier p `shouldSatisfy` (not . null)
  it "keeps cycle-limited runs out of the completed frontier" $ do
    case evaluateMemoryPortfolio
      ["operators"]
      [kernel]
      [MemoryConfig (boundedIntLiteral @1) (boundedIntLiteral @8)]
      [scenario {trafficCycleLimit = boundedIntLiteral @1}]
      [0 .. 7] of
      Left e -> expectationFailure (show e)
      Right p -> do
        length (memoryDesigns p) `shouldBe` 1
        memoryFrontier p `shouldBe` []

kernel :: MemoryKernel
kernel =
  MemoryKernel
    "identity"
    ( NModule
        "word_identity"
        sysDomain
        [("x", TBitVec 8)]
        [NOutput "y" (TBitVec 8) (AVar "x")]
        []
        (testCertificate "WordIdentity.correct")
    )
    [0]

scenario :: TrafficScenario
scenario =
  TrafficScenario
    "test"
    (boundedIntLiteral @1)
    (boundedIntLiteral @8)
    (boundedIntLiteral @4)
    (boundedIntLiteral @1)
    (boundedIntLiteral @1)
    (boundedIntLiteral @100000)
