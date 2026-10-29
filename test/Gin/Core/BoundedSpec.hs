{-# LANGUAGE DataKinds #-}

module Gin.Core.BoundedSpec (spec) where

import Control.Lens (preview, review, set, view)
import Data.Aeson (eitherDecode, encode)
import Data.Either (isLeft)
import Gin.Core.Bounded
import Gin.Memory
import Test.Hspec
import Test.QuickCheck (property)

spec :: Spec
spec = describe "checked integral settings" $ do
  it "rejects both range violations and machine extremes" $
    mapM_
      (\n -> mkBoundedInt @1 @16 n `shouldSatisfy` isLeft)
      [minBound, -1, 0, 17, maxBound]
  it "preserves every accepted integer through construction and the prism" $
    property $ \n -> case mkBoundedInt @1 @16 n of
      Left _ -> n < 1 || n > 16
      Right checked ->
        view boundedIntValue checked == n
          && preview (boundedInt @1 @16) n == Just checked
          && review (boundedInt @1 @16) checked == n
  it "round trips boundary values and rejects invalid JSON settings" $ do
    mapM_
      ( \n -> case mkBoundedInt @1 @16 n of
          Left err -> expectationFailure err
          Right checked -> eitherDecode (encode checked) `shouldBe` Right checked
      )
      [1, 16]
    mapM_
      (\bytes -> (eitherDecode bytes :: Either String LaneCount) `shouldSatisfy` isLeft)
      ["0", "17", "1.5", "2147483648", "\"1\""]
  it "composes record optics with checked settings" $ do
    let lanes = boundedIntLiteral @16
        changed = set memoryLanesL lanes defaultMemoryConfig
    view (memoryLanesL . boundedIntValue) changed `shouldBe` 16
    memoryAddressWidth changed `shouldBe` memoryAddressWidth defaultMemoryConfig
    set memoryLanesL (view memoryLanesL changed) changed `shouldBe` changed
    preview (boundedInt @1 @16) 17 `shouldBe` Nothing
  it "checks all memory and traffic numeric inputs before execution" $ do
    mkMemoryConfig 1 64 `shouldSatisfy` either (const False) (const True)
    mapM_
      (`shouldSatisfy` isLeft)
      [ mkTrafficScenario "x" 0 1 1 1 1 0
      , mkTrafficScenario "x" 1 0 1 1 1 0
      , mkTrafficScenario "x" 1 1 1000001 1 1 0
      , mkTrafficScenario "x" 1 1 1 0 1 0
      , mkTrafficScenario "x" 1 1 1 1 0 0
      , mkTrafficScenario "x" 1 1 1 1 1 (-1)
      , mkTrafficScenario "x" 1 1 1 1 1 1000001
      ]
