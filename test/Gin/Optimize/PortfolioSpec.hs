module Gin.Optimize.PortfolioSpec (spec) where

import Data.Either (isLeft)
import Data.Text qualified as T
import Gin.Core.Normal
import Gin.Core.Syntax
import Gin.Examples (counterNormal, sysDomain, testCertificate)
import Gin.Optimize.Policy
import Gin.Optimize.Portfolio
import Test.Hspec

spec :: Spec
spec = describe "circuit portfolios" $ do
  it "scores registers separately and bounds combinational depth at state" $ do
    let m = measureCircuit counterNormal
    metricRegisters m `shouldBe` 1
    metricRegisterBits m `shouldBe` 8
    metricLogicDepth m `shouldSatisfy` (> 0)
  it "identifies selected candidates and rejects foreign digests" $ do
    case decodePolicy "{\"format\":\"gin-policy/1\",\"objectives\":[{\"name\":\"ops\"}]}" >>= \p -> buildPortfolio p identityCircuit of
      Left e -> expectationFailure (show e)
      Right portfolio -> do
        map candidateObjectives (portfolioCandidates portfolio) `shouldBe` [[0]]
        let chosen = selectCandidate Nothing portfolio
        case chosen of
          Left e -> expectationFailure (show e)
          Right c -> do
            T.length (candidateId c) `shouldBe` 64
            selectCandidate (Just (candidateId c)) portfolio `shouldBe` Right c
        selectCandidate (Just "forged") portfolio `shouldSatisfy` isLeft
  it "does not select an infeasible baseline when the archive is empty" $ do
    let expensive = identityCircuit {nmBinds = [NBind "b" TBool (NPrim BoolNot [AVar "x"])], nmOutputs = [NOutput "y" TBool (AVar "b")]}
    case decodePolicy "{\"format\":\"gin-policy/1\",\"objectives\":[{\"name\":\"ops\"}],\"upperBounds\":[0]}" >>= \p -> buildPortfolio p expensive of
      Left e -> expectationFailure (show e)
      Right portfolio -> selectCandidate Nothing portfolio `shouldSatisfy` isLeft
  it "revalidates updated policy records at the library boundary" $ do
    case decodePolicy "{\"format\":\"gin-policy/1\",\"objectives\":[{\"name\":\"ops\"}]}" of
      Left e -> expectationFailure (show e)
      Right p -> do
        buildPortfolio p {policyObjectives = []} identityCircuit `shouldSatisfy` isLeft
        buildPortfolio p {policyObjectives = policyObjectives p <> policyObjectives p} identityCircuit `shouldSatisfy` isLeft
        buildPortfolio p {policyPreferences = ["missing"]} identityCircuit `shouldSatisfy` isLeft

identityCircuit :: NModule
identityCircuit = NModule "identity" sysDomain [("x",TBool)]
  [NOutput "y" TBool (AVar "x")] [] (testCertificate "Identity.correct")
