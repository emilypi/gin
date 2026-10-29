{-# LANGUAGE DataKinds #-}

module Gin.Optimize.PolicySpec (spec) where

import Control.Lens (set, view)
import Control.Exception (evaluate)
import Data.ByteString.Lazy.Char8 qualified as B
import Data.Either (isLeft)
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict qualified as M
import Data.Text qualified as T
import Data.Validation (Validation (..))
import Gin.Core.Bounded
import Gin.Core.Prim (PrimOp (..))
import Gin.Core.Type (Ty (..))
import Gin.Error (GinError (..), renderError)
import Gin.Optimize.Circuit (CircuitCosts (..), CircuitOptions (..))
import Gin.Optimize.Policy
import Test.Hspec
import System.Timeout (timeout)
import Yolk qualified as Y

spec :: Spec
spec = describe "optimization policies" $ do
  it "reports independent numeric and relationship errors together" $ do
    let bytes =
          "{\"format\":\"gin-policy/1\",\"objectives\":[{\"name\":\"area\"}],\
          \\"prefer\":[\"unknown\"],\"timeoutSeconds\":0,\"upperBounds\":[1,2],\
          \\"search\":{\"iterations\":1001,\"nodes\":0}}"
    case decodePolicy bytes of
      Left err -> map (T.takeWhile (/= ':')) (errContext err) `shouldBe`
        ["timeoutSeconds", "search.iterations", "search.nodes", "prefer", "upperBounds"]
      Right _ -> expectationFailure "invalid fields were accepted"
  it "accumulates independent objective fields and separate objectives" $ do
    let bytes =
          "{\"format\":\"gin-policy/1\",\"objectives\":[\
          \{\"name\":\"bad name\",\"default\":\"bad\",\"operators\":{\"typo\":1}},\
          \{\"name\":\"\"}]}"
    case decodePolicy bytes of
      Left err -> map (T.takeWhile (/= ':')) (errContext err) `shouldBe`
        [ "objectives[0].name", "objectives[0].default"
        , "objectives[0].operators", "objectives[1].name"
        ]
      Right _ -> expectationFailure "invalid objective fields were accepted"
  it "reports structural prerequisites once without dependent cascades" $ do
    let bytes =
          "{\"format\":\"gin-policy/1\",\"objectives\":false,\
          \\"timeoutSeconds\":0,\"search\":{\"nodes\":0},\"upperBounds\":[1,2]}"
    case decodePolicy bytes of
      Left err -> map (T.takeWhile (/= ':')) (errContext err) `shouldBe`
        ["objectives", "timeoutSeconds", "search.nodes"]
      Right _ -> expectationFailure "invalid policy shape was accepted"
  it "accumulates record-edit failures with structured paths and an error optic" $
    case decodePolicy (searchPolicy "iterations" 8) of
      Left err -> expectationFailure (show err)
      Right original | [objective] <- policyObjectives original -> do
        let badObjective = set objectiveNameL "bad name"
              (set objectiveOperatorsL
                (M.singleton "typo" (boundedIntLiteral @1)) objective)
            updated = set policyPreferencesL ["x", "x"]
              (set policyObjectivesL [badObjective] original)
        case validatePolicyAll updated of
          Failure errors -> do
            map policyIssuePath (NE.toList (getPolicyErrors errors)) `shouldBe`
              ["objectives[0].name", "objectives[0].operators", "prefer"]
            view _PolicyErrors errors `shouldBe` getPolicyErrors errors
            validatePolicy updated `shouldSatisfy` isLeft
          Success () -> expectationFailure "invalid edits were accepted"
      Right _ -> expectationFailure "expected one objective in the fixture"
  it "bounds list traversal before accumulating checks on edited records" $
    case decodePolicy (searchPolicy "iterations" 8) of
      Left err -> expectationFailure (show err)
      Right original | [objective] <- policyObjectives original -> do
        let updated = set policyObjectivesL (repeat objective)
              (set policyPreferencesL (repeat "x")
                (set policyUpperBoundsL (Just (repeat (boundedIntLiteral @1))) original))
            paths = case validatePolicyAll updated of
              Failure errors -> map policyIssuePath (NE.toList (getPolicyErrors errors))
              Success () -> []
        result <- timeout 1000000
          (evaluate (paths == ["objectives", "prefer", "upperBounds"]))
        result `shouldBe` Just True
      Right _ -> expectationFailure "expected one objective in the fixture"
  it "retains terminal-safe rendering for accumulated parse errors" $ do
    let bytes =
          "{\"format\":\"gin-policy/1\",\"objectives\":[{\"name\":\"area\"}],\
          \\"timeoutSeconds\":\"bad\\nvalue\",\"search\":{\"nodes\":false}}"
    case decodePolicy bytes of
      Left err -> do
        length (T.lines (renderError err)) `shouldBe` 3
        map (T.takeWhile (/= ':')) (errContext err) `shouldBe`
          ["timeoutSeconds", "search.nodes"]
      Right _ -> expectationFailure "invalid field types were accepted"
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
