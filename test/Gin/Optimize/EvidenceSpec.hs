-- |
-- Module       : Gin.Optimize.EvidenceSpec
-- Description  : Independent kernel checks of generated transition and stream proofs.
-- Copyright    : (c) 2026 Emily Pillmore
-- License      : BSD-3-Clause
--
-- Maintainer   : Emily Pillmore <emilypi@cohomolo.gy>
-- Stability    : experimental
-- Portability  : non-portable (GHC extensions)
module Gin.Optimize.EvidenceSpec (spec) where

import Control.Monad (unless)
import Data.Text qualified as Text
import Data.Text.IO qualified as Text
import Gin.Core.Normal
import Gin.Core.Syntax
import Gin.Examples (sysDomain, testCertificate)
import Gin.Optimize.Evidence
import Gin.Sim.Prim (evalPrim)
import Gin.TestUtil (itWithTools, runTool, withTempDir)
import System.Environment (getEnvironment)
import System.Exit (ExitCode (..))
import System.FilePath ((</>))
import System.Process (CreateProcess (..), proc, readCreateProcessWithExitCode)
import System.Timeout (timeout)
import Test.Hspec

spec :: Spec
spec = describe "optimizer equivalence evidence" $ do
  it "rejects changes to register initialization before generating a proof" $ do
    let altered =
          candidate
            { nmBinds =
                NBind "r" (TBitVec 3) (NReg (VBV 3 4) (AVar "next")) : drop 1 (nmBinds
                  candidate)
            }
    emitEquivalence original altered `shouldSatisfy` isLeft
  it "rejects mismatched public output names even when their types and values agree" $ do
    let altered = candidate {nmOutputs = [NOutput "renamed" (TBitVec 3) (AVar "r")]}
    emitEquivalence original altered `shouldSatisfy` isLeft
  itWithTools
    ["lean", "leanchecker"]
    "kernel-checks all cycles after projecting nonzero-initialized feedback state" $
    checks original candidate True
  itWithTools
    ["lean", "leanchecker"]
    "kernel-checks the mux distribution tradeoff for every input and cycle" $
    checks muxBefore muxAfter True
  itWithTools
    ["lean", "leanchecker"]
    "agrees with Gin primitive semantics on modular and width-changing boundary \
      \values" $ do
    values <- either (fail . show) pure (traverse (uncurry evalPrim) primitiveCases)
    let bindings =
          [ NBind
            (Name ("p" <> Text.pack (show index)))
            (valueTy value)
            (NPrim op (fmap ALit arguments))
          | (index, ((op, arguments), value)) <-
            zip [0 :: Int ..] (zip primitiveCases values)
          ]
        outputs =
          [ NOutput (unName (nbName binding)) (nbTy binding) (AVar (nbName binding))
          | binding <- bindings
          ]
        source =
          NModule
            "primitive_semantics"
            sysDomain
            []
            outputs
            bindings
            (testCertificate "Evidence.correct")
        target =
          source
            { nmBinds = []
            , nmOutputs = zipWith (\output value -> output {noAtom =
              ALit value}) outputs values
            }
    checks source target True
  itWithTools
    ["lean", "leanchecker"]
    "rejects a well-typed candidate with incorrect next-state behavior" $ do
    let incorrect = candidate {nmBinds =
          [NBind "r" (TBitVec 3) (NReg (VBV 3 5) (AVar "x"))]}
    checks original incorrect False

checks :: NModule -> NModule -> Bool -> Expectation
checks source target expected = withTempDir $ \dir -> do
  emitted <- either (fail . show) pure (emitEquivalence source target)
  -- Pin the toolchain independently of the user's global Lean default.
  toolchain <- Text.readFile ("lean" </> "lean-toolchain")
  Text.writeFile (dir </> "lean-toolchain") toolchain
  Text.writeFile (dir </> "GinOptimizationProof.lean") emitted
  (code, out, err) <-
    runTool dir "lean" ["-o", "GinOptimizationProof.olean", "GinOptimizationProof.lean"]
  if expected
    then do
      unless (code == ExitSuccess) (expectationFailure (Text.unpack (out <> err)))
      out `shouldSatisfy` Text.isInfixOf equivalenceTheoremName
      out `shouldSatisfy` (not . Text.isInfixOf "warning:")
      environment <- getEnvironment
      result <-
        timeout
          (60 * 1000000)
          ( readCreateProcessWithExitCode
              (proc "leanchecker" ["GinOptimizationProof"])
                { cwd = Just dir
                , env =
                  Just (("LEAN_PATH", dir) : filter ((/= "LEAN_PATH") . fst) environment)
                }
              ""
          )
      case result of
        Just (replay, stdoutText, stderrText) ->
          unless (replay == ExitSuccess) (expectationFailure (stdoutText <> stderrText))
        Nothing -> expectationFailure "kernel replay timed out"
    else code `shouldSatisfy` (/= ExitSuccess)

isLeft :: Either a b -> Bool
isLeft (Left _) = True
isLeft _ = False

original :: NModule
original =
  NModule
    "state_projection"
    sysDomain
    [("x", TBitVec 3)]
    [NOutput "out" (TBitVec 3) (AVar "out_value")]
    [ NBind "r" (TBitVec 3) (NReg (VBV 3 5) (AVar "next"))
    , NBind "discarded" (TBitVec 3) (NReg (VBV 3 3) (AVar "discarded_next"))
    , NBind "next" (TBitVec 3) (NPrim BvAdd [AVar "r", AVar "x"])
    , NBind "discarded_next" (TBitVec 3) (NPrim BvAdd [AVar "discarded", ALit (VBV 3 1)])
    , NBind "zero" (TBitVec 3) (NPrim BvMul [AVar "discarded", ALit (VBV 3 0)])
    , NBind "out_value" (TBitVec 3) (NPrim BvAdd [AVar "r", AVar "zero"])
    ]
    (testCertificate "Evidence.correct")

candidate :: NModule
candidate =
  original
    { nmOutputs = [NOutput "out" (TBitVec 3) (AVar "r")]
    , nmBinds =
        [ NBind "r" (TBitVec 3) (NReg (VBV 3 5) (AVar "next"))
        , NBind "next" (TBitVec 3) (NPrim BvAdd [AVar "r", AVar "x"])
        ]
    }

muxBefore :: NModule
muxBefore =
  NModule
    "mux_tradeoff"
    sysDomain
    (("c", TBool) : [(name, TBitVec 2) | name <- ["a", "b", "d", "e"]])
    [NOutput "out" (TBitVec 2) (AVar "result")]
    [ NBind "left" (TBitVec 2) (NMux (AVar "c") (AVar "a") (AVar "b"))
    , NBind "right" (TBitVec 2) (NMux (AVar "c") (AVar "d") (AVar "e"))
    , NBind "result" (TBitVec 2) (NPrim BvAdd [AVar "left", AVar "right"])
    ]
    (testCertificate "Evidence.correct")

muxAfter :: NModule
muxAfter =
  muxBefore
    { nmBinds =
        [ NBind "left" (TBitVec 2) (NPrim BvAdd [AVar "a", AVar "d"])
        , NBind "right" (TBitVec 2) (NPrim BvAdd [AVar "b", AVar "e"])
        , NBind "result" (TBitVec 2) (NMux (AVar "c") (AVar "left") (AVar "right"))
        ]
    }

primitiveCases :: [(PrimOp, [Value])]
primitiveCases =
  [(op, [VBool True, VBool False]) | op <- [BoolAnd, BoolOr, BoolXor, BoolEq]]
    <> [(BoolNot, [VBool True])]
    <> [ (op, [VBV 3 7, VBV 3 3])
       | op <- [BvAdd, BvSub, BvMul, BvAnd, BvOr, BvXor, BvEq, BvUlt, BvUle]
       ]
    <> [ (op, [VBV 3 7])
       | op <- [BvNeg, BvNot, BvShl 0, BvShl 2, BvShl 9, BvLshr 0, BvLshr 2, BvLshr 9]
       ]
    <> [ (BvConcat, [VBV 3 6, VBV 2 1])
       , (BvExtract 2 1, [VBV 3 6])
       , (BvZext 5, [VBV 3 7])
       , (BvOfBool, [VBool True])
       ]
