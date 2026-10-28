-- |
-- Module       : Gin.Optimize.CircuitSpec
-- Description  : Transition preservation and shared extraction at the Gin/Yolk boundary.
-- Copyright    : (c) 2026 Emily Pillmore
-- License      : BSD-3-Clause
--
-- Maintainer   : Emily Pillmore <emilypi@cohomolo.gy>
-- Stability    : experimental
-- Portability  : non-portable (GHC extensions)
module Gin.Optimize.CircuitSpec (spec) where

import Data.Foldable (for_)
import Data.List (sort)
import Data.Text (Text)
import Data.Text qualified as Text
import Gin.Core.Normal
import Gin.Core.Syntax
import Gin.Examples (counterNormal, detectorNormal, macNormal, sysDomain, testCertificate)
import Gin.Normalize (checkNormal)
import Gin.Optimize.Circuit
import Gin.Sim (simulateNormal)
import Numeric.Natural (Natural)
import Test.Hspec
import Yolk qualified as Y

spec :: Spec
spec = describe "typed circuit optimization" $ do
  for_ [MutableBackend, PersistentBackend] $ \backend -> describe (show backend) $ do
    let options = smallOptions backend 1
        costs = defaultCircuitCosts 1
    it "round-trips every primitive, including width-changing and oversized-shift operations" $ do
      result <- optimized (withoutRewrites options) costs everyPrimitive
      preserves everyPrimitive primitiveRows result
    it "keeps distinct register outputs whose next-state expressions agree" $ do
      result <- optimized options costs distinctStates
      preserves distinctStates [[VBV 3 0], [VBV 3 7], [VBV 3 2]] result
      for_ (circuitCandidates result) $ \candidate ->
        simulateNormal (optimizedModule candidate) [[VBV 3 0]]
          `shouldBe` Right [[VBV 3 1, VBV 3 6]]
    it "preserves feedback and nonzero initialization while simplifying next-state logic" $ do
      result <- optimized options costs feedback
      preserves feedback (fmap (\n -> [VBV 3 (n `mod` 8)]) [0 .. 39]) result
      for_ (circuitCandidates result) $ \candidate ->
        [() | NBind {nbRhs = NPrim BvMul _} <- nmBinds (optimizedModule candidate)] `shouldBe` []
    it "emits sharing across output and register-next roots only once" $ do
      result <- optimized (withoutRewrites options) costs sharedTransition
      preserves sharedTransition [[VBV 3 a, VBV 3 b] | a <- [0 .. 7], b <- [0 .. 7]] result
      for_ (circuitCandidates result) $ \candidate ->
        length [() | NBind {nbRhs = NPrim BvAdd _} <- nmBinds (optimizedModule candidate)] `shouldBe` 1
    it "removes newly dead feedback state and keeps extraction costs separate from final size" $ do
      result <- optimized options costs deadState
      preserves deadState (replicate 12 []) result
      for_ (circuitCandidates result) $ \candidate -> do
        nmBinds (optimizedModule candidate) `shouldBe` []
        extractionCost candidate `shouldSatisfy` all (> 0)
    it "preserves literal and duplicate roots without introducing copy binds" $ do
      result <- optimized options costs literalRoots
      preserves literalRoots [[]] result
      for_ (circuitCandidates result) $ \candidate -> nmBinds (optimizedModule candidate) `shouldBe` []
    it "instantiates widths observed only in literal operands of Boolean results" $ do
      let original = moduleWith "literal_compare" [] [NOutput "out" TBool (AVar "equal")]
            [NBind "equal" TBool (NPrim BvEq [ALit (VBV 7 19), ALit (VBV 7 19)])]
      result <- optimized options costs original
      preserves original [[]] result
      for_ (circuitCandidates result) $ \candidate -> nmBinds (optimizedModule candidate) `shouldBe` []
    for_ [1, 4096] $ \width ->
      it ("preserves the reflected width " <> show width <> " through identity elimination") $ do
        let original = widthIdentity width
        result <- optimized options costs original
        preserves original [[mkBV width 0], [mkBV width (-1)]] result
        for_ (circuitCandidates result) $ \candidate -> do
          fmap noTy (nmOutputs (optimizedModule candidate)) `shouldBe` [TBitVec width]
          nmBinds (optimizedModule candidate) `shouldBe` []
    it "produces incomparable shared-DAG candidates for mux distribution" $ do
      result <- optimized (smallOptions backend 2) tradeoffCosts muxTradeoff
      sort (fmap extractionCost (circuitCandidates result)) `shouldBe` [[6, 9], [9, 6]]
      circuitCoverage result `shouldBe` Y.Complete
      preserves muxTradeoff
        [[VBool c, VBV 2 a, VBV 2 b, VBV 2 d, VBV 2 e]
        | c <- [False, True], a <- [0 .. 3], b <- [0 .. 3], d <- [0 .. 3], e <- [0 .. 3]] result
    it "preserves fixed-width multiplication strength reduction, including wraparound" $ do
      result <- optimized (smallOptions backend 2) strengthCosts strengthReduction
      length (circuitCandidates result) `shouldSatisfy` (>= 2)
      preserves strengthReduction [[VBV 3 x] | x <- [0 .. 7]] result
    it "returns a valid baseline witness when saturation is stopped before rewriting" $ do
      result <- optimized (withoutRewrites options) costs feedback
      Y.stopReason (circuitRunResult result) `shouldBe` Y.IterationLimit
      preserves feedback [[VBV 3 3], [VBV 3 7]] result
    it "reports match exhaustion independently from extracted candidate correctness" $ do
      let bounded = options {circuitSaturationLimits = (circuitSaturationLimits options) {Y.matchLimit = 0}}
      result <- optimized bounded costs (widthIdentity 3)
      Y.stopReason (circuitRunResult result) `shouldBe` Y.MatchLimit
      preserves (widthIdentity 3) [[VBV 3 x] | x <- [0 .. 7]] result
    it "does not call a zero-budget incomplete extraction proven infeasible" $ do
      let bounded = (smallOptions backend 2)
            {circuitExtractionOptions = (Y.defaultParetoOptions 2) {Y.paretoExpansionLimit = Just 0}}
      result <- optimized bounded tradeoffCosts muxTradeoff
      circuitFeasibility result `shouldNotBe` Y.ProvenInfeasible
      for_ (circuitCandidates result) $ \candidate ->
        checkNormal (optimizedModule candidate) `shouldBe` Right ()
    it "rejects a cost vector with the wrong dimension" $ do
      let wrong = costs {circuitPrimitiveCost = \_ _ -> [1, 2]}
      optimizeCircuit options wrong (widthIdentity 3) `shouldSatisfy` isLeft
    it "rejects an invalid normal form before graph construction" $ do
      let invalid = feedback {nmBinds = fmap corrupt (nmBinds feedback)}
          corrupt b@NBind {nbRhs = NReg {}} = b {nbRhs = NReg (VBV 2 0) (AVar "next")}
          corrupt b = b
      optimizeCircuit options costs invalid `shouldSatisfy` isLeft
    for_ [("counter", counterNormal), ("detector", detectorNormal), ("mac", macNormal)] $ \(name, original) ->
      it ("preserves the " <> name <> " example on boundary-biased inputs") $ do
        result <- optimized options costs original
        let row n = [case ty of TBool -> VBool (odd n); TBitVec w -> mkBV w (n * 17 - 1); _ -> VBool False
                    | (_, ty) <- nmInputs original]
        preserves original (fmap row [0 .. 47]) result
  it "has backend-independent objective fronts and reconstructed circuit behavior" $ do
    mutable <- optimized (smallOptions MutableBackend 2) tradeoffCosts muxTradeoff
    persistent <- optimized (smallOptions PersistentBackend 2) tradeoffCosts muxTradeoff
    mutable `shouldBe` persistent

smallOptions :: CircuitBackend -> Int -> CircuitOptions
smallOptions backend dimensions = (defaultCircuitOptions dimensions)
  { circuitBackend = backend
  , circuitSaturationLimits = Y.Limits 4 2000 10000
  }

withoutRewrites :: CircuitOptions -> CircuitOptions
withoutRewrites options = options
  {circuitSaturationLimits = (circuitSaturationLimits options) {Y.iterationLimit = 0}}

optimized :: CircuitOptions -> CircuitCosts -> NModule -> IO CircuitResult
optimized options costs original = do
  checkNormal original `shouldBe` Right ()
  either (fail . show) pure (optimizeCircuit options costs original)

preserves :: NModule -> [[Value]] -> CircuitResult -> Expectation
preserves original rows result = do
  circuitCandidates result `shouldSatisfy` (not . null)
  let expected = simulateNormal original rows
  expected `shouldSatisfy` (not . isLeft)
  for_ (circuitCandidates result) $ \candidate -> do
    let actual = optimizedModule candidate
    checkNormal actual `shouldBe` Right ()
    nmInputs actual `shouldBe` nmInputs original
    fmap (\o -> (noName o, noTy o)) (nmOutputs actual)
      `shouldBe` fmap (\o -> (noName o, noTy o)) (nmOutputs original)
    nmCertificate actual `shouldBe` nmCertificate original
    nmDomain actual `shouldBe` nmDomain original
    simulateNormal actual rows `shouldBe` expected

isLeft :: Either a b -> Bool
isLeft (Left _) = True
isLeft _ = False

moduleWith :: Text -> [(Name, Ty)] -> [NOutput] -> [NBind] -> NModule
moduleWith name inputs outputs binds = NModule name sysDomain inputs outputs binds (testCertificate "Optimize.correct")

everyPrimitive :: NModule
everyPrimitive = moduleWith "all_primitives"
  [("x", TBitVec 3), ("y", TBitVec 3), ("b", TBool), ("c", TBool)] outputs binds
  where
    binds =
      [NBind (Name ("bool_" <> Text.pack (show index))) TBool (NPrim op [AVar "b", AVar "c"])
      | (index, op) <- zip [0 :: Int ..] [BoolAnd, BoolOr, BoolXor, BoolEq]]
      <> [NBind "bool_not" TBool (NPrim BoolNot [AVar "b"])]
      <> [NBind (Name ("binary_" <> Text.pack (show index))) (TBitVec 3) (NPrim op [AVar "x", AVar "y"])
         | (index, op) <- zip [0 :: Int ..] [BvAdd, BvSub, BvMul, BvAnd, BvOr, BvXor]]
      <> [NBind (Name ("unary_" <> Text.pack (show index))) (TBitVec 3) (NPrim op [AVar "x"])
         | (index, op) <- zip [0 :: Int ..] [BvNeg, BvNot, BvShl 0, BvShl 2, BvShl 8, BvLshr 0, BvLshr 2, BvLshr 8]]
      <> [NBind (Name ("compare_" <> Text.pack (show index))) TBool (NPrim op [AVar "x", AVar "y"])
         | (index, op) <- zip [0 :: Int ..] [BvEq, BvUlt, BvUle]]
      <> [NBind "concat_xy" (TBitVec 6) (NPrim BvConcat [AVar "x", AVar "y"])
         ,NBind "slice_x" (TBitVec 2) (NPrim (BvExtract 2 1) [AVar "x"])
         ,NBind "extended_x" (TBitVec 5) (NPrim (BvZext 5) [AVar "x"])
         ,NBind "bit_b" (TBitVec 1) (NPrim BvOfBool [AVar "b"])
         ,NBind "choose" (TBitVec 3) (NMux (AVar "b") (AVar "x") (AVar "y"))]
    outputs = [NOutput ("out_" <> unName (nbName b)) (nbTy b) (AVar (nbName b)) | b <- binds]

primitiveRows :: [[Value]]
primitiveRows = [[VBV 3 x, VBV 3 y, VBool b, VBool c]
               | x <- [0 .. 7], y <- [0 .. 7], b <- [False, True], c <- [False, True]]

distinctStates :: NModule
distinctStates = moduleWith "states" [("x", TBitVec 3)]
  [NOutput "first" (TBitVec 3) (AVar "r"), NOutput "second" (TBitVec 3) (AVar "s")]
  [NBind "r" (TBitVec 3) (NReg (VBV 3 1) (AVar "x"))
  ,NBind "s" (TBitVec 3) (NReg (VBV 3 6) (AVar "x"))]

feedback :: NModule
feedback = moduleWith "feedback" [("x", TBitVec 3)] [NOutput "out" (TBitVec 3) (AVar "r")]
  [NBind "r" (TBitVec 3) (NReg (VBV 3 5) (AVar "next"))
  ,NBind "product" (TBitVec 3) (NPrim BvMul [AVar "x", ALit (VBV 3 1)])
  ,NBind "next" (TBitVec 3) (NPrim BvAdd [AVar "r", AVar "product"])]

sharedTransition :: NModule
sharedTransition = moduleWith "sharing" [("x", TBitVec 3), ("y", TBitVec 3)]
  [NOutput "sum" (TBitVec 3) (AVar "sum_out"), NOutput "previous" (TBitVec 3) (AVar "r")]
  [NBind "r" (TBitVec 3) (NReg (VBV 3 4) (AVar "sum_next"))
  ,NBind "sum_out" (TBitVec 3) (NPrim BvAdd [AVar "x", AVar "y"])
  ,NBind "sum_next" (TBitVec 3) (NPrim BvAdd [AVar "x", AVar "y"])]

deadState :: NModule
deadState = moduleWith "dead_state" [] [NOutput "out" (TBitVec 3) (AVar "zero")]
  [NBind "r" (TBitVec 3) (NReg (VBV 3 5) (AVar "next"))
  ,NBind "next" (TBitVec 3) (NPrim BvAdd [AVar "r", ALit (VBV 3 1)])
  ,NBind "zero" (TBitVec 3) (NPrim BvMul [AVar "r", ALit (VBV 3 0)])]

literalRoots :: NModule
literalRoots = moduleWith "literal_roots" []
  [NOutput "first" (TBitVec 3) (ALit (VBV 3 5)), NOutput "second" (TBitVec 3) (ALit (VBV 3 5))] []

widthIdentity :: Natural -> NModule
widthIdentity width = moduleWith "identity" [("x", TBitVec width)] [NOutput "out" (TBitVec width) (AVar "sum")]
  [NBind "sum" (TBitVec width) (NPrim BvAdd [AVar "x", ALit (VBV width 0)])]

muxTradeoff :: NModule
muxTradeoff = moduleWith "mux_tradeoff" (("c", TBool) : [(name, TBitVec 2) | name <- ["a", "b", "d", "e"]])
  [NOutput "out" (TBitVec 2) (AVar "sum")]
  [NBind "left" (TBitVec 2) (NMux (AVar "c") (AVar "a") (AVar "b"))
  ,NBind "right" (TBitVec 2) (NMux (AVar "c") (AVar "d") (AVar "e"))
  ,NBind "sum" (TBitVec 2) (NPrim BvAdd [AVar "left", AVar "right"])]

tradeoffCosts :: CircuitCosts
tradeoffCosts = CircuitCosts
  {circuitPrimitiveCost = \_ _ -> [1, 4], circuitMuxCost = const [4, 1], circuitLiteralCost = const [0, 0]}

strengthReduction :: NModule
strengthReduction = moduleWith "strength" [("x", TBitVec 3)] [NOutput "out" (TBitVec 3) (AVar "product")]
  [NBind "product" (TBitVec 3) (NPrim BvMul [AVar "x", ALit (VBV 3 3)])]

strengthCosts :: CircuitCosts
strengthCosts = CircuitCosts
  {circuitPrimitiveCost = \_ op -> case op of BvMul -> [5, 1]; _ -> [1, 2]
  ,circuitMuxCost = const [1, 1]
  ,circuitLiteralCost = const [0, 0]}
