-- | Machinery behind "Gin.Normalize".
module Gin.Normalize.Internal
  ( primResultTy
  ) where

import Gin.Core.Syntax (PrimOp (..), Ty (..), isScalar)

-- | Result type of a saturated combinational prim applied to arguments of
-- the given types, following the rules in "Gin.Core.Prim". 'Nothing' when
-- the application is ill-typed or unsaturated, when an argument or the
-- result is not scalar, or when the prim constructs signals.
primResultTy :: PrimOp -> [Ty] -> Maybe Ty
primResultTy op args
  | all isScalar args = result >>= \t -> if isScalar t then Just t else Nothing
  | otherwise = Nothing
  where
    result = case (op, args) of
      (BoolAnd, [TBool, TBool]) -> Just TBool
      (BoolOr, [TBool, TBool]) -> Just TBool
      (BoolXor, [TBool, TBool]) -> Just TBool
      (BoolEq, [TBool, TBool]) -> Just TBool
      (BoolNot, [TBool]) -> Just TBool
      (BvAdd, _) -> sameWidth
      (BvSub, _) -> sameWidth
      (BvMul, _) -> sameWidth
      (BvAnd, _) -> sameWidth
      (BvOr, _) -> sameWidth
      (BvXor, _) -> sameWidth
      (BvNeg, [TBitVec n]) -> Just (TBitVec n)
      (BvNot, [TBitVec n]) -> Just (TBitVec n)
      (BvShl _, [TBitVec n]) -> Just (TBitVec n)
      (BvLshr _, [TBitVec n]) -> Just (TBitVec n)
      (BvEq, _) -> TBool <$ sameWidth
      (BvUlt, _) -> TBool <$ sameWidth
      (BvUle, _) -> TBool <$ sameWidth
      (BvConcat, [TBitVec a, TBitVec b]) -> Just (TBitVec (a + b))
      (BvExtract hi lo, [TBitVec n]) | n > hi && hi >= lo -> Just (TBitVec (hi - lo + 1))
      (BvZext m, [TBitVec n]) | m >= n -> Just (TBitVec m)
      (BvOfBool, [TBool]) -> Just (TBitVec 1)
      _ -> Nothing
    sameWidth = case args of
      [TBitVec n, TBitVec m] | n == m -> Just (TBitVec n)
      _ -> Nothing
