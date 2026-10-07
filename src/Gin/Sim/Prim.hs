-- | Semantics of combinational primitives (@docs/semantics.md@).
--
-- Each equation below transcribes one row of the primitive table in
-- @docs/semantics.md@, with @n@ the operand width. Arithmetic is on
-- unbounded 'Integer's and reduced modulo @2^n@, so results never depend
-- on a machine word size.
module Gin.Sim.Prim
  ( evalPrim
  ) where

import Data.Bits (xor, (.&.), (.|.))
import Data.List (find)
import Data.Text (Text)
import Data.Text qualified as Text
import Gin.Core.Syntax
  ( PrimOp (..)
  , Value (..)
  , isCombinational
  , maxWidth
  , mkBV
  , primArity
  , primName
  , validValue
  , valueTy
  )
import Gin.Error (GinError, Stage (StSim), ginError)
import Gin.Core.Utils (showT)


-- | Apply a combinational prim to exactly 'primArity' argument values.
-- Errors ('StSim') on a signal prim, wrong arity or ill-typed arguments.
--
-- Arguments must also satisfy 'validValue'; every result does, and has the
-- result type the typing rules in "Gin.Core.Prim" give for the argument
-- types. Shift amounts of at least the operand width yield 0 without
-- computing @2^k@, so huge amounts are cheap.
evalPrim :: PrimOp -> [Value] -> Either GinError Value
evalPrim op args
  | not (isCombinational op) =
      failure "is a signal primitive; only combinational primitives apply to values"
  | toInteger (length args) /= toInteger (primArity op) =
      failure
        ("takes " <> showT (primArity op) <> " arguments, got " <> showT (length args))
  | Just bad <- find (not . validValue) args =
      failure ("argument " <> showT bad <> " is not a valid value")
  | otherwise = either failure Right (apply op args)
  where
    failure msg = Left (ginError StSim (primName op <> " " <> msg))

-- | The primitive table. 'Left' carries the reason an application is
-- ill-typed; arity, validity and signal prims are handled by 'evalPrim'.
apply :: PrimOp -> [Value] -> Either Text Value
apply op args = case (op, args) of
  (BoolAnd, [VBool a, VBool b]) -> bool (a && b)
  (BoolOr, [VBool a, VBool b]) -> bool (a || b)
  (BoolXor, [VBool a, VBool b]) -> bool (a /= b)
  (BoolNot, [VBool a]) -> bool (not a)
  (BoolEq, [VBool a, VBool b]) -> bool (a == b)
  (BvAdd, [VBV n a, VBV m b]) | n == m -> bv n (a + b)
  (BvSub, [VBV n a, VBV m b]) | n == m -> bv n (a - b)
  (BvMul, [VBV n a, VBV m b]) | n == m -> bv n (a * b)
  (BvNeg, [VBV n a]) -> bv n (2 ^ n - a)
  (BvAnd, [VBV n a, VBV m b]) | n == m -> bv n (a .&. b)
  (BvOr, [VBV n a, VBV m b]) | n == m -> bv n (a .|. b)
  (BvXor, [VBV n a, VBV m b]) | n == m -> bv n (a `xor` b)
  (BvNot, [VBV n a]) -> bv n (2 ^ n - 1 - a)
  (BvShl k, [VBV n a])
    | k >= n -> bv n 0
    | otherwise -> bv n (a * 2 ^ k)
  (BvLshr k, [VBV n a])
    | k >= n -> bv n 0
    | otherwise -> bv n (a `div` 2 ^ k)
  (BvEq, [VBV n a, VBV m b]) | n == m -> bool (a == b)
  (BvUlt, [VBV n a, VBV m b]) | n == m -> bool (a < b)
  (BvUle, [VBV n a, VBV m b]) | n == m -> bool (a <= b)
  (BvConcat, [VBV n a, VBV m b])
    | n + m <= maxWidth -> bv (n + m) (a * 2 ^ m + b)
    | otherwise ->
        Left ("result width " <> showT (n + m) <> " exceeds the maximum width " <> showT maxWidth)
  (BvExtract hi lo, [VBV n a])
    | lo <= hi && hi < n -> let w = hi - lo + 1 in bv w ((a `div` 2 ^ lo) `mod` 2 ^ w)
    | otherwise ->
        Left
          ( showT hi
              <> " "
              <> showT lo
              <> ": bounds do not satisfy width > hi >= lo for width "
              <> showT n
          )
  (BvZext m, [VBV n a])
    | m < n -> Left (showT m <> ": target width is narrower than the operand width " <> showT n)
    | m > maxWidth ->
        Left (showT m <> ": target width exceeds the maximum width " <> showT maxWidth)
    | otherwise -> Right (VBV m a)
  (BvOfBool, [VBool b]) -> Right (VBV 1 (if b then 1 else 0))
  _ -> Left ("is not defined on arguments of types " <> showT (fmap valueTy args))
  where
    bool = Right . VBool
    bv n = Right . mkBV n
