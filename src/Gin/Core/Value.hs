-- | Runtime values shared by literals, register initialisers, simulation
-- and test vectors.
--
-- FROZEN CONTRACT (c-core-ast).
module Gin.Core.Value
  ( Value (..)
  , mkBV
  , valueTy
  , validValue
  ) where

import Gin.Core.Type (Ty (..), maxWidth)
import Numeric.Natural (Natural)

data Value
  = VBool !Bool
  | -- | @VBV width v@ with invariant @0 <= v < 2^width@ and
    -- @1 <= width <= maxWidth@.
    VBV !Natural !Integer
  | -- | Two or more components.
    VTuple ![Value]
  deriving stock (Eq, Ord, Show)

-- | Smart constructor: reduces the payload modulo @2^width@ (two's
-- complement wrap-around, C-4).
mkBV :: Natural -> Integer -> Value
mkBV w v = VBV w (v `mod` (2 ^ w))

valueTy :: Value -> Ty
valueTy = \case
  VBool _ -> TBool
  VBV w _ -> TBitVec w
  VTuple vs -> TProd (fmap valueTy vs)

-- | Does the value satisfy the representation invariants?
validValue :: Value -> Bool
validValue = \case
  VBool _ -> True
  VBV w v -> w >= 1 && w <= maxWidth && v >= 0 && v < 2 ^ w
  VTuple vs -> length vs >= 2 && all validValue vs
