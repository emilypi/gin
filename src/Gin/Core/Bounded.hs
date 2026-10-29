{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}
-- Literal bounds are public preconditions even though conversion itself
-- needs only KnownNat; keep GHC from suggesting their removal.
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

-- |
-- Module       : Gin.Core.Bounded
-- Description  : Checked integral settings with bounds carried by their types.
-- Copyright    : (c) 2026 Emily Pillmore
-- License      : BSD-3-Clause
-- Maintainer   : Emily Pillmore <emilypi@cohomolo.gy>
-- Stability    : experimental
-- Portability  : non-portable (GHC extensions)
--
-- The representation and its record selector stay private. There is no Num
-- instance: arithmetic must pass through 'mkBoundedInt' again. Record lenses
-- can therefore replace a setting without admitting an unchecked integer.
module Gin.Core.Bounded
  ( BoundedInt
  , mkBoundedInt
  , boundedIntLiteral
  , boundedIntValue
  , boundedInt
  ) where

import Control.Lens (Getter, Prism', prism, to)
import Data.Aeson (FromJSON (..), ToJSON)
import Data.Proxy (Proxy (..))
import GHC.TypeNats (KnownNat, Nat, natVal, type (<=))

newtype BoundedInt (lower :: Nat) (upper :: Nat) = BoundedInt
  { getBoundedInt :: Int
  }
  deriving (Eq, Ord, Show, ToJSON) via Int

type role BoundedInt nominal nominal

mkBoundedInt :: forall lower upper. (KnownNat lower, KnownNat upper)
  => Int -> Either String (BoundedInt lower upper)
mkBoundedInt value
  | toInteger value >= lo && toInteger value <= hi = Right (BoundedInt value)
  | otherwise = Left ("expected an integer between " <> show lo <> " and " <> show hi)
  where
    lo = toInteger (natVal (Proxy @lower))
    hi = toInteger (natVal (Proxy @upper))

-- | A compile-time checked literal, representable even on a 32-bit host.
boundedIntLiteral :: forall n lower upper.
  (KnownNat n, lower <= n, n <= upper, n <= 2147483647)
  => BoundedInt lower upper
boundedIntLiteral = BoundedInt (fromIntegral (natVal (Proxy @n)))

-- | Read a checked value. Updates use the prism or smart constructor.
boundedIntValue :: Getter (BoundedInt lower upper) Int
boundedIntValue = to getBoundedInt

-- | Match exactly the integers in the inclusive interval; review forgets
-- the bound. This does not expose an unchecked setter for the representation.
boundedInt :: (KnownNat lower, KnownNat upper) => Prism' Int (BoundedInt lower upper)
boundedInt = prism getBoundedInt $ \value ->
  either (const (Left value)) Right (mkBoundedInt value)

instance (KnownNat lower, KnownNat upper) => FromJSON (BoundedInt lower upper) where
  parseJSON value = parseJSON value >>= either fail pure . mkBoundedInt
