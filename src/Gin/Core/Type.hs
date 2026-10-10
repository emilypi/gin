{-# LANGUAGE TemplateHaskell #-}

-- | Types of the gin core IR.
module Gin.Core.Type
  ( Domain (..)
  , Ty (..)
  , maxWidth
  , isScalar
  , tFuns
  , splitFun

    -- * Optics
  , domainNameL
  , domainPeriodPsL
  , _TBool
  , _TBitVec
  , _TProd
  , _TFun
  , _TSignal
  ) where

import Control.Lens (Plated (..), makePrisms)
import Data.Text (Text)
import Gin.Core.Optics (makeFieldLenses)
import Numeric.Natural (Natural)

-- | A synchronous clock domain. Every domain has one clock and one
-- synchronous, active-high reset.
data Domain = Domain
  { domainName :: !Text
  , domainPeriodPs :: !Natural
  }
  deriving stock (Eq, Ord, Show)

data Ty
  = TBool
  | -- | Unsigned bit vector of the given width, 1 <= width <= 'maxWidth'.
    TBitVec !Natural
  | -- | Product of two or more components (n-ary, never unary or nullary).
    TProd ![Ty]
  | TFun !Ty !Ty
  | -- | A stream of values in the named domain, one per clock cycle.
    TSignal !Text !Ty
  deriving stock (Eq, Ord, Show)

-- | Largest bit-vector width gin accepts. Bounds memory use when
-- decoding untrusted IR.
maxWidth :: Natural
maxWidth = 4096

-- | Scalars are the only types allowed on top-entity ports and in normal form.
isScalar :: Ty -> Bool
isScalar = \case
  TBool -> True
  TBitVec w -> w >= 1 && w <= maxWidth
  _ -> False

-- | @tFuns [a, b] r = a -> b -> r@.
tFuns :: [Ty] -> Ty -> Ty
tFuns args res = foldr TFun res args

-- | Inverse of 'tFuns': peel every argument off a function type.
splitFun :: Ty -> ([Ty], Ty)
splitFun = \case
  TFun a r -> let (as, res) = splitFun r in (a : as, res)
  t -> ([], t)

----------------------------------------------------------------------
-- Optics

makeFieldLenses ''Domain
makePrisms ''Ty

-- | The immediate component types: 'Control.Lens.universe' lists every
-- type inside one, 'Control.Lens.transform' rewrites them bottom-up.
instance Plated Ty where
  plate f = \case
    TProd ts -> TProd <$> traverse f ts
    TFun a r -> TFun <$> f a <*> f r
    TSignal d t -> TSignal d <$> f t
    t -> pure t
