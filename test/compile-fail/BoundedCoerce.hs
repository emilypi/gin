{-# LANGUAGE DataKinds #-}
module BoundedCoerce where

import Data.Coerce (coerce)
import Gin.Core.Bounded

widen :: BoundedInt 1 16 -> BoundedInt 1 64
widen = coerce
