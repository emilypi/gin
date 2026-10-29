{-# LANGUAGE DataKinds #-}
module BoundedSettings where

import Control.Lens (set, view)
import Gin.Core.Bounded
import Gin.Memory

config :: MemoryConfig
config = set memoryLanesL (boundedIntLiteral @16) defaultMemoryConfig

lanes :: Int
lanes = view (memoryLanesL . boundedIntValue) config
