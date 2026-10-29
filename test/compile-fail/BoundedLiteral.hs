{-# LANGUAGE DataKinds #-}
module BoundedLiteral where

import Gin.Core.Bounded

invalid :: BoundedInt 1 16
invalid = boundedIntLiteral @17
