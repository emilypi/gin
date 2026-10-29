{-# LANGUAGE DataKinds #-}
module BoundedConstructor where

import Gin.Core.Bounded

invalid :: BoundedInt 1 16
invalid = BoundedInt 0
