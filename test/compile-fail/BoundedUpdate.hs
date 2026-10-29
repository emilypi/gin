{-# LANGUAGE DataKinds #-}
module BoundedUpdate where

import Gin.Core.Bounded

invalid :: BoundedInt 1 16 -> BoundedInt 1 16
invalid value = value {getBoundedInt = 0}
