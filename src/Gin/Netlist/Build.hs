-- | Normal form to netlist (c-netlist).
--
-- Owner: p5.
module Gin.Netlist.Build
  ( buildNetlist
  ) where

import Gin.Core.Normal (NModule)
import Gin.Error (GinError)
import Gin.Netlist.Types (Module)

-- | Precondition: 'Gin.Normalize.checkNormal' succeeded. Errors use
-- 'StNetlist'.
buildNetlist :: NModule -> Either GinError Module
buildNetlist = error "TODO(p5): buildNetlist"
