-- | Type checker for the core IR.
--
-- Owner: p3.
module Gin.Core.Check
  ( checkProgram
  ) where

import Gin.Core.Syntax (Program)
import Gin.Error (GinError)

-- | Full static check: scoping, prim typing rules ('Gin.Core.Prim'),
-- top-entity shape ('Gin.Core.Syntax.TopEntity'), scalar ports, unique
-- def names, and no recursion between globals. Errors use 'StCheck'.
checkProgram :: Program -> Either GinError ()
checkProgram = error "TODO(p3): checkProgram"
