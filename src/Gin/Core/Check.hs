-- | Type checker for the core IR.
module Gin.Core.Check
  ( checkProgram
  ) where

import Gin.Core.Syntax (Program)
import Gin.Error (GinError)

-- | Full static check: scoping, prim typing rules ('Gin.Core.Prim'),
-- top-entity shape ('Gin.Core.Syntax.TopEntity'), scalar ports, unique
-- def names, and no recursion between globals. Errors use 'StCheck'.
checkProgram :: Program -> Either GinError ()
checkProgram = error "not yet implemented: checkProgram"
