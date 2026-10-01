-- | Normalization: core IR to normal form ("Gin.Core.Normal").
module Gin.Normalize
  ( normalize
  , checkNormal
  ) where

import Gin.Core.Normal (NModule)
import Gin.Core.Syntax (Program)
import Gin.Error (GinError)

-- | Precondition: 'Gin.Core.Check.checkProgram' succeeded. Inlines
-- globals, beta-reduces, erases signals, lowers @sig.mealy@ to registers,
-- flattens tuples and A-normalizes. Errors use 'StNormalize' (e.g. a
-- lambda that cannot be eliminated, or a combinational loop).
normalize :: Program -> Either GinError NModule
normalize = error "not yet implemented: normalize"

-- | Validate every invariant listed in "Gin.Core.Normal".
checkNormal :: NModule -> Either GinError ()
checkNormal = error "not yet implemented: checkNormal"
