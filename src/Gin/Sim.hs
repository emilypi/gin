-- | Reference simulators (c-sim), used for translation validation.
--
-- Owner: p8.
module Gin.Sim
  ( simulateCore
  , simulateNormal
  ) where

import Gin.Core.Normal (NModule)
import Gin.Core.Syntax (Program, Value)
import Gin.Error (GinError)

-- | Simulate the core IR directly. One input row per cycle (values in
-- input port order); returns one output row per cycle (output port
-- order). Precondition: 'Gin.Core.Check.checkProgram' succeeded. Errors
-- use 'StSim' (e.g. arity or type mismatch in a row, or a recursive let
-- that is not productive).
simulateCore :: Program -> [[Value]] -> Either GinError [[Value]]
simulateCore = error "TODO(p8): simulateCore"

-- | Simulate a normal-form module, same row conventions.
simulateNormal :: NModule -> [[Value]] -> Either GinError [[Value]]
simulateNormal = error "TODO(p8): simulateNormal"
