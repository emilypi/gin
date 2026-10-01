-- | Semantics of combinational primitives (c-semantics).
--
-- Owner: p8.
module Gin.Sim.Prim
  ( evalPrim
  ) where

import Gin.Core.Syntax (PrimOp, Value)
import Gin.Error (GinError)

-- | Apply a combinational prim to exactly 'primArity' argument values.
-- Errors ('StSim') on a signal prim, wrong arity or ill-typed arguments.
evalPrim :: PrimOp -> [Value] -> Either GinError Value
evalPrim = error "TODO(p8): evalPrim"
