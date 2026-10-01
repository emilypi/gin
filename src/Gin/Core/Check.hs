-- | Type checker for the core IR.
module Gin.Core.Check
  ( checkProgram
  ) where

import Gin.Core.Syntax (Program)
import Gin.Error (GinError)

-- | Full static check. Errors use 'StCheck'. Enforces: unique def names;
-- every 'EGlobal' resolves; no recursion among globals (direct or
-- mutual); lexical scoping as documented on 'ELet'; binder names within
-- one 'ELam' binder list, and within one 'ELet' bind list, are pairwise
-- distinct; prim instantiated types match the rules in "Gin.Core.Prim",
-- including value/type agreement for register and mealy initial values;
-- application argument types match; an 'EIf' condition is 'TBool' and its
-- branches agree and are neither signals nor functions; projections are
-- in range; every 'Value' is valid ('validValue'); and the 'TopEntity'
-- rules, including scalar ports, unique port names, a legal top name, and
-- every signal in the top entity's domain.
checkProgram :: Program -> Either GinError ()
checkProgram = error "not yet implemented: checkProgram"
