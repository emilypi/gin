-- | Normal form: the first-order, signal-erased, tuple-free program the
-- normalizer produces and the netlist builder consumes.
--
-- Invariants, checked by 'Gin.Normalize.checkNormal':
--
--   1. Every type in an 'NModule' is scalar ('isScalar').
--   2. Every bound name is unique and distinct from every input name.
--   3. 'NPrim' carries only combinational prims ('isCombinational'),
--      saturated ('primArity' atoms), well-typed.
--   4. Every variable referenced is an input or a bind.
--   5. The dependency graph over binds, ignoring the argument edge of
--      'NReg', is acyclic, and 'nmBinds' is in a topological order of it
--      (an 'NReg' argument may refer forward).
--   6. Each 'NReg' initial value has the bind's type.
--
-- Semantics: every name denotes one value per clock cycle. Inputs take
-- the driven value; 'NReg' denotes its initial value at cycle 0 and the
-- previous cycle's argument value afterwards; everything else is
-- combinational within the cycle (see @docs/semantics.md@).
module Gin.Core.Normal
  ( Atom (..)
  , NRhs (..)
  , NBind (..)
  , NOutput (..)
  , NModule (..)
  ) where

import Data.Text (Text)
import Gin.Core.Syntax (Certificate, Domain, Name, PrimOp, Ty, Value)

data Atom
  = AVar !Name
  | -- | Scalar literal only.
    ALit !Value
  deriving stock (Eq, Show)

data NRhs
  = NPrim !PrimOp ![Atom]
  | -- | @NMux cond then else@; @cond@ is 'TBool'.
    NMux !Atom !Atom !Atom
  | -- | @NReg init next@.
    NReg !Value !Atom
  | NAtom !Atom
  deriving stock (Eq, Show)

data NBind = NBind
  { nbName :: !Name
  , nbTy :: !Ty
  , nbRhs :: !NRhs
  }
  deriving stock (Eq, Show)

data NOutput = NOutput
  { noName :: !Text
  -- ^ Port name, from 'Gin.Core.Syntax.topOutputs'.
  , noTy :: !Ty
  , noAtom :: !Atom
  }
  deriving stock (Eq, Show)

data NModule = NModule
  { nmName :: !Text
  , nmDomain :: !Domain
  , nmInputs :: ![(Name, Ty)]
  -- ^ Names equal the input port names, in port order.
  , nmOutputs :: ![NOutput]
  -- ^ In output port order.
  , nmBinds :: ![NBind]
  , nmCertificate :: !Certificate
  }
  deriving stock (Eq, Show)
