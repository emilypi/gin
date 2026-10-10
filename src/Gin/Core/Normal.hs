{-# LANGUAGE TemplateHaskell #-}

-- | Normal form (NF): the first-order, signal-erased, tuple-free program
-- the normalizer produces and the netlist builder consumes.
--
-- Invariants, checked by 'Gin.Normalize.checkNormal':
--
--   1. Every type in an 'NModule' is scalar ('isScalar').
--   2. Input names are pairwise distinct; every bound name is unique and
--      distinct from every input name.
--   3. Every right-hand side has its bind's type: 'NPrim' carries only
--      combinational prims ('isCombinational'), saturated ('primArity'
--      atoms), typed per "Gin.Core.Prim" on its atoms' types; 'NMux''s
--      condition is 'TBool' and both branches have the bind's type;
--      'NAtom''s atom and 'NReg''s argument have the bind's type. Every
--      'NOutput' atom has type 'noTy'.
--   4. Every variable referenced is an input or a bind.
--   5. The dependency graph over binds, ignoring the argument edge of
--      'NReg', is acyclic, and 'nmBinds' is in a topological order of it
--      (an 'NReg' argument may refer forward).
--   6. Each 'NReg' initial value has the bind's type.
--   7. Every bind is reachable from an output (no dead binds), and no
--      bind is an 'NAtom' copy (copies are propagated away).
--   8. At most 'Gin.Limits.maxNormalBinds' binds.
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

    -- * Optics
  , rhsAtoms
  , _AVar
  , _ALit
  , _NPrim
  , _NMux
  , _NReg
  , _NAtom
  , nbNameL
  , nbTyL
  , nbRhsL
  , noNameL
  , noTyL
  , noAtomL
  , nmNameL
  , nmDomainL
  , nmInputsL
  , nmOutputsL
  , nmBindsL
  , nmCertificateL
  ) where

import Control.Lens (Traversal', makePrisms)
import Data.Text (Text)
import Gin.Core.Optics (makeFieldLenses)
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

----------------------------------------------------------------------
-- Optics

makePrisms ''Atom
makePrisms ''NRhs
makeFieldLenses ''NBind
makeFieldLenses ''NOutput
makeFieldLenses ''NModule

-- | The atoms a right-hand side reads, in order.
rhsAtoms :: Traversal' NRhs Atom
rhsAtoms f = \case
  NPrim op as -> NPrim op <$> traverse f as
  NMux c t e -> NMux <$> f c <*> f t <*> f e
  NReg v a -> NReg v <$> f a
  NAtom a -> NAtom <$> f a
