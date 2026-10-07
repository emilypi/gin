-- | Abstract syntax of the gin core IR, the language the Lean exporter
-- emits (as JSON, see @docs/file-formats.md@) and the normalizer consumes.
module Gin.Core.Syntax
  ( Name (..)
  , Expr (..)
  , Bind (..)
  , Def (..)
  , Port (..)
  , TopEntity (..)
  , Certificate (..)
  , SpecDef (..)
  , Producer (..)
  , Program (..)
  , lookupDef
  , globalRefs
  , module Gin.Core.Type
  , module Gin.Core.Value
  , module Gin.Core.Prim
  ) where

import Data.List (find)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.String (IsString)
import Data.Text (Text)
import Gin.Core.Prim
import Gin.Core.Type
import Gin.Core.Value
import Numeric.Natural (Natural)

-- | Local variables and global definitions share one name type. Globals
-- are fully qualified Lean names (@Counter.counter@).
newtype Name = Name {unName :: Text}
  deriving stock (Show)
  deriving newtype (Eq, Ord, IsString)

data Expr
  = -- | Lambda- or let-bound variable.
    EVar !Name
  | -- | Reference to a 'Def' in 'progDefs'.
    EGlobal !Name
  | ELit !Value
  | -- | Primitive together with its full instantiated type.
    EPrim !PrimOp !Ty
  | -- | Curried n-ary application, n >= 1. Partial application is allowed.
    EApp !Expr ![Expr]
  | -- | Curried n-ary lambda, n >= 1.
    ELam ![(Name, Ty)] !Expr
  | -- | @ELet isRec binds body@. Non-recursive lets scope sequentially
    -- (each bind sees the earlier ones); recursive lets scope every bind
    -- over all binds and the body.
    ELet !Bool ![Bind] !Expr
  | -- | Tuple of two or more components.
    ETuple ![Expr]
  | -- | Zero-based projection out of a tuple.
    EProj !Natural !Expr
  | -- | Combinational choice; the condition is a 'TBool' value, never a signal.
    EIf !Expr !Expr !Expr
  deriving stock (Eq, Show)

data Bind = Bind
  { bindName :: !Name
  , bindTy :: !Ty
  , bindExpr :: !Expr
  }
  deriving stock (Eq, Show)

data Def = Def
  { defName :: !Name
  , defTy :: !Ty
  , defBody :: !Expr
  }
  deriving stock (Eq, Show)

-- | A top-entity port. 'portTy' is always scalar ('isScalar').
data Port = Port
  { portName :: !Text
  , portTy :: !Ty
  }
  deriving stock (Eq, Show)

-- | The circuit to synthesise. The type of 'topDef' must be
--
-- > Signal d i1 -> .. -> Signal d ik -> Signal d o
--
-- where @d = domainName topDomain@, the @ij@ are the input port types in
-- order, and @o@ is the single output port type or, for n >= 2 outputs,
-- the right-nested binary product
-- @TProd [o1, TProd [o2, .. TProd [o(n-1), on]]]@ (the shape of Lean's
-- @o1 × o2 × … × on@); output j is read by projecting along that spine.
-- k may be 0. 'topName' satisfies 'Gin.Netlist.Types.isLegalIdent', and
-- port names are pairwise distinct.
data TopEntity = TopEntity
  { topName :: !Text
  , topDomain :: !Domain
  , topInputs :: ![Port]
  , topOutputs :: ![Port]
  -- ^ Non-empty.
  , topDef :: !Name
  }
  deriving stock (Eq, Show)

-- | A definition the theorem statement depends on, rendered by the
-- exporter's fixed printer (fully qualified names, no user notation), so you
-- read what the kernel checked rather than a name. This is what answers
-- "does the specification say what I want?".
data SpecDef = SpecDef
  { specDefName :: !Text
  , specDefBody :: !Text
  }
  deriving stock (Eq, Show)

-- | The trace (@Certificate@ in the code, @"certificate"@ in the JSON):
-- evidence, produced by the Lean exporter, that the implementation was
-- proven against a specification. gin cannot re-check the proof: it
-- enforces a policy on these fields ('Gin.Certificate') and carries the
-- statement, the specification's definitions and their hash into
-- generated HDL headers for human review.
data Certificate = Certificate
  { certTheorem :: !Text
  -- ^ Fully qualified name of the refinement theorem.
  , certStatement :: !Text
  -- ^ Pretty-printed statement of the theorem.
  , certAxioms :: ![Text]
  -- ^ Axioms the theorem's proof depends on (Lean @collectAxioms@).
  , certImplAxioms :: ![Text]
  -- ^ Axioms the implementation definitions depend on.
  , certSpecDefs :: ![SpecDef]
  -- ^ Every definition the statement depends on transitively, other than
  -- the implementation and gin's DSL and Lean's core library.
  }
  deriving stock (Eq, Show)

data Producer = Producer
  { producerTool :: !Text
  , producerLeanVersion :: !Text
  }
  deriving stock (Eq, Show)

data Program = Program
  { progProducer :: !Producer
  , progTop :: !TopEntity
  , progDefs :: ![Def]
  , progCertificate :: !Certificate
  }
  deriving stock (Eq, Show)

lookupDef :: Name -> Program -> Maybe Def
lookupDef n = find ((== n) . defName) . progDefs

-- | Globals an expression refers to.
globalRefs :: Expr -> Set Name
globalRefs = \case
  EVar _ -> Set.empty
  EGlobal n -> Set.singleton n
  ELit _ -> Set.empty
  EPrim _ _ -> Set.empty
  EApp f args -> foldMap globalRefs (f : args)
  ELam _ body -> globalRefs body
  ELet _ binds body -> foldMap (globalRefs . bindExpr) binds <> globalRefs body
  ETuple es -> foldMap globalRefs es
  EProj _ e -> globalRefs e
  EIf c t e -> globalRefs c <> globalRefs t <> globalRefs e
