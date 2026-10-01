-- | Abstract syntax of the gin core IR, the language the Lean exporter
-- emits (as JSON, c-ir-json) and the normalizer consumes.
--
-- FROZEN CONTRACT (c-core-ast).
module Gin.Core.Syntax
  ( Name (..)
  , Expr (..)
  , Bind (..)
  , Def (..)
  , Port (..)
  , TopEntity (..)
  , Certificate (..)
  , Producer (..)
  , Program (..)
  , lookupDef
  , module Gin.Core.Type
  , module Gin.Core.Value
  , module Gin.Core.Prim
  ) where

import Data.List (find)
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
-- order, and @o@ is the single output port type, or the 'TProd' of the
-- output port types when there are two or more. k may be 0.
data TopEntity = TopEntity
  { topName :: !Text
  , topDomain :: !Domain
  , topInputs :: ![Port]
  , topOutputs :: ![Port]
  -- ^ Non-empty.
  , topDef :: !Name
  }
  deriving stock (Eq, Show)

-- | Evidence, produced by the Lean exporter, that the implementation was
-- proven against a specification. gin cannot re-check the proof; it
-- enforces a policy on these fields (c-cert-policy) and carries the
-- statement into generated HDL headers for human review.
data Certificate = Certificate
  { certTheorem :: !Text
  -- ^ Fully qualified name of the refinement theorem.
  , certStatement :: !Text
  -- ^ Pretty-printed statement of the theorem.
  , certAxioms :: ![Text]
  -- ^ Axioms the theorem's proof depends on (Lean @collectAxioms@).
  , certImplAxioms :: ![Text]
  -- ^ Axioms the implementation definitions depend on.
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
