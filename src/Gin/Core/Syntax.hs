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
  , mkTuple
  , lookupDef
  , globalRefs
  , module Gin.Core.Type
  , module Gin.Core.Value
  , module Gin.Core.Prim
  ) where

import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.List (find)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.String (IsString)
import Data.Text (Text)
import Gin.Core.Prim
import Gin.Core.Type
import Gin.Core.Value

-- | Local variables and global definitions share one name type. Globals
-- are fully qualified Lean names (@Counter.counter@).
newtype Name = Name {unName :: Text}
  deriving stock (Show)
  deriving newtype (Eq, Ord, IsString)

-- | A core expression over types @ty@ and names @name@; the exporter
-- emits @Expr Ty Name@. 'fmap' and 'traverse' act on the names.
data Expr ty name
  = -- | Lambda- or let-bound variable.
    EVar !name
  | -- | Reference to a 'Def' in 'progDefs'.
    EGlobal !name
  | ELit !Value
  | -- | Primitive together with its full instantiated type.
    EPrim !PrimOp !ty
  | -- | Curried n-ary application, n >= 1. Partial application is allowed.
    EApp !(Expr ty name) ![Expr ty name]
  | -- | Curried n-ary lambda, n >= 1.
    ELam ![(name, ty)] !(Expr ty name)
  | -- | @ELet binds body@. Non-recursive lets scope sequentially
    -- (each bind sees the earlier ones).
    ELet ![Bind ty name] !(Expr ty name)
  | -- | @ELetRec binds body@. Recursive lets scope every bind
    -- over all binds and the body. Separate from ELet because
    -- personally I want to know when I am in a recursive block.
    ELetRec ![Bind ty name] !(Expr ty name)
  | -- | Tuple of two or more components. Projections are keys. The keys
    -- of an n-tuple are 0 to n-1 ('mkTuple').
    ETuple !(IntMap (Expr ty name))
  | -- | @EProj i e@ is the component of the tuple @e@ at key @i@.
    EProj !Int !(Expr ty name)
  | -- | Combinational choice; each condition is a 'TBool' value, never a
    -- signal. This is the standard MultiWayIf implementation:
    -- @EIf [(c1, t1), .., (cn, tn)] e@ is the first @ti@ whose @ci@ holds,
    -- or @e@ when none does, n >= 1.
    EIf ![(Expr ty name, Expr ty name)] !(Expr ty name)
  deriving stock (Eq, Show, Functor, Foldable, Traversable)

data Bind ty name = Bind
  { bindName :: !name
  , bindTy :: !ty
  , bindExpr :: !(Expr ty name)
  }
  deriving stock (Eq, Show, Functor, Foldable, Traversable)

data Def ty name = Def
  { defName :: !name
  , defTy :: !ty
  , defBody :: !(Expr ty name)
  }
  deriving stock (Eq, Show, Functor, Foldable, Traversable)

-- | A top-entity port. 'portTy' is always scalar ('isScalar').
data Port ty = Port
  { portName :: !Text
  , portTy :: !ty
  }
  deriving stock (Eq, Show, Functor)

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
data TopEntity ty name = TopEntity
  { topName :: !Text
  , topDomain :: !Domain
  , topInputs :: ![Port ty]
  , topOutputs :: ![Port ty]
  -- ^ Non-empty.
  , topDef :: !name
  }
  deriving stock (Eq, Show, Functor, Foldable, Traversable)

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

data Program ty name = Program
  { progProducer :: !Producer
  , progTop :: !(TopEntity ty name)
  , progDefs :: ![Def ty name]
  , progCertificate :: !Certificate
  }
  deriving stock (Eq, Show, Functor, Foldable, Traversable)

-- | The tuple of the given components, keyed by position.
mkTuple :: [Expr ty name] -> Expr ty name
mkTuple = ETuple . IntMap.fromList . zip [0 ..]

lookupDef :: (Eq name) => name -> Program ty name -> Maybe (Def ty name)
lookupDef n = find ((== n) . defName) . progDefs

-- | Globals an expression refers to.
globalRefs :: (Ord name) => Expr ty name -> Set name
globalRefs = \case
  EVar _ -> Set.empty
  EGlobal n -> Set.singleton n
  ELit _ -> Set.empty
  EPrim _ _ -> Set.empty
  EApp f args -> foldMap globalRefs (f : args)
  ELam _ body -> globalRefs body
  ELet binds body -> bindRefs binds <> globalRefs body
  ELetRec binds body -> bindRefs binds <> globalRefs body
  ETuple es -> foldMap globalRefs es
  EProj _ e -> globalRefs e
  EIf arms e -> foldMap (\(c, t) -> globalRefs c <> globalRefs t) arms <> globalRefs e
  where
    bindRefs = foldMap (globalRefs . bindExpr)
