{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- |
-- Module       : Gin.Optimize.Circuit
-- Description  : Typed equality saturation of combinational transition forests.
-- Copyright    : (c) 2026 Emily Pillmore
-- License      : BSD-3-Clause
--
-- Maintainer   : Emily Pillmore <emilypi@cohomolo.gy>
-- Stability    : experimental
-- Portability  : non-portable (GHC extensions)
--
-- Each input and current register output is a distinct symbolic leaf. The
-- roots contain every output and every register-next expression together,
-- so extraction and emission preserve sharing across the whole transition
-- function. Registers are reconnected with their original initial values.
-- The built-in rules preserve fixed-width, unsigned modular semantics;
-- their registration is typed, but is not a formal equivalence certificate.
module Gin.Optimize.Circuit
  ( CircuitBackend (..)
  , CircuitOptions (..)
  , CircuitCosts (..)
  , CircuitCandidate (..)
  , CircuitResult (..)
  , defaultCircuitOptions
  , defaultCircuitCosts
  , circuitRuleSetVersion
  , optimizeCircuit
  ) where

import Control.Monad (foldM, unless, when)
import Control.Monad.Except (ExceptT, MonadError, liftEither, runExceptT, throwError)
import Control.Monad.State.Strict (StateT, gets, modify', runStateT)
import Control.Monad.Trans.Class (lift)
import Data.Functor.Const (Const)
import Data.HKD (FFoldable (..), FFunctor (..), FTraversable (..), ffoldMapDefault, ffmapDefault)
import Data.Kind (Type)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Proxy (Proxy (..))
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Word (Word64)
import GHC.TypeNats (KnownNat, Nat, SomeNat (..), natVal, someNatVal)
import Gin.Core.Normal
import Gin.Core.Syntax (Name (..), PrimOp (..), Ty (..), Value (..), maxWidth, mkBV, valueTy)
import Gin.Error (GinError, Stage (StNormalize), ginError, withContext)
import Gin.Limits (maxNormalBinds)
import Gin.Normalize (checkNormal)
import Gin.Normalize.Internal (primResultTy)
import Numeric.Natural (Natural)
import Type.Reflection (TypeRep, Typeable, eqTypeRep, typeRep, (:~~:) (HRefl))
import Yolk qualified as Y

data CircuitBackend = MutableBackend | PersistentBackend
  deriving stock (Eq, Ord, Show)

data CircuitOptions = CircuitOptions
  { circuitBackend :: !CircuitBackend
  , circuitSaturationLimits :: !Y.Limits
  , circuitExtractionOptions :: !Y.ParetoOptions
  }
  deriving stock (Eq, Show)

-- | Additive proxy weights, with one entry per objective. Register and input
-- leaves cost zero; fixed register resources are scored on the final module
-- by the caller. The extractor checks dimensions and its arithmetic bounds.
data CircuitCosts = CircuitCosts
  { circuitPrimitiveCost :: Ty -> PrimOp -> [Natural]
  , circuitMuxCost :: Ty -> [Natural]
  , circuitLiteralCost :: Value -> [Natural]
  }

data CircuitCandidate = CircuitCandidate
  { optimizedModule :: !NModule
  , extractionCost :: ![Natural]
  -- ^ Cost of the extracted forest before removal of newly dead state.
  -- Recompute final circuit metrics after reconstruction and cleanup.
  }
  deriving stock (Eq, Show)

data CircuitResult = CircuitResult
  { circuitCandidates :: ![CircuitCandidate]
  , circuitRunResult :: !Y.RunResult
  , circuitCoverage :: !Y.ParetoCoverage
  , circuitFeasibility :: !Y.ParetoFeasibility
  , circuitTermination :: !Y.ParetoTermination
  , circuitExpansions :: !Word64
  , circuitPendingBounds :: ![[Natural]]
  , circuitWitnessesComplete :: !Bool
  }
  deriving stock (Eq, Show)

defaultCircuitOptions :: Int -> CircuitOptions
defaultCircuitOptions dimensions = CircuitOptions
  { circuitBackend = MutableBackend
  , circuitSaturationLimits = Y.defaultLimits
  , circuitExtractionOptions = Y.defaultParetoOptions dimensions
  }

defaultCircuitCosts :: Int -> CircuitCosts
defaultCircuitCosts dimensions = CircuitCosts
  { circuitPrimitiveCost = \_ _ -> replicate dimensions 1
  , circuitMuxCost = const (replicate dimensions 1)
  , circuitLiteralCost = const (replicate dimensions 0)
  }

circuitRuleSetVersion :: Text
circuitRuleSetVersion = "gin-circuit-rules/1"

-- The constructor is private: the only inhabitants are reflected scalar
-- types checked against Gin's width bounds. Different widths are different
-- Haskell sorts, not an unchecked payload of one bit-vector sort.
data Bits (n :: Nat)

data Scalar s where
  Boolean :: Scalar Bool
  BitVector :: KnownNat n => Proxy n -> Scalar (Bits n)

scalarType :: Scalar s -> Ty
scalarType Boolean = TBool
scalarType (BitVector p) = TBitVec (natVal p)

scalarRep :: Scalar s -> TypeRep s
scalarRep Boolean = typeRep
scalarRep (BitVector (_ :: Proxy n)) = typeRep @(Bits n)

withScalar :: MonadError GinError m => Ty -> (forall s. Typeable s => Scalar s -> m a) -> m a
withScalar TBool action = action Boolean
withScalar (TBitVec width) action
  | width >= 1 && width <= maxWidth = case someNatVal width of
      SomeNat p -> action (BitVector p)
withScalar ty _ = throwError (problem ("unsupported scalar type: " <> shown ty))

data Some f where
  Some :: Typeable s => !(Scalar s) -> !(f s) -> Some f

newtype Forest (f :: Type -> Type) = Forest { forestRoots :: [Some f] }

instance FFunctor Forest where
  ffmap = ffmapDefault
instance FFoldable Forest where
  ffoldMap = ffoldMapDefault
instance FTraversable Forest where
  ftraverse f roots = Forest <$> traverse (\(Some s x) -> Some s <$> f x) (forestRoots roots)

data Leaf = InputLeaf !Name | RegisterLeaf !Name
  deriving stock (Eq, Ord, Show)

data Circuit s f where
  Wire :: !(Scalar s) -> !Leaf -> Circuit s f
  Literal :: !(Scalar s) -> !Value -> Circuit s f
  Operation :: !(Scalar s) -> !PrimOp -> !(Forest f) -> Circuit s f
  Select :: !(Scalar s) -> !(f Bool) -> !(f s) -> !(f s) -> Circuit s f

instance FFunctor (Circuit s) where
  ffmap = ffmapDefault
instance FFoldable (Circuit s) where
  ffoldMap = ffoldMapDefault
instance FTraversable (Circuit s) where
  ftraverse _ (Wire s leaf) = pure (Wire s leaf)
  ftraverse _ (Literal s value) = pure (Literal s value)
  ftraverse f (Operation s op children) = Operation s op <$> ftraverse f children
  ftraverse f (Select s c a b) = Select s <$> f c <*> f a <*> f b

instance Y.Language Circuit where
  operatorKey = \case
    Wire s leaf -> "wire:" <> show (scalarType s, leaf)
    Literal s value -> "literal:" <> show (scalarType s, value)
    Operation s op (Forest children) ->
      "primitive:" <> show (scalarType s, op, fmap someType children)
    Select s _ _ _ -> "mux:" <> show (scalarType s)

someType :: Some f -> Ty
someType (Some s _) = scalarType s

castScalar :: MonadError GinError m => Scalar s -> Some f -> m (f s)
castScalar wanted (Some actual value) = case eqTypeRep (scalarRep wanted) (scalarRep actual) of
  Just HRefl -> pure value
  Nothing -> throwError (problem ("sort mismatch: " <> shown (scalarType wanted, scalarType actual)))

checkedOperation :: MonadError GinError m => Scalar s -> PrimOp -> Forest f -> m (Circuit s f)
checkedOperation result op children@(Forest operands) = do
  unless (primResultTy op (fmap someType operands) == Just (scalarType result)) $
    throwError (problem ("ill-typed primitive in circuit adapter: " <> shown op))
  pure (Operation result op children)

type Import b r m = ExceptT GinError (Y.EGraphT b r Circuit m)

importForest :: Y.Backend b m => NModule -> Import b r m (Forest (Y.ClassId r))
importForest original = do
  inputs <- foldM (\env (name, ty) -> addLeaf env name ty (InputLeaf name)) Map.empty (nmInputs original)
  states <- foldM (\env b -> addLeaf env (nbName b) (nbTy b) (RegisterLeaf (nbName b))) inputs registers
  env <- foldM importBind states (nmBinds original)
  outputs <- traverse (importAtom env . noAtom) (nmOutputs original)
  next <- traverse (\(_, atom) -> importAtom env atom) (registerInputs original)
  pure (Forest (outputs <> next))
  where
    registers = fmap fst (registerInputs original)
    addLeaf env name ty leaf = withScalar ty $ \s -> do
      ident <- lift (Y.add (Wire s leaf))
      pure (Map.insert name (Some s ident) env)
    importBind env NBind {nbRhs = NReg {}} = pure env
    importBind env b = withScalar (nbTy b) $ \s -> do
      layer <- case nbRhs b of
        NPrim op atoms -> traverse (importAtom env) atoms >>= checkedOperation s op . Forest
        NMux c a d -> do
          condition <- importAtom env c >>= castScalar Boolean
          yes <- importAtom env a >>= castScalar s
          no <- importAtom env d >>= castScalar s
          pure (Select s condition yes no)
        _ -> throwError (problem "unexpected non-combinational binding in adapter")
      ident <- lift (Y.add layer)
      pure (Map.insert (nbName b) (Some s ident) env)

importAtom :: Y.Backend b m => Map Name (Some (Y.ClassId r)) -> Atom -> Import b r m (Some (Y.ClassId r))
importAtom env (AVar name) = maybe
  (throwError (problem ("undefined circuit wire: " <> unName name))) pure (Map.lookup name env)
importAtom _ (ALit value) = withScalar (valueTy value) $ \s ->
  Some s <$> lift (Y.add (Literal s value))

registerInputs :: NModule -> [(NBind, Atom)]
registerInputs original = [(b, next) | b@NBind {nbRhs = NReg _ next} <- nmBinds original]

newtype AtomAt s = AtomAt { atomAt :: Atom }

data Emission = Emission
  { emittedBinds :: ![NBind]
  , emittedNames :: !(Set Name)
  , emittedNext :: !Int
  , emittedCount :: !Int
  }

reconstruct :: NModule -> Forest (Y.Dag Circuit) -> Either GinError NModule
reconstruct original roots = do
  (Forest values, emission) <- runStateT (Y.foldDagManyM emit roots) initial
  let (outputs, next) = splitAt (length (nmOutputs original)) values
  unless (length outputs == length (nmOutputs original) && length next == length registers) $
    Left (problem "extracted root count differs from the transition interface")
  newOutputs <- sequence
    [ do
        unless (someType value == noTy out) (Left (problem "output sort changed during reconstruction"))
        pure out {noAtom = someAtom value}
    | (out, value) <- zip (nmOutputs original) outputs
    ]
  newRegisters <- sequence
    [ case nbRhs reg of
        NReg value _ -> do
          unless (someType nextValue == nbTy reg) (Left (problem "register sort changed during reconstruction"))
          pure reg {nbRhs = NReg value (someAtom nextValue)}
        _ -> Left (problem "register descriptor changed during reconstruction")
    | ((reg, _), nextValue) <- zip registers next
    ]
  let candidate = prune original
        { nmOutputs = newOutputs
        , nmBinds = newRegisters <> reverse (emittedBinds emission)
        }
  checkNormal candidate
  pure candidate
  where
    registers = registerInputs original
    initial = Emission []
      (Set.fromList (fmap fst (nmInputs original) <> fmap nbName (nmBinds original)
        <> fmap (Name . noName) (nmOutputs original))) 0 0
    someAtom (Some _ value) = atomAt value
    emit :: Circuit s AtomAt -> StateT Emission (Either GinError) (AtomAt s)
    emit = \case
      Wire _ (InputLeaf name) -> pure (AtomAt (AVar name))
      Wire _ (RegisterLeaf name) -> pure (AtomAt (AVar name))
      Literal _ value -> pure (AtomAt (ALit value))
      Operation s op (Forest children) -> allocate (scalarType s) (NPrim op (fmap someAtom children))
      Select s c a b -> allocate (scalarType s) (NMux (atomAt c) (atomAt a) (atomAt b))
    allocate :: Ty -> NRhs -> StateT Emission (Either GinError) (AtomAt s)
    allocate ty rhs = do
      count <- gets emittedCount
      when (count >= maxNormalBinds) (lift (Left (problem "reconstructed circuit exceeds the normal-form size limit")))
      name <- freshName
      modify' $ \st -> st
        { emittedBinds = NBind name ty rhs : emittedBinds st
        , emittedCount = count + 1
        }
      pure (AtomAt (AVar name))
    freshName = do
      index <- gets emittedNext
      used <- gets emittedNames
      let name = Name ("opt_" <> shown index)
      modify' (\st -> st {emittedNext = index + 1})
      if Set.member name used then freshName else do
        modify' (\st -> st {emittedNames = Set.insert name (emittedNames st)})
        pure name

-- Follow register-next edges as well as combinational edges. A simplification
-- can disconnect state, so retaining every original register would violate NF.
prune :: NModule -> NModule
prune original = original {nmBinds = filter (\b -> Set.member (nbName b) live) (nmBinds original)}
  where
    bindMap = Map.fromList [(nbName b, nbRhs b) | b <- nmBinds original]
    live = visit Set.empty (concatMap (atomNames . noAtom) (nmOutputs original))
    visit seen [] = seen
    visit seen (name : rest)
      | Set.member name seen = visit seen rest
      | otherwise = visit (Set.insert name seen) (maybe [] rhsNames (Map.lookup name bindMap) <> rest)
    rhsNames = \case
      NPrim _ atoms -> concatMap atomNames atoms
      NMux c a b -> concatMap atomNames [c, a, b]
      NReg _ next -> atomNames next
      NAtom value -> atomNames value
    atomNames (AVar name) = [name]
    atomNames ALit {} = []

-- | Optimize a checked NF using either backend. Exhaustion and model
-- optimality are reported independently from saturation. This routine checks
-- representation invariants; callers still validate the chosen circuit's
-- behavior and must not label it formally proved by this operation.
optimizeCircuit :: CircuitOptions -> CircuitCosts -> NModule -> Either GinError CircuitResult
optimizeCircuit options costs original = withContext "while optimizing the circuit" $ do
  checkNormal original
  rules <- circuitRules original
  let result = case circuitBackend options of
        MutableBackend -> Y.runMutable (searchCircuit options costs rules original)
        PersistentBackend -> Y.runPersistent (searchCircuit options costs rules original)
  either (Left . problem . shown) id result

searchCircuit :: Y.Backend b m => CircuitOptions -> CircuitCosts -> [Y.Rewrite Circuit] -> NModule
              -> Y.EGraphT b r Circuit m (Either GinError CircuitResult)
searchCircuit options costs rules original = runExceptT $ do
  roots <- importForest original
  runResult <- lift (Y.run (circuitSaturationLimits options) rules)
  search <- lift (Y.extractParetoMany (circuitExtractionOptions options) weight roots)
    >>= either (throwError . problem . shown) pure
  candidates <- traverse
    (\candidate -> do
      result <- liftEither (reconstruct original (Y.candidateValue candidate))
      pure (CircuitCandidate result (Y.candidateCost candidate)))
    (Y.paretoCandidates search)
  pure CircuitResult
    { circuitCandidates = candidates
    , circuitRunResult = runResult
    , circuitCoverage = Y.paretoCoverage search
    , circuitFeasibility = Y.paretoFeasibility search
    , circuitTermination = Y.paretoTermination search
    , circuitExpansions = Y.paretoExpansions search
    , circuitPendingBounds = Y.paretoPendingBounds search
    , circuitWitnessesComplete = Y.paretoWitnessesComplete search
    }
  where
    weight :: Circuit s (Const ()) -> [Natural]
    weight = \case
      Wire {} -> replicate (Y.paretoDimensions (circuitExtractionOptions options)) 0
      Literal _ value -> circuitLiteralCost costs value
      Operation s op _ -> circuitPrimitiveCost costs (scalarType s) op
      Select s _ _ _ -> circuitMuxCost costs (scalarType s)

-- A small checked rule language keeps runtime width instantiation at one
-- boundary. Both patterns are checked by Gin and Yolk before registration.
data RuleExpr
  = RVar !String !Ty
  | RLiteral !Value
  | RPrim !Ty !PrimOp ![RuleExpr]
  | RMux !Ty !RuleExpr !RuleExpr !RuleExpr

compilePattern :: RuleExpr -> Either GinError (Some (Y.Pattern Circuit))
compilePattern = \case
  RVar name ty -> withScalar ty $ \s -> pure (Some s (Y.var name))
  RLiteral value -> withScalar (valueTy value) $ \s -> pure (Some s (Y.node (Literal s value)))
  RPrim ty op operands -> withScalar ty $ \s -> do
    children <- Forest <$> traverse compilePattern operands
    layer <- checkedOperation s op children
    pure (Some s (Y.node layer))
  RMux ty c a b -> withScalar ty $ \s -> do
    condition <- compilePattern c >>= castScalar Boolean
    yes <- compilePattern a >>= castScalar s
    no <- compilePattern b >>= castScalar s
    pure (Some s (Y.node (Select s condition yes no)))

compileRule :: (String, RuleExpr, RuleExpr) -> Either GinError (Y.Rewrite Circuit)
compileRule (name, lhs, rhs) = do
  Some s left <- compilePattern lhs
  right <- compilePattern rhs >>= castScalar s
  either (Left . problem . shown) Right (Y.rewrite name left right)

circuitRules :: NModule -> Either GinError [Y.Rewrite Circuit]
circuitRules original = traverse compileRule (booleanRules <> concatMap rulesAt types)
  where
    types = Set.toAscList (Set.fromList
      (fmap snd (nmInputs original) <> fmap nbTy (nmBinds original) <> fmap noTy (nmOutputs original)
        <> concatMap literalTypes (concatMap bindAtoms (nmBinds original) <> fmap noAtom (nmOutputs original))))
    literalTypes (ALit value) = [valueTy value]
    literalTypes AVar {} = []
    bindAtoms bind = case nbRhs bind of
      NPrim _ atoms -> atoms
      NMux c a b -> [c, a, b]
      NReg _ next -> [next]
      NAtom atom -> [atom]
    rulesAt ty = muxRules ty <> case ty of
      TBitVec width -> vectorRules width <> oversizedShifts width
      _ -> []
    oversizedShifts width =
      [ ("oversized-shift/" <> show (width, op), RPrim (TBitVec width) op [RVar "x" (TBitVec width)], RLiteral (VBV width 0))
      | op <- Set.toAscList (Set.fromList [p | NBind {nbTy = TBitVec w, nbRhs = NPrim p _} <- nmBinds original, w == width])
      , case op of BvShl amount -> amount >= width; BvLshr amount -> amount >= width; _ -> False
      ]

booleanRules :: [(String, RuleExpr, RuleExpr)]
booleanRules =
  [ rule "and-true" (binary BoolAnd x true) x
  , rule "and-false" (binary BoolAnd x false) false
  , rule "or-false" (binary BoolOr x false) x
  , rule "or-true" (binary BoolOr x true) true
  , rule "xor-false" (binary BoolXor x false) x
  , rule "xor-self" (binary BoolXor x x) false
  , rule "and-self" (binary BoolAnd x x) x
  , rule "or-self" (binary BoolOr x x) x
  , rule "eq-self" (binary BoolEq x x) true
  , rule "not-not" (unary BoolNot (unary BoolNot x)) x
  ] <> [rule ("commute-" <> show op) (binary op x y) (binary op y x) | op <- [BoolAnd, BoolOr, BoolXor, BoolEq]]
  where
    x = RVar "x" TBool
    y = RVar "y" TBool
    true = RLiteral (VBool True)
    false = RLiteral (VBool False)
    unary op a = RPrim TBool op [a]
    binary op a b = RPrim TBool op [a, b]
    rule name = (,,) ("bool/" <> name)

muxRules :: Ty -> [(String, RuleExpr, RuleExpr)]
muxRules ty =
  [ named "true" (mux (RLiteral (VBool True)) a b) a
  , named "false" (mux (RLiteral (VBool False)) a b) b
  , named "same" (mux c a a) a
  ] <> concatMap distribute operations
  where
    a = RVar "a" ty
    b = RVar "b" ty
    d = RVar "d" ty
    e = RVar "e" ty
    c = RVar "c" TBool
    mux = RMux ty
    named name = (,,) ("mux/" <> show ty <> "/" <> name)
    operations = case ty of TBool -> [BoolAnd, BoolOr]; TBitVec _ -> [BvAdd, BvMul]; _ -> []
    distribute op =
      let binary x y = RPrim ty op [x, y]
          outside = binary (mux c a b) (mux c d e)
          inside = mux c (binary a d) (binary b e)
          common = mux c (binary a b) (binary a d)
          factored = binary a (mux c b d)
      in [named ("distribute/" <> show op) outside inside
         ,named ("factor/" <> show op) inside outside
         ,named ("common/" <> show op) common factored]

vectorRules :: Natural -> [(String, RuleExpr, RuleExpr)]
vectorRules width =
  [ named "add-zero" (binary BvAdd x zero) x
  , named "sub-zero" (binary BvSub x zero) x
  , named "sub-self" (binary BvSub x x) zero
  , named "mul-one" (binary BvMul x one) x
  , named "mul-zero" (binary BvMul x zero) zero
  , named "and-zero" (binary BvAnd x zero) zero
  , named "and-ones" (binary BvAnd x ones) x
  , named "and-self" (binary BvAnd x x) x
  , named "or-zero" (binary BvOr x zero) x
  , named "or-self" (binary BvOr x x) x
  , named "xor-zero" (binary BvXor x zero) x
  , named "xor-self" (binary BvXor x x) zero
  , named "neg-neg" (unary BvNeg (unary BvNeg x)) x
  , named "not-not" (unary BvNot (unary BvNot x)) x
  , named "shl-zero" (unary (BvShl 0) x) x
  , named "lshr-zero" (unary (BvLshr 0) x) x
  , named "zext-same" (unary (BvZext width) x) x
  , named "extract-all" (unary (BvExtract (width - 1) 0) x) x
  , named "eq-self" (comparison BvEq x x) (RLiteral (VBool True))
  , named "ult-self" (comparison BvUlt x x) (RLiteral (VBool False))
  , named "ule-self" (comparison BvUle x x) (RLiteral (VBool True))
  , named "mul-two" (binary BvMul x (literal 2)) (unary (BvShl 1) x)
  , named "mul-three" (binary BvMul x (literal 3)) (binary BvAdd x (unary (BvShl 1) x))
  , named "collect-three" (binary BvAdd x (unary (BvShl 1) x)) (binary BvMul x (literal 3))
  ] <> [named ("commute/" <> show op) (binary op x y) (binary op y x) | op <- [BvAdd, BvMul, BvAnd, BvOr, BvXor]]
  where
    ty = TBitVec width
    x = RVar "x" ty
    y = RVar "y" ty
    literal = RLiteral . mkBV width
    zero = literal 0
    one = literal 1
    ones = literal (-1)
    unary op a = RPrim ty op [a]
    binary op a b = RPrim ty op [a, b]
    comparison op a b = RPrim TBool op [a, b]
    named name = (,,) ("bv/" <> show width <> "/" <> name)

problem :: Text -> GinError
problem = ginError StNormalize

shown :: Show a => a -> Text
shown = Text.pack . show
