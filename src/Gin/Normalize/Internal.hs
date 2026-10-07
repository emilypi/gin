-- | Machinery behind "Gin.Normalize".
--
-- The core IR is evaluated into a wire-level semantic domain: a scalar is a
-- wire or a literal, a tuple is a tree of wires, and a function exists only
-- while it is being applied. Signals are erased, because every wire already
-- denotes one value per clock cycle (@docs/semantics.md@): @sig.pure x@ is
-- @x@ and @sig.lift k f s1 .. sk@ is @f s1 .. sk@. Evaluation emits one bind
-- per primitive operation, multiplexer and register into a graph; a
-- combinational right-hand side that was already emitted is reused rather
-- than duplicated. @sig.register@ becomes one register per scalar component
-- of its value, and @sig.mealy@ allocates its state registers before
-- evaluating the step function, then feeds the next state back into them.
-- A recursive @let@ allocates a wire per scalar component of each binding
-- and ties it to the binding's value with a copy.
--
-- A final pass removes binds no output depends on, then propagates every
-- copy, rejects combinational loops (cycles not broken by a register),
-- orders the remaining binds topologically and names them after the source
-- binders they were bound to where possible. Removing dead binds first
-- means a loop no output depends on, such as @let rec d = d in x@, is not
-- an error: it is never evaluated, by this normal form or by evaluation by
-- need ("Gin.Sim").
--
-- Two budgets keep hostile input from exhausting time or memory. Every bind
-- emitted while inlining counts against 'Gin.Limits.maxNormalBinds',
-- including binds that duplicate an earlier one, so exponential inlining is
-- stopped before the term is built. Every evaluation step counts against
-- 'maxEvalSteps', which bounds programs that do exponential work without
-- emitting binds at all. Names are replaced by integer ids before
-- evaluation, and wires are named after a bounded prefix of their source
-- binder, so the cost of a step does not grow with the length of names.
-- Every tuple the evaluator builds has an id. Naming visits each tuple once
-- and an @if@ muxes each pair of tuples once, so a value whose components
-- share tuples (@t1 = (t0, t0)@, @t2 = (t1, t1)@, ..) costs time linear in
-- the number of tuples, not in the size of the value written out as a tree.
-- I bound both budgets rather than trust a design you did not write to be
-- small.
module Gin.Normalize.Internal
  ( buildModule
  , primResultTy
  , maxEvalSteps
  ) where

import Control.Applicative ((<|>))
import Control.Monad (foldM, unless, when, zipWithM, zipWithM_)
import Control.Monad.State.Strict (State, StateT (..), gets, modify', runState, state)
import Data.Foldable (foldrM)
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet
import Data.List (genericDrop)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Traversable (mapAccumM)
import Gin.Core.Normal (Atom (..), NBind (..), NModule (..), NOutput (..), NRhs (..))
import Gin.Core.Syntax
  ( Bind (..)
  , Def (..)
  , Expr (..)
  , Name (..)
  , Port (..)
  , PrimOp (..)
  , Program (..)
  , TopEntity (..)
  , Ty (..)
  , Value (..)
  , isCombinational
  , isScalar
  , primArity
  , primName
  , validValue
  , valueTy
  )
import Gin.Error (GinError, Stage (..), ginError, withContext)
import Gin.Limits (maxNormalBinds)
import Numeric.Natural (Natural)

-- | Evaluation steps (expression visits plus function applications) one
-- normalization may take: 256 per permitted bind. Programs that stay
-- within 'maxNormalBinds' without pathological sharing use a small
-- fraction of it.
maxEvalSteps :: Int
maxEvalSteps = 256 * maxNormalBinds

-- | Nesting depth up to which error contexts (@in def@, @in bind@) are
-- recorded. Deeper evaluation still runs, as a tail call without a
-- context, so stack use stays bounded however deeply calls nest.
maxContextDepth :: Int
maxContextDepth = 256

----------------------------------------------------------------------
-- Prim typing

-- | Result type of a saturated combinational prim applied to arguments of
-- the given types, following the rules in "Gin.Core.Prim". 'Nothing' when
-- the application is ill-typed or unsaturated, when an argument or the
-- result is not scalar, or when the prim constructs signals.
primResultTy :: PrimOp -> [Ty] -> Maybe Ty
primResultTy op args
  | all isScalar args = result >>= \t -> if isScalar t then Just t else Nothing
  | otherwise = Nothing
  where
    result = case (op, args) of
      (BoolAnd, [TBool, TBool]) -> Just TBool
      (BoolOr, [TBool, TBool]) -> Just TBool
      (BoolXor, [TBool, TBool]) -> Just TBool
      (BoolEq, [TBool, TBool]) -> Just TBool
      (BoolNot, [TBool]) -> Just TBool
      (BvAdd, _) -> sameWidth
      (BvSub, _) -> sameWidth
      (BvMul, _) -> sameWidth
      (BvAnd, _) -> sameWidth
      (BvOr, _) -> sameWidth
      (BvXor, _) -> sameWidth
      (BvNeg, [TBitVec n]) -> Just (TBitVec n)
      (BvNot, [TBitVec n]) -> Just (TBitVec n)
      (BvShl _, [TBitVec n]) -> Just (TBitVec n)
      (BvLshr _, [TBitVec n]) -> Just (TBitVec n)
      (BvEq, _) -> TBool <$ sameWidth
      (BvUlt, _) -> TBool <$ sameWidth
      (BvUle, _) -> TBool <$ sameWidth
      (BvConcat, [TBitVec a, TBitVec b]) -> Just (TBitVec (a + b))
      (BvExtract hi lo, [TBitVec n]) | n > hi && hi >= lo -> Just (TBitVec (hi - lo + 1))
      (BvZext m, [TBitVec n]) | m >= n -> Just (TBitVec m)
      (BvOfBool, [TBool]) -> Just (TBitVec 1)
      _ -> Nothing
    sameWidth = case args of
      [TBitVec n, TBitVec m] | n == m -> Just (TBitVec n)
      _ -> Nothing

----------------------------------------------------------------------
-- Interned syntax

-- | A core expression with every name replaced by an integer id, so that
-- the cost of an evaluation step does not depend on how long the source
-- names are. Equal names get equal ids, which keeps shadowing as in the
-- source.
data IExpr
  = IVar !Int
  | IGlobal !Int
  | ILit !Value
  | IPrim !PrimOp
  | IApp IExpr [IExpr]
  | ILam [Int] IExpr
  | ILet !Bool [IBind] IExpr
  | ITuple [IExpr]
  | IProj !Natural IExpr
  | IIf IExpr IExpr IExpr

data IBind = IBind
  { ibName :: !Int
  , ibTy :: !Ty
  , ibExpr :: IExpr
  }

-- | The ids given to names so far, and the name of each id.
data Interner = Interner !(Map Name Int) !(IntMap Name)

intern :: Name -> State Interner Int
intern x = state $ \s@(Interner ids names) -> case Map.lookup x ids of
  Just i -> (i, s)
  Nothing ->
    let i = Map.size ids
     in (i, Interner (Map.insert x i ids) (IntMap.insert i x names))

internExpr :: Expr -> State Interner IExpr
internExpr = \case
  EVar x -> IVar <$> intern x
  EGlobal g -> IGlobal <$> intern g
  ELit v -> pure (ILit v)
  EPrim op _ -> pure (IPrim op)
  EApp f args -> IApp <$> internExpr f <*> traverse internExpr args
  ELam params body -> ILam <$> traverse (intern . fst) params <*> internExpr body
  ELet isRec binds body -> ILet isRec <$> traverse internBind binds <*> internExpr body
  ETuple es -> ITuple <$> traverse internExpr es
  EProj i e -> IProj i <$> internExpr e
  EIf c t e -> IIf <$> internExpr c <*> internExpr t <*> internExpr e
  where
    internBind (Bind x t e) = IBind <$> intern x <*> pure t <*> internExpr e

-- | The bodies of all definitions and the id of the top entity's
-- definition, with the name of every id. A later definition with the same
-- name replaces an earlier one.
internProgram :: Program -> (IntMap IExpr, Int, IntMap Name)
internProgram prog = (IntMap.fromList defs, top, names)
  where
    ((defs, top), Interner _ names) = runState build (Interner Map.empty IntMap.empty)
    build =
      (,)
        <$> traverse (\d -> (,) <$> intern (defName d) <*> internExpr (defBody d)) (progDefs prog)
        <*> intern (topDef (progTop prog))

----------------------------------------------------------------------
-- The semantic domain

-- | A wire (an input or a bind, by internal id) or a scalar literal.
data W
  = WVar !Int
  | WLit !Value
  deriving stock (Eq, Ord, Show)

-- | A right-hand side over wires. 'RCopy' only ties recursive bindings and
-- never survives the final pass.
data RRhs
  = RPrim !PrimOp ![W]
  | RMux !W !W !W
  | RReg !Value !W
  | RCopy !W
  deriving stock (Eq, Ord, Show)

data RBind = RBind
  { rbTy :: !Ty
  , rbRhs :: !RRhs
  , rbHint :: !Text
  -- ^ Fallback name when no source binder was bound to the wire.
  }
  deriving stock (Show)

-- | Values of the evaluator. Signals share the representation of the
-- values they carry.
data SVal
  = -- | A scalar wire or literal with its (scalar) type.
    SAtom !W !Ty
  | -- | A tuple with an id unique to this node ('tuple'). Values are never
    -- updated, so a tuple reached twice through sharing is one node, visited
    -- once by passes that only need to see each tuple once.
    STuple !Int ![SVal]
  | -- | A function, with the definition it was written in (for error context).
    SFun !(Maybe Int) (SVal -> M SVal)

data Env = Env
  { envVars :: !(IntMap SVal)
  , envDef :: !(Maybe Int)
  }

data St = St
  { stDefs :: !(IntMap IExpr)
  -- ^ Definition bodies by the id of their name.
  , stNames :: !(IntMap Name)
  -- ^ Source name of every interned id.
  , stInputs :: !(IntMap Text)
  -- ^ Input wire ids and their port names.
  , stNextId :: !Int
  , stNextTuple :: !Int
  -- ^ Id of the next tuple built.
  , stBinds :: !(IntMap RBind)
  , stEmitted :: !Int
  -- ^ Binds emitted so far, counting reuses of an existing bind.
  , stSteps :: !Int
  , stShared :: !(Map (Ty, RRhs) Int)
  -- ^ Combinational right-hand sides emitted so far, for reuse.
  , stAliases :: !(IntMap Text)
  -- ^ First source binder each wire was bound to.
  , stNamed :: !IntSet
  -- ^ Tuples whose components have been named after a source binder.
  , stGlobals :: !(IntMap SVal)
  -- ^ Values of the definitions evaluated so far.
  , stActive :: !IntSet
  -- ^ Definitions whose bodies are being evaluated.
  , stCurDef :: !(Maybe Int)
  -- ^ Definition whose code is being evaluated, for error contexts.
  , stDepth :: !Int
  -- ^ Number of error contexts currently pushed.
  }

type M = StateT St (Either GinError)

failN :: Text -> M a
failN msg = StateT (const (Left (ginError StNormalize msg)))

-- | Push an error context for the duration of a computation, up to
-- 'maxContextDepth' nested contexts.
inContext :: Text -> M a -> M a
inContext ctx m = do
  depth <- gets stDepth
  if depth >= maxContextDepth
    then m
    else do
      modify' (\s -> s {stDepth = depth + 1})
      r <- StateT (withContext ctx . runStateT m)
      modify' (\s -> s {stDepth = depth})
      pure r

showT :: (Show a) => a -> Text
showT = Text.pack . show

-- | The source name of an interned id. Lazy in the lookup, so an error
-- message or context that is never shown costs nothing.
sourceName :: Int -> M Text
sourceName i = gets (maybe ("#" <> showT i) unName . IntMap.lookup i . stNames)

-- | The prefix of a source name that names wires, at most 'maxAliasLength'
-- characters long.
aliasBase :: Int -> M Text
aliasBase i = Text.take maxAliasLength <$> sourceName i

-- | Charge evaluation steps against 'maxEvalSteps'.
spend :: Int -> M ()
spend k = do
  n <- gets stSteps
  when (n > maxEvalSteps - k) $
    failN ("normalization exceeds " <> showT maxEvalSteps <> " evaluation steps")
  modify' (\s -> s {stSteps = n + k})

tick :: M ()
tick = spend 1

freshId :: M Int
freshId = do
  i <- gets stNextId
  modify' (\s -> s {stNextId = i + 1})
  pure i

-- | A tuple node with a fresh id.
tuple :: [SVal] -> M SVal
tuple vs = do
  t <- gets stNextTuple
  modify' (\s -> s {stNextTuple = t + 1})
  pure (STuple t vs)

countBind :: M ()
countBind = do
  n <- gets stEmitted
  when (n >= maxNormalBinds) $
    failN ("normal form exceeds " <> showT maxNormalBinds <> " binds while inlining")
  modify' (\s -> s {stEmitted = n + 1})

-- | Emit a bind for a wire id allocated earlier.
emitAt :: Int -> Text -> Ty -> RRhs -> M ()
emitAt i hint ty rhs = do
  countBind
  modify' (\s -> s {stBinds = IntMap.insert i (RBind ty rhs hint) (stBinds s)})

-- | Emit a combinational bind, reusing an earlier bind with the same
-- right-hand side.
emitShared :: Text -> Ty -> RRhs -> M W
emitShared hint ty rhs = do
  countBind
  existing <- gets (Map.lookup (ty, rhs) . stShared)
  case existing of
    Just i -> pure (WVar i)
    Nothing -> do
      i <- freshId
      modify' $ \s ->
        s
          { stBinds = IntMap.insert i (RBind ty rhs hint) (stBinds s)
          , stShared = Map.insert (ty, rhs) i (stShared s)
          }
      pure (WVar i)

-- | Remember that a source binder names this value; component @k@ of a
-- tuple-valued binder @x@ is named @x_k@. Only a prefix of a long binder
-- name is used ('aliasBase'), and components whose name would grow past
-- 'maxAliasLength' keep the name of the operation that produced them, so
-- long names and deeply nested tuples do not cost time and memory
-- proportional to the product of name length and bind count, or quadratic
-- in the nesting depth.
--
-- Each tuple is named once, by the first binder that reaches it with a
-- name shorter than 'maxAliasLength': a tuple shared by several binders, or
-- several times within one value, is not walked again. The cost of all
-- calls together is linear in the number of tuples built, however large
-- the values are when written out as trees.
alias :: Int -> SVal -> M ()
alias x v0 = do
  base <- aliasBase x
  go base v0
  where
    go name v = do
      tick
      case v of
        SAtom (WVar i) _ ->
          modify' (\s -> s {stAliases = IntMap.insertWith (\_ old -> old) i name (stAliases s)})
        STuple t vs
          | Text.compareLength name maxAliasLength == LT -> do
              named <- gets (IntSet.member t . stNamed)
              unless named $ do
                modify' (\s -> s {stNamed = IntSet.insert t (stNamed s)})
                zipWithM_ (\k -> go (name <> "_" <> showT k)) [0 :: Int ..] vs
        _ -> pure ()

-- | Longest prefix of a source binder name used to name wires, and length
-- beyond which tuple components are no longer named after their binder.
maxAliasLength :: Int
maxAliasLength = 64

bindVar :: Int -> SVal -> Env -> Env
bindVar x v env = env {envVars = IntMap.insert x v (envVars env)}

-- | The scalar components of a value, in order. Accumulates from the right,
-- so the cost is linear in the size of the value however its tuples nest.
leaves :: SVal -> M [(W, Ty)]
leaves v0 = go v0 []
  where
    go v acc = do
      tick
      case v of
        SAtom w t -> pure ((w, t) : acc)
        STuple _ vs -> foldrM go acc vs
        SFun _ _ -> failN "a function value cannot be lowered to wires"

----------------------------------------------------------------------
-- Evaluation

eval :: Env -> IExpr -> M SVal
eval env expr = do
  tick
  case expr of
    IVar x -> case IntMap.lookup x (envVars env) of
      Just v -> pure v
      Nothing -> sourceName x >>= \n -> failN ("unbound variable " <> n)
    IGlobal g -> global g
    ILit v -> literal v
    IPrim op -> pure (primFun op)
    IApp f args -> do
      fv <- eval env f
      avs <- traverse (eval env) args
      foldM apply fv avs
    ILam params body -> lambda env params body
    ILet False binds body -> foldM letBind env binds >>= (`eval` body)
    ILet True binds body -> recLet env binds body
    ITuple es -> traverse (eval env) es >>= tuple
    IProj i e -> eval env e >>= project i
    IIf c t e -> do
      cv <- eval env c
      case cv of
        SAtom (WLit (VBool b)) _ -> eval env (if b then t else e)
        SAtom w TBool -> do
          tv <- eval env t
          ev <- eval env e
          mux w tv ev
        _ -> failN "the condition of an if is not a Bool"

apply :: SVal -> SVal -> M SVal
apply f a = do
  tick
  case f of
    SFun d k -> withDef d (k a)
    _ -> failN "application of a value that is not a function"

-- | Run a function body, adding the definition it was written in to error
-- contexts when that differs from the definition being evaluated.
withDef :: Maybe Int -> M a -> M a
withDef d m = do
  cur <- gets stCurDef
  depth <- gets stDepth
  case d of
    Just g
      | d /= cur
      , depth < maxContextDepth -> do
          name <- sourceName g
          modify' (\s -> s {stCurDef = d})
          r <- inContext ("in def " <> name) m
          modify' (\s -> s {stCurDef = cur})
          pure r
    _ -> m

lambda :: Env -> [Int] -> IExpr -> M SVal
lambda env params body = case params of
  [] -> eval env body
  x : rest -> pure $ SFun (envDef env) $ \a -> do
    alias x a
    lambda (bindVar x a env) rest body

global :: Int -> M SVal
global g = do
  cached <- gets (IntMap.lookup g . stGlobals)
  case cached of
    Just v -> pure v
    Nothing -> do
      def <- gets (IntMap.lookup g . stDefs)
      active <- gets (IntSet.member g . stActive)
      name <- sourceName g
      case def of
        Nothing -> failN ("unknown global " <> name)
        Just _ | active -> failN ("recursive definition " <> name)
        Just body -> do
          modify' (\s -> s {stActive = IntSet.insert g (stActive s)})
          v <- withDef (Just g) (eval (Env IntMap.empty (Just g)) body)
          modify' $ \s ->
            s
              { stActive = IntSet.delete g (stActive s)
              , stGlobals = IntMap.insert g v (stGlobals s)
              }
          pure v

literal :: Value -> M SVal
literal v
  | validValue v = spend (size v) >> go v
  | otherwise = failN ("invalid literal " <> showT v)
  where
    go = \case
      VTuple vs -> traverse go vs >>= tuple
      scalar -> pure (SAtom (WLit scalar) (valueTy scalar))
    size = \case
      VTuple vs -> 1 + sum (fmap size vs)
      _ -> 1

letBind :: Env -> IBind -> M Env
letBind env (IBind x _ e) = do
  ctx <- bindContext x
  v <- inContext ctx (eval env e)
  alias x v
  pure (bindVar x v env)

bindContext :: Int -> M Text
bindContext x = ("in bind " <>) <$> sourceName x

recLet :: Env -> [IBind] -> IExpr -> M SVal
recLet env binds body = do
  holes <- traverse (\b -> bindContext (ibName b) >>= (`inContext` hole b)) binds
  let env' = foldr (uncurry bindVar) env (zip (fmap ibName binds) holes)
  zipWithM_ (tieBind env') binds holes
  eval env' body
  where
    hole b = sourceName (ibName b) >>= (`placeholder` ibTy b)
    tieBind env' b h = do
      ctx <- bindContext (ibName b)
      inContext ctx $ do
        v <- eval env' (ibExpr b)
        alias (ibName b) v
        name <- sourceName (ibName b)
        tie name h v

-- | Fresh wires for every scalar component of a recursively bound value,
-- named @x@ in error messages.
placeholder :: Text -> Ty -> M SVal
placeholder x = \case
  TSignal _ t -> placeholder x t
  TProd ts -> traverse (placeholder x) ts >>= tuple
  TFun _ _ -> failN ("a recursive let cannot bind the function " <> x)
  t
    | isScalar t -> (`SAtom` t) . WVar <$> freshId
    | otherwise -> failN ("recursive binding " <> x <> " has a non-scalar type " <> showT t)

-- | Tie the wires of a recursive binding @x@ to its value with copies.
tie :: Text -> SVal -> SVal -> M ()
tie x hole v = case (hole, v) of
  (SAtom (WVar i) t, SAtom w t') | t == t' -> emitAt i (Text.take maxAliasLength x) t (RCopy w)
  (STuple _ hs, STuple _ vs) | length hs == length vs -> zipWithM_ (tie x) hs vs
  _ -> failN ("the value of recursive binding " <> x <> " does not match its type")

project :: Natural -> SVal -> M SVal
project i v = do
  spend (fromIntegral (min i (fromIntegral maxEvalSteps)))
  case v of
    STuple _ vs | x : _ <- genericDrop i vs -> pure x
    _ -> failN ("projection " <> showT i <> " out of a value without that component")

-- | One mux per scalar component where the branches differ. Each pair of
-- tuples is muxed once and the result reused wherever the pair recurs, so
-- branches whose components share tuples cost time linear in the number of
-- distinct pairs, not in the size of the branches written out as trees.
mux :: W -> SVal -> SVal -> M SVal
mux c a0 b0 = snd <$> go Map.empty a0 b0
  where
    go memo a b =
      tick >> case (a, b) of
        (SAtom x t, SAtom y t')
          | t /= t' -> failN "the branches of an if have different types"
          | x == y -> pure (memo, a)
          | otherwise -> (\w -> (memo, SAtom w t)) <$> emitShared "mux" t (RMux c x y)
        (STuple i xs, STuple j ys)
          | Just r <- Map.lookup (i, j) memo -> pure (memo, r)
          | length xs == length ys -> do
              (memo', rs) <- mapAccumM (\m (x, y) -> go m x y) memo (zip xs ys)
              r <- tuple rs
              pure (Map.insert (i, j) r memo', r)
        (SFun _ _, _) -> failN "an if whose branches carry a function is not supported"
        (_, SFun _ _) -> failN "an if whose branches carry a function is not supported"
        _ -> failN "the branches of an if have different shapes"

----------------------------------------------------------------------
-- Prims

-- | A prim as a curried function collecting 'primArity' arguments.
primFun :: PrimOp -> SVal
primFun op = collect (primArity op) []
  where
    collect n acc = SFun Nothing $ \a ->
      if n <= 1 then runPrim op (reverse (a : acc)) else pure (collect (n - 1) (a : acc))

runPrim :: PrimOp -> [SVal] -> M SVal
runPrim op args = case (op, args) of
  (SigPure, [x]) -> pure x
  (SigLift _, f : ss) -> foldM apply f ss
  (SigRegister v, [s]) -> register v s
  (SigMealy v, [f, i]) -> mealy v f i
  _
    | isCombinational op -> combinational op args
    | otherwise -> failN ("malformed application of " <> primName op)

combinational :: PrimOp -> [SVal] -> M SVal
combinational op args = do
  ws <- traverse scalarArg args
  case primResultTy op (fmap snd ws) of
    Nothing -> failN ("ill-typed application of " <> primName op)
    Just t -> (`SAtom` t) <$> emitShared (primHint op) t (RPrim op (fmap fst ws))
  where
    scalarArg = \case
      SAtom w t -> pure (w, t)
      _ -> failN (primName op <> " applied to a value that is not a scalar")

-- | @bv.add@ is hinted as @add@.
primHint :: PrimOp -> Text
primHint = Text.takeWhileEnd (/= '.') . primName

-- | One register per scalar component, initialised from the matching
-- component of the value.
register :: Value -> SVal -> M SVal
register v s = case (v, s) of
  (VTuple vs, STuple _ ss) | length vs == length ss -> zipWithM register vs ss >>= tuple
  (_, SAtom w t) | valueTy v == t -> do
    i <- freshId
    emitAt i "reg" t (RReg v w)
    pure (SAtom (WVar i) t)
  _ -> failN "the initial value of a register does not match its argument"

-- | State registers are allocated first, so the step function can read
-- them, and bound to the next state it returns afterwards.
mealy :: Value -> SVal -> SVal -> M SVal
mealy v f i = do
  (st, regs) <- stateWires v
  r <- apply f st >>= (`apply` i)
  case r of
    STuple _ [next, o] -> do
      ws <- leaves next
      unless (length ws == length regs) $
        failN "the next state of a mealy machine does not match its initial value"
      zipWithM_ feedBack regs ws
      pure o
    _ -> failN "the step function of a mealy machine does not return a (state, output) pair"
  where
    feedBack (rid, initial) (w, t)
      | valueTy initial == t = emitAt rid "state" t (RReg initial w)
      | otherwise = failN "the next state of a mealy machine does not match its initial value"

-- | A fresh wire for every scalar component of a mealy machine's initial
-- state, with the component it starts from, in order.
stateWires :: Value -> M (SVal, [(Int, Value)])
stateWires v0 = do
  (regs, st) <- go [] v0
  pure (st, reverse regs)
  where
    go acc = \case
      VTuple vs -> do
        (acc', cs) <- mapAccumM go acc vs
        (acc',) <$> tuple cs
      v -> do
        i <- freshId
        pure ((i, v) : acc, SAtom (WVar i) (valueTy v))

----------------------------------------------------------------------
-- Top level

-- | Evaluate the top entity and run the final pass. The result satisfies
-- the invariants of "Gin.Core.Normal" when the program is well typed;
-- "Gin.Normalize.normalize" checks them.
buildModule :: Program -> Either GinError NModule
buildModule prog = do
  let top = progTop prog
      (defs, topId, names) = internProgram prog
      inputs = IntMap.fromList (zip [0 ..] (fmap portName (topInputs top)))
      st0 =
        St
          { stDefs = defs
          , stNames = names
          , stInputs = inputs
          , stNextId = IntMap.size inputs
          , stNextTuple = 0
          , stBinds = IntMap.empty
          , stEmitted = 0
          , stSteps = 0
          , stShared = Map.empty
          , stAliases = IntMap.empty
          , stNamed = IntSet.empty
          , stGlobals = IntMap.empty
          , stActive = IntSet.empty
          , stCurDef = Nothing
          , stDepth = 0
          }
  (outs, st) <- runStateT (elaborate top topId) st0
  withContext ("in top entity " <> topName top) (assemble prog outs st)

-- | Apply the top entity's definition, whose name has the given id, to its
-- inputs and read its outputs.
elaborate :: TopEntity -> Int -> M [(Port, W)]
elaborate top topId = inContext ("in top entity " <> topName top) $ do
  when (null (topOutputs top)) $ failN "the top entity has no outputs"
  f <- global topId
  args <- zipWithM input [0 ..] (topInputs top)
  result <- foldM apply f args
  parts <- spine (length (topOutputs top)) result
  zipWithM output (topOutputs top) parts
  where
    input i port
      | isScalar (portTy port) = pure (SAtom (WVar i) (portTy port))
      | otherwise = failN ("input port " <> portName port <> " is not scalar")
    output port = \case
      SAtom w t | t == portTy port -> pure (port, w)
      _ -> failN ("output port " <> portName port <> " is not driven by a " <> showT (portTy port))

-- | Split a result along the right-nested product spine of @n@ outputs.
spine :: Int -> SVal -> M [SVal]
spine n v
  | n <= 1 = pure [v]
  | STuple _ [o, rest] <- v = (o :) <$> spine (n - 1) rest
  | otherwise = failN ("the top entity's result does not have " <> showT n <> " outputs")

operands :: RRhs -> [W]
operands = \case
  RPrim _ ws -> ws
  RMux c a b -> [c, a, b]
  RReg _ w -> [w]
  RCopy w -> [w]

mapRhs :: (W -> W) -> RRhs -> RRhs
mapRhs f = \case
  RPrim op ws -> RPrim op (fmap f ws)
  RMux c a b -> RMux (f c) (f a) (f b)
  RReg v w -> RReg v (f w)
  RCopy w -> RCopy (f w)

isCopy :: RRhs -> Bool
isCopy = \case
  RCopy _ -> True
  _ -> False

-- | Build the module from the emitted binds. Binds no output depends on,
-- through any operand, are dropped before copies are resolved and loops
-- are looked for, so only loops the outputs depend on are errors.
assemble :: Program -> [(Port, W)] -> St -> Either GinError NModule
assemble prog outs st = do
  let emitted = stBinds st
      raw = IntMap.restrictKeys emitted (reachable emitted (fmap snd outs))
      label i =
        fromMaybe ("#" <> showT i) $
          IntMap.lookup i (stInputs st)
            <|> IntMap.lookup i (stAliases st)
            <|> fmap rbHint (IntMap.lookup i raw)
  copies <- resolveCopies label raw
  let sub = \case
        WVar i | Just w <- IntMap.lookup i copies -> w
        w -> w
      substituted b = b {rbRhs = mapRhs sub (rbRhs b)}
      binds = IntMap.map substituted (IntMap.filter (not . isCopy . rbRhs) raw)
      outs' = [(p, sub w) | (p, w) <- outs]
  order <- topoOrder label binds
  -- Every bind left is still read by an output: propagating a copy only
  -- shortens the paths from the outputs.
  let ordered = [(i, b) | i <- order, Just b <- [IntMap.lookup i binds]]
      names = assignNames (stInputs st) (stAliases st) ordered
      nameOf i = maybe (Left (internal i)) (Right . Name) (IntMap.lookup i names)
      atom = \case
        WLit v -> Right (ALit v)
        WVar i -> AVar <$> nameOf i
      rhs = \case
        RPrim op ws -> NPrim op <$> traverse atom ws
        RMux c a b -> NMux <$> atom c <*> atom a <*> atom b
        RReg v w -> NReg v <$> atom w
        RCopy w -> NAtom <$> atom w
  nbinds <- traverse (\(i, b) -> NBind <$> nameOf i <*> pure (rbTy b) <*> rhs (rbRhs b)) ordered
  nouts <- traverse (\(p, w) -> NOutput (portName p) (portTy p) <$> atom w) outs'
  let top = progTop prog
  pure
    NModule
      { nmName = topName top
      , nmDomain = topDomain top
      , nmInputs = [(Name (portName p), portTy p) | p <- topInputs top]
      , nmOutputs = nouts
      , nmBinds = nbinds
      , nmCertificate = progCertificate prog
      }
  where
    internal i = ginError StNormalize ("internal error: wire #" <> showT i <> " has no bind")

-- | Map every copy bind to the non-copy wire or literal it denotes. A cycle
-- of copies is a combinational loop.
resolveCopies :: (Int -> Text) -> IntMap RBind -> Either GinError (IntMap W)
resolveCopies label binds = foldM start IntMap.empty (IntMap.keys targets)
  where
    targets = IntMap.mapMaybe (\b -> case rbRhs b of RCopy w -> Just w; _ -> Nothing) binds
    start done i
      | IntMap.member i done = Right done
      | otherwise = walk done [] IntSet.empty i
    walk done path onPath i
      | Just w <- IntMap.lookup i done = Right (settle w path done)
      | Just target <- IntMap.lookup i targets =
          if IntSet.member i onPath
            then Left (loopError label (i : reverse (takeWhile (/= i) path)))
            else case target of
              WVar j -> walk done (i : path) (IntSet.insert i onPath) j
              WLit _ -> Right (settle target (i : path) done)
      | otherwise = Right (settle (WVar i) path done)
    settle w path done = foldl' (\m k -> IntMap.insert k w m) done path

-- | Wires a right-hand side reads within the cycle: all operands except a
-- register's argument.
combinationalDeps :: RRhs -> IntSet
combinationalDeps = \case
  RReg _ _ -> IntSet.empty
  r -> IntSet.fromList [i | WVar i <- operands r]

-- | A topological order of the combinational dependency graph, preferring
-- the earliest-emitted ready bind; a cycle is a combinational loop.
topoOrder :: (Int -> Text) -> IntMap RBind -> Either GinError [Int]
topoOrder label binds = go ready0 indeg0 [] (0 :: Int)
  where
    deps = IntMap.map (IntSet.filter (`IntMap.member` binds) . combinationalDeps . rbRhs) binds
    users =
      IntMap.fromListWith
        IntSet.union
        [(d, IntSet.singleton i) | (i, ds) <- IntMap.toList deps, d <- IntSet.toList ds]
    indeg0 = IntMap.map IntSet.size deps
    ready0 = IntMap.keysSet (IntMap.filter (== 0) indeg0)
    go ready indeg acc done = case IntSet.minView ready of
      Just (i, rest) ->
        let readers = IntMap.findWithDefault IntSet.empty i users
            (indeg', ready') = IntSet.foldl' release (indeg, rest) readers
         in go ready' indeg' (i : acc) (done + 1)
      Nothing
        | done == IntMap.size binds -> Right (reverse acc)
        | otherwise ->
            Left (loopError label (findCycle deps (IntMap.keysSet (IntMap.filter (> 0) indeg))))
    release (indeg, ready) u =
      let k = IntMap.findWithDefault 0 u indeg - 1
       in (IntMap.insert u k indeg, if k == 0 then IntSet.insert u ready else ready)

-- | A cycle among binds that could not be ordered. Each of them reads at
-- least one other, so walking reads from any of them must revisit a bind.
findCycle :: IntMap IntSet -> IntSet -> [Int]
findCycle deps stuck = maybe [] (walk IntMap.empty [] 0 . fst) (IntSet.minView stuck)
  where
    walk seen path k i = case IntMap.lookup i seen of
      Just pos -> reverse (take (k - pos) path)
      Nothing -> case IntSet.minView (IntSet.intersection stuck (readsOf i)) of
        Nothing -> reverse (i : path)
        Just (j, _) -> walk (IntMap.insert i k seen) (i : path) (k + 1 :: Int) j
    readsOf i = IntMap.findWithDefault IntSet.empty i deps

loopError :: (Int -> Text) -> [Int] -> GinError
loopError label ids =
  ginError StNormalize $
    "combinational loop (a cycle not broken by a register) through "
      <> Text.intercalate ", " (fmap label (take 8 ids))
      <> (if length ids > 8 then ", ..." else "")

-- | Binds an output depends on, through any operand.
reachable :: IntMap RBind -> [W] -> IntSet
reachable binds = go IntSet.empty
  where
    go seen = \case
      [] -> seen
      WLit _ : rest -> go seen rest
      WVar i : rest
        | IntSet.member i seen -> go seen rest
        | Just b <- IntMap.lookup i binds -> go (IntSet.insert i seen) (operands (rbRhs b) <> rest)
        | otherwise -> go seen rest

-- | Names for inputs (their port names) and binds (the first source binder
-- bound to the wire, else the emission hint), made unique with numeric
-- suffixes in bind order.
assignNames :: IntMap Text -> IntMap Text -> [(Int, RBind)] -> IntMap Text
assignNames inputs aliases ordered = names
  where
    (names, _, _) = foldl' step (inputs, Set.fromList (IntMap.elems inputs), Map.empty) ordered
    step (!acc, !used, !counters) (i, b) =
      let base = nonEmpty (fromMaybe (rbHint b) (IntMap.lookup i aliases))
          (name, counters') = fresh used counters base
       in (IntMap.insert i name acc, Set.insert name used, counters')
    nonEmpty t = if Text.null t then "w" else t
    fresh used counters base
      | not (Set.member base used) = (base, counters)
      | otherwise = suffixed (Map.findWithDefault (1 :: Int) base counters)
      where
        suffixed k
          | Set.member candidate used = suffixed (k + 1)
          | otherwise = (candidate, Map.insert base (k + 1) counters)
          where
            candidate = base <> "_" <> showT k
