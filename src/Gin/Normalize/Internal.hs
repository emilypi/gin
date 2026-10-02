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
-- A final pass propagates every copy, rejects combinational loops (cycles
-- not broken by a register), removes binds no output depends on, orders the
-- rest topologically and names them after the source binders they were
-- bound to where possible.
--
-- Two budgets keep hostile input from exhausting time or memory. Every bind
-- emitted while inlining counts against 'Gin.Limits.maxNormalBinds',
-- including binds that duplicate an earlier one, so exponential inlining is
-- stopped before the term is built. Every evaluation step counts against
-- 'maxEvalSteps', which bounds programs that do exponential work without
-- emitting binds at all.
module Gin.Normalize.Internal
  ( buildModule
  , primResultTy
  , maxEvalSteps
  ) where

import Control.Applicative ((<|>))
import Control.Monad (foldM, unless, when, zipWithM, zipWithM_)
import Control.Monad.State.Strict (StateT (..), gets, modify')
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet
import Data.List (genericDrop)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as Text
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
  | STuple ![SVal]
  | -- | A function, with the definition it was written in (for error context).
    SFun !(Maybe Name) (SVal -> M SVal)

data Env = Env
  { envVars :: !(Map Name SVal)
  , envDef :: !(Maybe Name)
  }

data St = St
  { stDefs :: !(Map Name Def)
  , stInputs :: !(IntMap Text)
  -- ^ Input wire ids and their port names.
  , stNextId :: !Int
  , stBinds :: !(IntMap RBind)
  , stEmitted :: !Int
  -- ^ Binds emitted so far, counting reuses of an existing bind.
  , stSteps :: !Int
  , stShared :: !(Map (Ty, RRhs) Int)
  -- ^ Combinational right-hand sides emitted so far, for reuse.
  , stAliases :: !(IntMap Text)
  -- ^ First source binder each wire was bound to.
  , stGlobals :: !(Map Name SVal)
  -- ^ Values of the definitions evaluated so far.
  , stActive :: !(Set Name)
  -- ^ Definitions whose bodies are being evaluated.
  , stCurDef :: !(Maybe Name)
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
-- tuple-valued binder @x@ is named @x_k@. Components whose name would grow
-- past 'maxAliasLength' keep the name of the operation that produced them,
-- so deeply nested tuples do not cost time and memory quadratic in their
-- depth.
alias :: Name -> SVal -> M ()
alias x = go (unName x)
  where
    go name v = do
      tick
      case v of
        SAtom (WVar i) _ ->
          modify' (\s -> s {stAliases = IntMap.insertWith (\_ old -> old) i name (stAliases s)})
        STuple vs
          | Text.compareLength name maxAliasLength == LT ->
              zipWithM_ (\k -> go (name <> "_" <> showT k)) [0 :: Int ..] vs
        _ -> pure ()

-- | Length beyond which tuple components are no longer named after their
-- source binder.
maxAliasLength :: Int
maxAliasLength = 64

bindVar :: Name -> SVal -> Env -> Env
bindVar x v env = env {envVars = Map.insert x v (envVars env)}

-- | The scalar components of a value, in order.
leaves :: SVal -> M [(W, Ty)]
leaves v = do
  tick
  case v of
    SAtom w t -> pure [(w, t)]
    STuple vs -> concat <$> traverse leaves vs
    SFun _ _ -> failN "a function value cannot be lowered to wires"

----------------------------------------------------------------------
-- Evaluation

eval :: Env -> Expr -> M SVal
eval env expr = do
  tick
  case expr of
    EVar x -> maybe (failN ("unbound variable " <> unName x)) pure (Map.lookup x (envVars env))
    EGlobal g -> global g
    ELit v -> literal v
    EPrim op _ -> pure (primFun op)
    EApp f args -> do
      fv <- eval env f
      avs <- traverse (eval env) args
      foldM apply fv avs
    ELam params body -> lambda env params body
    ELet False binds body -> foldM letBind env binds >>= (`eval` body)
    ELet True binds body -> recLet env binds body
    ETuple es -> STuple <$> traverse (eval env) es
    EProj i e -> eval env e >>= project i
    EIf c t e -> do
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
withDef :: Maybe Name -> M a -> M a
withDef d m = do
  cur <- gets stCurDef
  depth <- gets stDepth
  case d of
    Just name
      | d /= cur
      , depth < maxContextDepth -> do
          modify' (\s -> s {stCurDef = d})
          r <- inContext ("in def " <> unName name) m
          modify' (\s -> s {stCurDef = cur})
          pure r
    _ -> m

lambda :: Env -> [(Name, Ty)] -> Expr -> M SVal
lambda env params body = case params of
  [] -> eval env body
  (x, _) : rest -> pure $ SFun (envDef env) $ \a -> do
    alias x a
    lambda (bindVar x a env) rest body

global :: Name -> M SVal
global g = do
  cached <- gets (Map.lookup g . stGlobals)
  case cached of
    Just v -> pure v
    Nothing -> do
      def <- gets (Map.lookup g . stDefs)
      active <- gets (Set.member g . stActive)
      case def of
        Nothing -> failN ("unknown global " <> unName g)
        Just _ | active -> failN ("recursive definition " <> unName g)
        Just d -> do
          modify' (\s -> s {stActive = Set.insert g (stActive s)})
          v <- withDef (Just g) (eval (Env Map.empty (Just g)) (defBody d))
          modify' $ \s ->
            s {stActive = Set.delete g (stActive s), stGlobals = Map.insert g v (stGlobals s)}
          pure v

literal :: Value -> M SVal
literal v
  | validValue v = spend (size v) >> pure (go v)
  | otherwise = failN ("invalid literal " <> showT v)
  where
    go = \case
      VTuple vs -> STuple (fmap go vs)
      scalar -> SAtom (WLit scalar) (valueTy scalar)
    size = \case
      VTuple vs -> 1 + sum (fmap size vs)
      _ -> 1

letBind :: Env -> Bind -> M Env
letBind env (Bind x _ e) = do
  v <- inContext ("in bind " <> unName x) (eval env e)
  alias x v
  pure (bindVar x v env)

recLet :: Env -> [Bind] -> Expr -> M SVal
recLet env binds body = do
  holes <- traverse (\b -> inContext (ctx b) (placeholder (bindName b) (bindTy b))) binds
  let env' = foldr (uncurry bindVar) env (zip (fmap bindName binds) holes)
  zipWithM_ (tieBind env') binds holes
  eval env' body
  where
    ctx b = "in bind " <> unName (bindName b)
    tieBind env' b hole = inContext (ctx b) $ do
      v <- eval env' (bindExpr b)
      alias (bindName b) v
      tie (bindName b) hole v

-- | Fresh wires for every scalar component of a recursively bound value.
placeholder :: Name -> Ty -> M SVal
placeholder x = \case
  TSignal _ t -> placeholder x t
  TProd ts -> STuple <$> traverse (placeholder x) ts
  TFun _ _ -> failN ("a recursive let cannot bind the function " <> unName x)
  t
    | isScalar t -> (`SAtom` t) . WVar <$> freshId
    | otherwise -> failN ("recursive binding " <> unName x <> " has a non-scalar type " <> showT t)

tie :: Name -> SVal -> SVal -> M ()
tie x hole v = case (hole, v) of
  (SAtom (WVar i) t, SAtom w t') | t == t' -> emitAt i (unName x) t (RCopy w)
  (STuple hs, STuple vs) | length hs == length vs -> zipWithM_ (tie x) hs vs
  _ -> failN ("the value of recursive binding " <> unName x <> " does not match its type")

project :: Natural -> SVal -> M SVal
project i v = do
  spend (fromIntegral (min i (fromIntegral maxEvalSteps)))
  case v of
    STuple vs | x : _ <- genericDrop i vs -> pure x
    _ -> failN ("projection " <> showT i <> " out of a value without that component")

mux :: W -> SVal -> SVal -> M SVal
mux c a b =
  tick >> case (a, b) of
    (SAtom x t, SAtom y t')
      | t /= t' -> failN "the branches of an if have different types"
      | x == y -> pure a
      | otherwise -> (`SAtom` t) <$> emitShared "mux" t (RMux c x y)
    (STuple xs, STuple ys) | length xs == length ys -> STuple <$> zipWithM (mux c) xs ys
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
  (VTuple vs, STuple ss) | length vs == length ss -> STuple <$> zipWithM register vs ss
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
    STuple [next, o] -> do
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

stateWires :: Value -> M (SVal, [(Int, Value)])
stateWires = \case
  VTuple vs -> do
    parts <- traverse stateWires vs
    pure (STuple (fmap fst parts), concatMap snd parts)
  v -> do
    i <- freshId
    pure (SAtom (WVar i) (valueTy v), [(i, v)])

----------------------------------------------------------------------
-- Top level

-- | Evaluate the top entity and run the final pass. The result satisfies
-- the invariants of "Gin.Core.Normal" when the program is well typed;
-- "Gin.Normalize.normalize" checks them.
buildModule :: Program -> Either GinError NModule
buildModule prog = do
  let top = progTop prog
      inputs = IntMap.fromList (zip [0 ..] (fmap portName (topInputs top)))
      st0 =
        St
          { stDefs = Map.fromList [(defName d, d) | d <- progDefs prog]
          , stInputs = inputs
          , stNextId = IntMap.size inputs
          , stBinds = IntMap.empty
          , stEmitted = 0
          , stSteps = 0
          , stShared = Map.empty
          , stAliases = IntMap.empty
          , stGlobals = Map.empty
          , stActive = Set.empty
          , stCurDef = Nothing
          , stDepth = 0
          }
  (outs, st) <- runStateT (elaborate top) st0
  withContext ("in top entity " <> topName top) (assemble prog outs st)

elaborate :: TopEntity -> M [(Port, W)]
elaborate top = inContext ("in top entity " <> topName top) $ do
  when (null (topOutputs top)) $ failN "the top entity has no outputs"
  f <- global (topDef top)
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
  | STuple [o, rest] <- v = (o :) <$> spine (n - 1) rest
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

assemble :: Program -> [(Port, W)] -> St -> Either GinError NModule
assemble prog outs st = do
  let raw = stBinds st
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
  let live = reachable binds (fmap snd outs')
      ordered = [(i, b) | i <- order, IntSet.member i live, Just b <- [IntMap.lookup i binds]]
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
