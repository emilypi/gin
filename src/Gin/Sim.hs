-- | Reference simulators, used for translation validation.
--
-- Both simulators transcribe @docs/semantics.md@. They are written
-- independently of the normalizer so that agreement between them (and
-- with the Lean model and the HDL simulation) is evidence that the
-- compiler preserved the meaning of the program.
--
-- 'simulateCore' is a denotational interpreter of the core IR. A signal
-- denotes a lazy stream with one element per cycle, a function denotes a
-- Haskell closure, and a recursive @let@ ties the knot through those lazy
-- streams. Before any stream element is demanded, the interpreter checks
-- that every feedback loop passes through @sig.register@: each signal
-- carries the set of recursive binders its current-cycle value depends
-- on (@sig.register@ resets that set, @sig.lift@ and @sig.mealy@ propagate
-- it from their inputs), and a binder that reaches itself is reported as
-- not productive instead of looping.
--
-- 'simulateNormal' runs the normal form cycle by cycle: register state in
-- a map, binds evaluated in order, outputs read, then registers updated.
module Gin.Sim
  ( simulateCore
  , simulateNormal
  ) where

import Control.Monad (foldM, unless, when, zipWithM, zipWithM_)
import Data.Graph (SCC (..), stronglyConnComp)
import Data.List (genericDrop, transpose, uncons)
import Data.List.NonEmpty qualified as NonEmpty
import Data.Map.Lazy qualified as LMap
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe, listToMaybe, mapMaybe)
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
  , primArity
  , primName
  , validValue
  , valueTy
  )
import Gin.Error (GinError, Stage (StSim), ginError, withContext)
import Gin.Sim.Prim (evalPrim)
import Numeric.Natural (Natural)

-- | Simulate the core IR directly. One input row per cycle (values in
-- input port order); returns one output row per cycle (output port
-- order). Precondition: 'Gin.Core.Check.checkProgram' succeeded. Errors
-- use 'StSim' (e.g. arity or type mismatch in a row, or a recursive let
-- that is not productive).
--
-- Rows are validated before anything is evaluated. A top entity with
-- several outputs must return the right-nested product of
-- @docs/semantics.md@; output @j@ is read along that spine. Only signals,
-- and tuples of signals, may be defined in terms of themselves by a
-- recursive @let@: recursion through a plain value or a function is
-- rejected rather than evaluated. Evaluation deeper than 100000 nested
-- applications is reported as an error instead of exhausting the stack.
simulateCore :: Program -> [[Value]] -> Either GinError [[Value]]
simulateCore prog rows = do
  let top = progTop prog
      inputs = topInputs top
  validateRows [(portName p, portTy p) | p <- inputs] rows
  globals <- globalEnv prog
  topValue <-
    fromMaybe
      (Left (simError ("top entity def " <> unName (topDef top) <> " is not defined")))
      (Map.lookup (topDef top) globals)
  let columns = take (length inputs) (transpose rows <> repeat [])
      inputSignals = [DSig (Sig Set.empty (fmap (Right . fromValue) col)) | col <- columns]
  out <-
    withContext ("in def " <> unName (topDef top)) $
      applyAll 0 topValue inputSignals >>= asSignal "the top entity's result"
  readOutputs (topOutputs top) (length rows) (sigStream out)

-- | Simulate a normal-form module, same row conventions.
--
-- Binds are evaluated in list order, so each one may read only inputs and
-- earlier binds, except that an 'NReg' argument may refer forward. Every
-- bind and output value is checked against its declared type.
simulateNormal :: NModule -> [[Value]] -> Either GinError [[Value]]
simulateNormal nm rows = do
  validateRows [(unName n, t) | (n, t) <- nmInputs nm] rows
  go initial (zip [0 ..] rows) []
  where
    initial = Map.fromList [(nbName b, v) | b@NBind {nbRhs = NReg v _} <- nmBinds nm]
    go _ [] acc = Right (reverse acc)
    go regs ((t, row) : rest) acc = do
      (outs, regs') <- inCycle t (normalCycle nm regs row)
      go regs' rest (outs : acc)

----------------------------------------------------------------------
-- Shared

simError :: Text -> GinError
simError = ginError StSim

showT :: (Show a) => a -> Text
showT = Text.pack . show

inCycle :: Int -> Either GinError a -> Either GinError a
inCycle t = withContext ("in cycle " <> showT t)

-- | Every row has one valid value per port, of the port's type.
validateRows :: [(Text, Ty)] -> [[Value]] -> Either GinError ()
validateRows ports = zipWithM_ checkRow [0 ..]
  where
    checkRow t row = inCycle t $ do
      unless (length row == length ports) . Left . simError $
        "expected "
          <> showT (length ports)
          <> " input values ("
          <> Text.intercalate ", " (fmap fst ports)
          <> "), got "
          <> showT (length row)
      zipWithM_ checkValue ports row
    checkValue (name, ty) v =
      unless (validValue v && valueTy v == ty) . Left . simError $
        "input " <> name <> ": expected a value of type " <> showT ty <> ", got " <> showT v

-- | The value is valid and has the given type.
hasType :: Text -> Ty -> Value -> Either GinError Value
hasType what ty v
  | validValue v && valueTy v == ty = Right v
  | otherwise = Left (simError (what <> ": expected type " <> showT ty <> ", got " <> showT v))

----------------------------------------------------------------------
-- Core IR: semantic domain

-- | Identity of a recursive binder's signal: the evaluation depth of its
-- @let@ and the index of the signal among the leaves of that @let@'s
-- binders. Lets that are open at the same time have distinct depths.
type Placeholder = (Int, Int)

-- | Denotation of a core IR expression.
data D
  = DBool !Bool
  | DBV !Natural !Integer
  | DTuple ![D]
  | -- | A closure; the 'Int' is the evaluation depth of the application.
    DFun !(Int -> D -> Either GinError D)
  | DSig !Sig

data Sig = Sig
  { sigDeps :: !(Set Placeholder)
  -- ^ Recursive binders this signal's value depends on within one cycle.
  , sigStream :: [Either GinError D]
  -- ^ One element per cycle, produced lazily.
  }

-- | The evaluation context: global defs, and the depth of the current
-- application (bounded by 'maxEvalDepth').
data Ctx = Ctx
  { ctxGlobals :: Map Name (Either GinError D)
  , ctxDepth :: !Int
  }

type Env = Map Name D

-- | Bound on nested applications. Well-typed programs without recursion
-- among globals stay far below it; it turns runaway evaluation of
-- malformed input into an error.
maxEvalDepth :: Int
maxEvalDepth = 100000

fromValue :: Value -> D
fromValue = \case
  VBool b -> DBool b
  VBV w x -> DBV w x
  VTuple vs -> DTuple (fmap fromValue vs)

toValue :: D -> Either GinError Value
toValue = \case
  DBool b -> Right (VBool b)
  DBV w x -> Right (VBV w x)
  DTuple ds -> VTuple <$> traverse toValue ds
  DFun _ -> Left (simError "expected a value, got a function")
  DSig _ -> Left (simError "expected a value, got a signal")

asSignal :: Text -> D -> Either GinError Sig
asSignal what = \case
  DSig s -> Right s
  _ -> Left (simError (what <> " is not a signal"))

----------------------------------------------------------------------
-- Core IR: evaluation

-- | Global defs, each evaluated lazily at most once. Recursion among
-- globals is rejected up front, so the lazy map is well founded.
globalEnv :: Program -> Either GinError (Map Name (Either GinError D))
globalEnv prog = do
  let defs = progDefs prog
      graph = [(d, defName d, Set.toList (globalRefs (defBody d))) | d <- defs]
  case [NonEmpty.toList ds | NECyclicSCC ds <- stronglyConnComp graph] of
    [] -> Right ()
    ds : _ ->
      Left . simError $
        "recursion among globals: " <> Text.intercalate ", " (fmap (unName . defName) ds)
  let globals = LMap.fromList [(defName d, evalDef d) | d <- defs]
      evalDef d =
        withContext ("in def " <> unName (defName d)) (eval (Ctx globals 0) Map.empty (defBody d))
  Right globals

eval :: Ctx -> Env -> Expr -> Either GinError D
eval ctx env = \case
  EVar n -> maybe (Left (simError ("unbound variable " <> unName n))) Right (Map.lookup n env)
  EGlobal n ->
    fromMaybe (Left (simError ("unknown global " <> unName n))) (Map.lookup n (ctxGlobals ctx))
  ELit v -> Right (fromValue v)
  EPrim op _ -> Right (primValue op)
  EApp f args -> do
    fv <- eval ctx env f
    avs <- traverse (eval ctx env) args
    applyAll (ctxDepth ctx) fv avs
  ELam binders body -> case binders of
    [] -> Left (simError "lambda without binders")
    _ -> Right (closure ctx env (fmap fst binders) body)
  ELet False binds body -> do
    let bindOne e b = do
          d <- inBind b (eval ctx e (bindExpr b))
          Right (Map.insert (bindName b) d e)
    env' <- foldM bindOne env binds
    eval ctx env' body
  ELet True binds body -> letRec ctx env binds >>= \env' -> eval ctx env' body
  ETuple es -> DTuple <$> traverse (eval ctx env) es
  EProj i e ->
    eval ctx env e >>= \case
      DTuple ds | Just d <- listToMaybe (genericDrop i ds) -> Right d
      _ -> Left (simError ("projection " <> showT i <> " out of a value without that component"))
  EIf c t e ->
    eval ctx env c >>= \case
      DBool True -> eval ctx env t
      DBool False -> eval ctx env e
      _ -> Left (simError "if condition is not a Bool")

inBind :: Bind -> Either GinError a -> Either GinError a
inBind b = withContext ("in bind " <> unName (bindName b))

closure :: Ctx -> Env -> [Name] -> Expr -> D
closure ctx env names body = DFun $ \depth arg ->
  let ctx' = ctx {ctxDepth = depth}
   in case names of
        [x] -> eval ctx' (Map.insert x arg env) body
        x : xs -> Right (closure ctx' (Map.insert x arg env) xs body)
        [] -> eval ctx' env body

apply :: Int -> D -> D -> Either GinError D
apply depth f arg
  | depth >= maxEvalDepth =
      Left (simError ("evaluation exceeded " <> showT maxEvalDepth <> " nested applications"))
  | otherwise = case f of
      DFun g -> g (depth + 1) arg
      _ -> Left (simError "applied a value that is not a function")

applyAll :: Int -> D -> [D] -> Either GinError D
applyAll depth = foldM (apply depth)

-- | A prim as a curried function of 'primArity' arguments.
primValue :: PrimOp -> D
primValue op = collect (primArity op) []
  where
    collect k acc = DFun $ \depth arg ->
      if k <= 1
        then runPrim depth op (reverse (arg : acc))
        else Right (collect (k - 1) (arg : acc))

-- | A saturated prim application.
runPrim :: Int -> PrimOp -> [D] -> Either GinError D
runPrim depth op args
  | isCombinational op = fromValue <$> (traverse toValue args >>= evalPrim op)
  | otherwise = case (op, args) of
      (SigPure, [x]) -> Right (DSig (Sig Set.empty (repeat (Right x))))
      (SigLift _, f : ss) -> do
        sigs <- traverse (asSignal (primName op <> " argument")) ss
        let element xs = sequence xs >>= applyAll depth f
        Right . DSig $
          Sig (foldMap sigDeps sigs) (fmap element (zipStreams (fmap sigStream sigs)))
      (SigRegister v, [s]) -> do
        sg <- asSignal (primName op <> " argument") s
        Right (DSig (Sig Set.empty (Right (fromValue v) : sigStream sg)))
      (SigMealy v, [f, s]) -> do
        sg <- asSignal (primName op <> " argument") s
        Right (DSig (Sig (sigDeps sg) (mealyStream depth f (fromValue v) (sigStream sg))))
      _ -> Left (simError (primName op <> " applied to unexpected arguments"))

-- | Element-wise transposition of streams; ends with the shortest one.
zipStreams :: [[a]] -> [[a]]
zipStreams ss = case traverse uncons ss of
  Just cells -> fmap fst cells : zipStreams (fmap snd cells)
  Nothing -> []

-- | @(st(t+1), o(t)) = f (st t) (i t)@ with @st(0) = v@.
mealyStream :: Int -> D -> D -> [Either GinError D] -> [Either GinError D]
mealyStream depth f v0 = go (Right v0)
  where
    go st = \case
      [] -> []
      i : is ->
        let r = do
              s <- st
              x <- i
              applyAll depth f [s, x] >>= \case
                DTuple [s', o] -> Right (s', o)
                _ -> Left (simError "sig.mealy step function did not return a (state, output) pair")
         in fmap snd r : go (fmap fst r) is

----------------------------------------------------------------------
-- Core IR: recursive lets

-- | Binds of a recursive @let@, in dependency order: a bind that refers to
-- no binder of its strongly connected component is evaluated like a
-- non-recursive bind; each recursive component is evaluated by 'tieKnot'.
letRec :: Ctx -> Env -> [Bind] -> Either GinError Env
letRec ctx env0 binds = foldM step env0 (stronglyConnComp graph)
  where
    names = Set.fromList (fmap bindName binds)
    graph = [(b, bindName b, refs b) | b <- binds]
    refs b = Set.toList (Set.intersection names (freeVars (bindExpr b)))
    inner = ctx {ctxDepth = ctxDepth ctx + 1}
    step env = \case
      AcyclicSCC b -> do
        d <- inBind b (eval inner env (bindExpr b))
        Right (Map.insert (bindName b) d env)
      NECyclicSCC bs -> tieKnot ctx env (NonEmpty.toList bs)

-- | Where the signals sit in a signal-like type: one numbered leaf per
-- 'TSignal', nested along 'TProd'.
data Shape = Leaf !Int | Node ![Shape]

-- | Number the signal leaves of the given types from @next@; 'Nothing'
-- unless every type is a signal or a tuple of signal-like types.
shapes :: Int -> [Ty] -> Maybe (Int, [Shape])
shapes next = \case
  [] -> Just (next, [])
  t : ts -> do
    (next', s) <- case t of
      TSignal _ _ -> Just (next + 1, Leaf next)
      TProd cs -> fmap Node <$> shapes next cs
      _ -> Nothing
    fmap (s :) <$> shapes next' ts

-- | Leaf indices of a shape with the component path to each.
leafPaths :: Shape -> [(Int, [Int])]
leafPaths = \case
  Leaf l -> [(l, [])]
  Node ss -> concat [[(l, i : p) | (l, p) <- leafPaths s] | (i, s) <- zip [0 ..] ss]

-- | The signals at the leaves of a value of the given shape.
leaves :: Shape -> D -> Either GinError [(Int, Sig)]
leaves shape d = case (shape, d) of
  (Leaf l, DSig s) -> Right [(l, s)]
  (Node ss, DTuple ds) | length ss == length ds -> concat <$> zipWithM leaves ss ds
  _ -> Left (simError "recursive binding does not have the shape of its declared type")

-- | Replace the dependency set of every leaf signal.
relabel :: (Int -> Set Placeholder) -> Shape -> D -> D
relabel deps shape d = case (shape, d) of
  (Leaf l, DSig s) -> DSig s {sigDeps = deps l}
  (Node ss, DTuple ds) -> DTuple (zipWith (relabel deps) ss ds)
  _ -> d

-- | A recursive component: bind each binder to a placeholder of its type
-- whose streams are, lazily, those of the binder's own value; evaluate
-- the binds; reject a cycle of current-cycle dependencies among the
-- placeholders; and rebind each binder to its value, with dependencies on
-- the placeholders replaced by what those placeholders depend on.
tieKnot :: Ctx -> Env -> [Bind] -> Either GinError Env
tieKnot ctx env binds = do
  shps <- case shapes 0 (fmap bindTy binds) of
    Just (_, ss) -> Right ss
    Nothing ->
      Left . simError $
        "recursive let: "
          <> Text.intercalate ", " [unName (bindName b) <> " : " <> showT (bindTy b) | b <- binds]
          <> " is defined in terms of itself, but only signals and tuples of signals may be"
          <> " recursive (feedback through sig.register)"
  let depth = ctxDepth ctx
      inner = ctx {ctxDepth = depth + 1}
      results = [inBind b (eval inner env' (bindExpr b)) | b <- binds]
      streams =
        LMap.fromList
          [(l, leafStream p r) | (s, r) <- zip shps results, (l, p) <- leafPaths s]
      placeholder = \case
        Leaf l -> DSig (Sig (Set.singleton (depth, l)) (LMap.findWithDefault [] l streams))
        Node ss -> DTuple (fmap placeholder ss)
      env' = foldr (\(b, s) -> Map.insert (bindName b) (placeholder s)) env (zip binds shps)
  values <- sequence results
  sigs <- concat <$> zipWithM3 (\b s d -> inBind b (leaves s d)) binds shps values
  let local s = [l | (dep, l) <- Set.toList (sigDeps s), dep == depth]
      binderOf =
        Map.fromList
          [(l, unName (bindName b)) | (b, s) <- zip binds shps, (l, _) <- leafPaths s]
      loops = stronglyConnComp [(l, l, local s) | (l, s) <- sigs]
  case [NonEmpty.toList ls | NECyclicSCC ls <- loops] of
    [] -> Right ()
    ls : _ ->
      Left . simError $
        "recursive let is not productive: the value of "
          <> Text.intercalate ", " (Set.toList (Set.fromList (mapMaybe (`Map.lookup` binderOf) ls)))
          <> " at a cycle depends on itself at that cycle"
          <> " (feedback must pass through sig.register)"
  let resolved = LMap.fromList [(l, resolve (sigDeps s)) | (l, s) <- sigs]
      resolve = foldMap $ \p@(dep, l) ->
        if dep == depth then resolvedAt l else Set.singleton p
      resolvedAt l = LMap.findWithDefault Set.empty l resolved
      finals = [relabel resolvedAt s d | (s, d) <- zip shps values]
  Right (foldr (\(b, d) -> Map.insert (bindName b) d) env (zip binds finals))
  where
    zipWithM3 f as bs cs = sequence (zipWith3 f as bs cs)

-- | The stream at a component path of a binder's value.
leafStream :: [Int] -> Either GinError D -> [Either GinError D]
leafStream path = \case
  Left e -> repeat (Left e)
  Right d -> case follow path d of
    Just (DSig s) -> sigStream s
    _ -> repeat (Left (simError "recursive binding does not have the shape of its declared type"))
  where
    follow = \case
      [] -> Just
      i : is -> \case
        DTuple ds -> listToMaybe (drop i ds) >>= follow is
        _ -> Nothing

-- | Free local variables of an expression.
freeVars :: Expr -> Set Name
freeVars = \case
  EVar n -> Set.singleton n
  EGlobal _ -> Set.empty
  ELit _ -> Set.empty
  EPrim _ _ -> Set.empty
  EApp f as -> foldMap freeVars (f : as)
  ELam bs body -> freeVars body `Set.difference` Set.fromList (fmap fst bs)
  ELet False binds body ->
    foldr (\b acc -> freeVars (bindExpr b) <> Set.delete (bindName b) acc) (freeVars body) binds
  ELet True binds body ->
    foldMap freeVars (body : fmap bindExpr binds)
      `Set.difference` Set.fromList (fmap bindName binds)
  ETuple es -> foldMap freeVars es
  EProj _ e -> freeVars e
  EIf c t e -> foldMap freeVars [c, t, e]

-- | Globals an expression refers to.
globalRefs :: Expr -> Set Name
globalRefs = \case
  EGlobal n -> Set.singleton n
  EVar _ -> Set.empty
  ELit _ -> Set.empty
  EPrim _ _ -> Set.empty
  EApp f as -> foldMap globalRefs (f : as)
  ELam _ body -> globalRefs body
  ELet _ binds body -> foldMap globalRefs (body : fmap bindExpr binds)
  ETuple es -> foldMap globalRefs es
  EProj _ e -> globalRefs e
  EIf c t e -> foldMap globalRefs [c, t, e]

-- | The first @n@ elements of the top entity's output stream, split
-- along the right-nested product spine into one value per output port.
readOutputs :: [Port] -> Int -> [Either GinError D] -> Either GinError [[Value]]
readOutputs ports n = go 0 []
  where
    go t acc stream
      | t >= n = Right (reverse acc)
      | otherwise = case stream of
          [] -> Left (simError ("the output signal ends after " <> showT t <> " cycles"))
          x : xs -> do
            row <- inCycle t (x >>= toValue >>= spine ports)
            go (t + 1) (row : acc) xs
    spine ps v = case ps of
      [p] -> pure <$> port p v
      p : rest -> case v of
        VTuple [o, more] -> (:) <$> port p o <*> spine rest more
        _ ->
          Left . simError $
            "expected a pair ("
              <> portName p
              <> ", remaining outputs) on the output spine, got "
              <> showT v
      [] -> Left (simError "the top entity has no outputs")
    port p = hasType ("output " <> portName p) (portTy p)

----------------------------------------------------------------------
-- Normal form

-- | One cycle: evaluate the binds in order, read the outputs, and compute
-- the register state of the next cycle.
normalCycle :: NModule -> Map Name Value -> [Value] -> Either GinError ([Value], Map Name Value)
normalCycle nm regs row = do
  env <- foldM bindStep (Map.fromList (zip (fmap fst (nmInputs nm)) row)) (nmBinds nm)
  outs <- traverse (output env) (nmOutputs nm)
  regs' <- Map.fromList <$> sequence [nextState env b a | b@NBind {nbRhs = NReg _ a} <- nmBinds nm]
  Right (outs, regs')
  where
    bindStep env b = withContext ("in bind " <> unName (nbName b)) $ do
      when (Map.member (nbName b) env) . Left . simError $
        unName (nbName b) <> " is bound more than once"
      v <- case nbRhs b of
        NPrim op as -> traverse (atom env) as >>= evalPrim op
        NMux c th el ->
          atom env c >>= \case
            VBool True -> atom env th
            VBool False -> atom env el
            other -> Left (simError ("mux condition is not a Bool: " <> showT other))
        NReg _ _ ->
          maybe (Left (simError "register has no state")) Right (Map.lookup (nbName b) regs)
        NAtom a -> atom env a
      _ <- hasType (unName (nbName b)) (nbTy b) v
      Right (Map.insert (nbName b) v env)
    output env o = atom env (noAtom o) >>= hasType ("output " <> noName o) (noTy o)
    nextState env b a = do
      v <- atom env a >>= hasType ("register " <> unName (nbName b) <> " next value") (nbTy b)
      Right (nbName b, v)
    atom env = \case
      ALit v -> Right v
      AVar n ->
        maybe
          (Left (simError ("reads " <> unName n <> ", which is not an input or an earlier bind")))
          Right
          (Map.lookup n env)
