-- | Reference simulators, used for translation validation. They are how I
-- answer the README's third question: does the generated hardware still
-- implement the functionality described by Lean?
--
-- Both simulators transcribe @docs/semantics.md@. I keep them independent
-- of the normalizer so that agreement between them (and with the Lean
-- model and the HDL simulation) is evidence that the compiler preserved
-- the meaning of the program.
--
-- 'simulateCore' is an interpreter of the core IR. It first applies the
-- top entity to its input signals, which builds the network of signals
-- the program describes (inputs and @sig.pure@, @sig.lift@,
-- @sig.register@ and @sig.mealy@ nodes), and then runs that network one
-- cycle at a time. Values are computed by need, each at most once per
-- cycle. To keep long chains of values from nesting deeply, arguments,
-- @let@ binds and tuple components are computed as soon as they are
-- bound, unless they need a value that is still being computed; those
-- are computed when used. A value that is needed again while it is still
-- being computed depends on itself within the cycle: that is reported as
-- a recursive let that is not productive, instead of looping. At the end
-- of each cycle the next state of every register and mealy machine is
-- computed, so a cycle never needs the values of an earlier one.
--
-- 'simulateNormal' runs the normal form cycle by cycle: register state in
-- a map, binds evaluated in order, outputs read, then registers updated.
module Gin.Sim
  ( simulateCore
  , simulateNormal
  , isBudgetError
  ) where

import Control.Applicative ((<|>))
import Control.Monad (ap, foldM, unless, when, zipWithM, zipWithM_, (>=>))
import Control.Monad.ST (ST, runST)
import Data.Foldable (traverse_)
import Data.Graph (SCC (..), stronglyConnComp)
import Data.List (genericDrop)
import Data.List.NonEmpty qualified as NonEmpty
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (listToMaybe)
import Data.STRef (STRef, newSTRef, readSTRef, writeSTRef)
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
import Gin.Error (GinError (..), Stage (StSim), ginError, withContext)
import Gin.Limits (maxNormalBinds)
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
-- @docs/semantics.md@; output @j@ is read along that spine.
--
-- Results are those of evaluation by need: a value matters only if an
-- output, a register or mealy state, or another such value needs it, and
-- @if@ needs its condition and then one branch. A recursive @let@
-- therefore denotes the solution of its equations whenever every value
-- can be computed without needing itself within the same cycle. Feedback
-- through @sig.register@ or the state of @sig.mealy@ always qualifies,
-- and so do, for example, @p = (7, p.0)@, a @sig.lift@ whose function
-- ignores the argument that is fed back, and a @sig.mealy@ machine whose
-- output depends only on its state while its input is computed from that
-- output. When the condition of an @if@ needs the value being computed,
-- the @if@ still has a value if both branches agree on it, component by
-- component for tuples: the output of
-- @\\s e -> if e then (s + 1, s) else (s, s)@ is @s@ whatever @e@ is.
-- Any other value that needs itself within a cycle is not productive,
-- and is an error only if an output needs it (directly, or through a
-- register or mealy state).
--
-- Evaluation is bounded. Work done once for the whole run may take
-- @2^28@ evaluation steps and create @2^18@ signal nodes: building the
-- signal network, and computing the values that are the same in every
-- cycle, such as global definitions and the binds of a recursive @let@
-- met while the network is built, even when a cycle is the first to need
-- them. Each cycle may take a further @2^20@ steps, so a run takes at
-- most @2^28 + rows * 2^20@ steps. Going beyond these, or nesting values
-- and applications more than 100000 deep (for example in a recursive
-- function that never returns), is an error.
--
-- A step is an expression evaluated, an argument, @let@ bind or tuple
-- component bound (variables and literals included), a component of a
-- literal tuple, a value computed or a function applied, and in a cycle
-- also a node visited, a register or mealy machine advanced, or a
-- component of its next state stored. Every node counts against the
-- node bound: inputs, @sig.pure@, @sig.lift@ (identity lifts included),
-- registers, mealy machines and the nodes that stand for recursive
-- binders, whether the network is being built or a value computed once
-- creates them (it keeps them for the rest of the run); signals a cycle
-- makes and drops are not counted. A cycle may take 16 steps for each
-- bind a normal form may have ('Gin.Limits.maxNormalBinds'), and
-- evaluation takes about 6 steps a cycle for an operation inside a
-- function, 10 for a @sig.lift@ node of one operation and 3 for a
-- register. A program that normalizes can still exceed these bounds if
-- evaluating it takes far more steps, or nodes, than its normal form has
-- binds: one that applies functions @2^17@ times a cycle to compute the
-- identity, which normalizes to no binds at all, is stopped in cycle 0,
-- and ordinary helper-call overhead and identity lifts can likewise
-- exceed them. Exceeding a bound returns an error for which
-- 'isBudgetError' holds: the simulation is inconclusive, not a
-- disagreement, and callers should report it as such. Whenever
-- 'simulateCore' returns a result, it agrees with 'simulateNormal' on
-- the normalized program.
simulateCore :: Program -> [[Value]] -> Either GinError [[Value]]
simulateCore prog rows = do
  validateRows [(portName p, portTy p) | p <- topInputs (progTop prog)] rows
  noGlobalRecursion prog
  runST (runCore prog rows)

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

-- | Message prefix of every error raised because a simulation bound was
-- exceeded, as opposed to an error in the program or the rows.
budgetPrefix :: Text
budgetPrefix = "reference simulation budget exceeded: "

budgetError :: Text -> GinError
budgetError = simError . (budgetPrefix <>)

-- | Did 'simulateCore' stop because it exceeded one of its bounds
-- (evaluation steps, network nodes, nesting depth)? Such a result is
-- inconclusive: it says nothing about whether the program agrees with
-- its vectors. I would rather report it as @SKIP@ ("Gin.Driver") than
-- count it as a disagreement.
isBudgetError :: GinError -> Bool
isBudgetError e = errStage e == StSim && budgetPrefix `Text.isPrefixOf` errMessage e

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
-- Core IR: limits

-- | Evaluation steps the work done once for the whole run may take
-- ('Once'): building the signal network, and computing the values that
-- are the same in every cycle. 4096 for each bind a normal form may have
-- ('maxNormalBinds'), @2^28@ in all.
buildSteps :: Int
buildSteps = 4096 * maxNormalBinds

-- | Evaluation steps each cycle may take ('PerCycle'): 16 for each bind a
-- normal form may have, @2^20@ in all. Each cycle starts with the full
-- budget, so the steps of a run grow with its rows, as the work of
-- 'simulateNormal' does.
cycleSteps :: Int
cycleSteps = 16 * maxNormalBinds

-- | Signal nodes the work done once may create: four times
-- 'maxNormalBinds', @2^18@ in all. Every node counts (inputs, @sig.pure@
-- and @sig.lift@ nodes, registers, mealy machines and the nodes standing
-- for recursive binders), so this is not a bound on binds: a normal form
-- has no bind for an input, a @sig.pure@ or an identity lift, and a
-- design of 65536 registers built from four nodes each exceeds it
-- although its normal form has only 65536 binds. Nodes are kept for the
-- whole run, so this bounds the memory they hold, and the steps a cycle
-- spends visiting the network.
maxNetworkNodes :: Int
maxNetworkNodes = 4 * maxNormalBinds

-- | Bound on values being computed and functions being applied at the
-- same time. Well-typed programs without unbounded recursion stay far
-- below it; it keeps runaway recursion from exhausting the stack.
maxEvalDepth :: Int
maxEvalDepth = 100000

-- | Context lines kept on an error raised inside nested evaluation.
maxContextLines :: Int
maxContextLines = 16

----------------------------------------------------------------------
-- Core IR: semantic domain

-- | Denotation of a core IR expression, in weak head normal form.
data D s
  = DBool !Bool
  | DBV !Natural !Integer
  | DTuple ![Thunk s]
  | -- | A closure, applied to an argument that may not be computed yet.
    DFun !(Thunk s -> Eval s (D s))
  | DSig !(Node s)

-- | A value that may not have been computed yet.
data Thunk s
  = Ready !(D s)
  | -- | A register or mealy state component that was not productive.
    Undefined !(Loop s)
  | Lazy !(Cell s)

-- | A value computed when it is first needed.
data Cell s = Cell
  { cellLabel :: !(Maybe Text)
  -- ^ The recursive binder this value belongs to, named in loop errors.
  , cellContext :: !(Maybe Text)
  -- ^ Context added to an error raised while computing the value.
  , cellCharge :: !Charge
  -- ^ The bound its computation counts against: that of the work done
  -- when the cell was created.
  , cellState :: !(STRef s (CellState s))
  }

data CellState s
  = -- | Not computed yet. A 'Guard' records an earlier attempt that
    -- needed a value still being computed, and when it would fail again.
    Pending !(Maybe (Guard s)) (Eval s (D s))
  | -- | Being computed, by the activation with this number.
    Running !Int
  | Done (D s)

-- | An activation: a cell being computed, and the number of the
-- computation, so a later computation of the same cell is distinguished.
data Active s = Active !(STRef s (CellState s)) !Int

-- | A failed attempt to compute a value, made while the given activation
-- was the innermost one (or at top level). While that activation is
-- still running, everything the attempt found running still is, so
-- trying again would fail the same way.
data Guard s = Guard !(Maybe (Active s)) !(Loop s)

-- | A node of the signal network. Its value at the current cycle is
-- created when it is first asked for in that cycle.
data Node s = Node
  { nodeId :: !Int
  , nodeKind :: !(NodeKind s)
  , nodeCell :: !(STRef s (Maybe (Int, Thunk s)))
  -- ^ The cycle the cached value belongs to, and the value.
  }

data NodeKind s
  = -- | A top-entity input; the cycle loop sets its value.
    NInput
  | NPure !(Thunk s)
  | NLift !(Thunk s) ![Node s]
  | -- | The state (the cycle it belongs to, and its value) and the input.
    NRegister !(STRef s (Int, Thunk s)) !(Node s)
  | -- | Step function, state, input, and the step result of one cycle.
    NMealy !(Thunk s) !(STRef s (Int, Thunk s)) !(Node s) !(STRef s (Maybe (Int, Thunk s)))
  | -- | A recursive binder of signal type, and the node it stands for.
    NPlaceholder !Text !(Thunk s)

type Env s = Map Name (Thunk s)

fromValue :: Value -> D s
fromValue = \case
  VBool b -> DBool b
  VBV w x -> DBV w x
  VTuple vs -> DTuple (fmap (Ready . fromValue) vs)

----------------------------------------------------------------------
-- Core IR: evaluation monad

-- | Why evaluation stopped.
data Failure s
  = -- | A value was needed while it was being computed.
    Bottom !(Loop s)
  | -- | Anything else; ends the simulation.
    Abort !GinError

data Loop s = Loop
  { loopOrigin :: !(Maybe (STRef s (CellState s)))
  -- ^ The value needed again while being computed; 'Nothing' once the
  -- failure has propagated past it, so the whole loop is known.
  , loopNames :: ![Text]
  -- ^ Recursive binders on the loop, most recently passed first.
  , loopCycle :: !Int
  -- ^ The cycle, or -1 while the signal network is built.
  }

data Sim s = Sim
  { simOnceSteps :: !(STRef s Int)
  -- ^ Steps of the work done once, against 'buildSteps'.
  , simSteps :: !(STRef s Int)
  -- ^ Steps of the current cycle, against 'cycleSteps'.
  , simNodes :: !(STRef s Int)
  -- ^ Nodes created by the work done once.
  , simCycle :: !(STRef s Int)
  , simFresh :: !(STRef s Int)
  -- ^ Numbers for nodes and activations.
  , simGlobals :: !(STRef s (Map Name (Thunk s)))
  }

-- | Which work evaluation is doing, and so which bound its steps count
-- against.
data Charge
  = -- | Work whose result is kept for the whole run: building the signal
    -- network, and computing a value created while doing such work (a
    -- global definition, or a bind of a recursive @let@ met while the
    -- network is built), even when a cycle is the first to need it. Such
    -- a value is the same in every cycle, so it is computed once. Its
    -- steps count against 'buildSteps', and the nodes it creates, which
    -- it keeps, against 'maxNetworkNodes'.
    Once
  | -- | Computing the values of one cycle, against 'cycleSteps'.
    PerCycle
  deriving stock (Eq)

-- | Where evaluation is: its nesting depth, the innermost activation, and
-- the work it is doing.
data Here s = Here !Int !(Maybe (Active s)) !Charge

-- | Evaluation with a shared step budget.
newtype Eval s a = Eval (Sim s -> Here s -> ST s (Either (Failure s) a))

runEval :: Eval s a -> Sim s -> Here s -> ST s (Either (Failure s) a)
runEval (Eval m) = m

instance Functor (Eval s) where
  fmap f (Eval m) = Eval $ \sim here -> fmap f <$> m sim here

instance Applicative (Eval s) where
  pure x = Eval $ \_ _ -> pure (Right x)
  (<*>) = ap

instance Monad (Eval s) where
  Eval m >>= k = Eval $ \sim here ->
    m sim here >>= \case
      Left f -> pure (Left f)
      Right x -> runEval (k x) sim here

liftST :: ST s a -> Eval s a
liftST m = Eval $ \_ _ -> Right <$> m

askSim :: Eval s (Sim s)
askSim = Eval $ \sim _ -> pure (Right sim)

innermost :: Eval s (Maybe (Active s))
innermost = Eval $ \_ (Here _ active _) -> pure (Right active)

currentCharge :: Eval s Charge
currentCharge = Eval $ \_ (Here _ _ c) -> pure (Right c)

-- | Run a computation as the given work.
withCharge :: Charge -> Eval s a -> Eval s a
withCharge c (Eval m) = Eval $ \sim (Here d active _) -> m sim (Here d active c)

failWith :: Failure s -> Eval s a
failWith f = Eval $ \_ _ -> pure (Left f)

abort :: Text -> Eval s a
abort = failWith . Abort . simError

-- | Run a computation, returning how it failed instead of failing.
attempt :: Eval s a -> Eval s (Either (Failure s) a)
attempt (Eval m) = Eval $ \sim here -> Right <$> m sim here

-- | Catch a loop; any other failure propagates.
tryBottom :: Eval s a -> Eval s (Either (Loop s) a)
tryBottom m =
  attempt m >>= \case
    Right x -> pure (Right x)
    Left (Bottom l) -> pure (Left l)
    Left (Abort e) -> failWith (Abort e)

-- | Charge one evaluation step.
tick :: Eval s ()
tick = charge 1

-- | Charge evaluation steps to the work being done: against 'buildSteps'
-- for work done once, and against 'cycleSteps' in a cycle.
charge :: Int -> Eval s ()
charge k = Eval $ \sim (Here _ _ c) -> do
  let (counter, limit) = case c of
        Once -> (simOnceSteps sim, buildSteps)
        PerCycle -> (simSteps sim, cycleSteps)
  n <- readSTRef counter
  if n <= limit - k
    then Right () <$ (writeSTRef counter $! n + k)
    else do
      building <- (< 0) <$> readSTRef (simCycle sim)
      let work = case c of
            Once
              | building -> "building the signal network needs"
              | otherwise -> "the values computed once for the whole run need"
            PerCycle -> "the cycle needs"
      pure . Left . Abort . budgetError $
        work <> " more than " <> showT limit <> " evaluation steps"

-- | One level deeper, bounded by 'maxEvalDepth', optionally inside a new
-- activation.
deeper :: Maybe (Active s) -> Eval s a -> Eval s a
deeper new (Eval m) = Eval $ \sim (Here d active c) ->
  if d >= maxEvalDepth
    then
      pure . Left . Abort . budgetError $
        "evaluation nested more than "
          <> showT maxEvalDepth
          <> " values and applications deep (a recursive function that does not return?)"
    else m sim (Here (d + 1) (new <|> active) c)

fresh :: Eval s Int
fresh = do
  sim <- askSim
  liftST $ do
    i <- readSTRef (simFresh sim)
    i <$ (writeSTRef (simFresh sim) $! i + 1)

currentCycle :: Eval s Int
currentCycle = askSim >>= liftST . readSTRef . simCycle

-- | A value computed on first use, as part of the work being done now.
delay :: Maybe Text -> Maybe Text -> Eval s (D s) -> Eval s (Thunk s)
delay label ctx m = do
  c <- currentCharge
  Lazy . Cell label ctx c <$> liftST (newSTRef (Pending Nothing m))

-- | A value whose computation just failed with the given loop, to be
-- computed again when it is needed and could succeed.
retry :: Maybe Text -> Loop s -> Eval s (D s) -> Eval s (Thunk s)
retry ctx loop m = do
  active <- innermost
  c <- currentCharge
  Lazy . Cell Nothing ctx c <$> liftST (newSTRef (Pending (Just (Guard active loop)) m))

-- | Is the activation (or top level, for 'Nothing') still running?
running :: Maybe (Active s) -> Eval s Bool
running = \case
  Nothing -> pure True
  Just (Active ref a) ->
    liftST (readSTRef ref) >>= \case
      Running a' -> pure (a == a')
      _ -> pure False

-- | The value of a thunk, computing it if needed. A computation that
-- fails because it needs a value still being computed is not cached as a
-- failure: once that value is known it may succeed. Until then (see
-- 'Guard') it fails again without being repeated.
force :: Thunk s -> Eval s (D s)
force = \case
  Ready d -> pure d
  Undefined l -> failWith (Bottom l)
  Lazy c ->
    liftST (readSTRef (cellState c)) >>= \case
      Done d -> pure d
      Running _ -> do
        t <- currentCycle
        failWith (Bottom (Loop (Just (cellState c)) [] t))
      Pending g m -> maybe (pure Nothing) recheck g >>= maybe (compute c m) (failWith . passing c . Bottom)
  where
    recheck (Guard active l) = (\stuck -> if stuck then Just l else Nothing) <$> running active

-- | Compute a cell's value as the work that created it, so a value
-- created while building the network is charged to the work done once
-- even when a cycle is the first to need it.
compute :: Cell s -> Eval s (D s) -> Eval s (D s)
compute c m = withCharge (cellCharge c) tick >> do
  a <- fresh
  outer <- innermost
  liftST (writeSTRef (cellState c) (Running a))
  attempt (deeper (Just (Active (cellState c) a)) (withCharge (cellCharge c) m)) >>= \case
    Right d -> d <$ liftST (writeSTRef (cellState c) (Done d))
    Left f -> do
      liftST . writeSTRef (cellState c) $ case f of
        Bottom l -> Pending (Just (Guard outer l)) m
        Abort _ -> Pending Nothing m
      failWith (passing c f)

-- | Record that a failure propagated out of the computation of a cell.
passing :: Cell s -> Failure s -> Failure s
passing c = \case
  Bottom l
    | Just origin <- loopOrigin l ->
        Bottom
          l
            { loopNames = maybe id addName (cellLabel c) (loopNames l)
            , loopOrigin = if origin == cellState c then Nothing else Just origin
            }
    | otherwise -> Bottom l
  Abort e -> Abort (maybe e (`nestedIn` e) (cellContext c))
  where
    addName n ns
      | n `elem` ns || length ns >= 8 = ns
      | otherwise = n : ns

-- | Add a context line, unless the error already carries many.
nestedIn :: Text -> GinError -> GinError
nestedIn ctx e
  | length (errContext e) < maxContextLines = e {errContext = errContext e <> [ctx]}
  | otherwise = e

-- | Turn every failure into an error with the given context line.
within :: Text -> Eval s a -> Eval s a
within ctx m =
  attempt m >>= \case
    Right x -> pure x
    Left f -> do
      let e = failureError f
      failWith (Abort e {errContext = errContext e <> [ctx]})

failureError :: Failure s -> GinError
failureError = \case
  Abort e -> e
  Bottom l -> loopError l

loopError :: Loop s -> GinError
loopError l =
  simError $
    "recursive let is not productive: "
      <> subject
      <> atCycle
      <> " depends on itself (feedback must pass through sig.register or the state of"
      <> " sig.mealy)"
  where
    subject = case reverse (loopNames l) of
      [] -> "a value"
      ns -> "the value of " <> Text.intercalate ", " ns
    atCycle
      | loopCycle l >= 0 = " at cycle " <> showT (loopCycle l)
      | otherwise = ""

----------------------------------------------------------------------
-- Core IR: running the program

runCore :: Program -> [[Value]] -> ST s (Either GinError [[Value]])
runCore prog rows = do
  sim <-
    Sim
      <$> newSTRef 0
      <*> newSTRef 0
      <*> newSTRef 0
      <*> newSTRef (-1)
      <*> newSTRef 0
      <*> newSTRef Map.empty
  either (Left . failureError) Right <$> runEval (coreRun prog rows) sim (Here 0 Nothing Once)

-- | Build the signal network, then run it one cycle per row. Each cycle
-- computes the nodes in dependency order first (a node that needs a value
-- still being computed is left for later), so long chains of signals do
-- not nest; then reads the outputs; then computes every next state.
-- The work done once and every cycle each have their own step budget
-- ('Charge').
coreRun :: Program -> [[Value]] -> Eval s [[Value]]
coreRun prog rows = do
  defineGlobals prog
  let top = progTop prog
  inputs <- traverse (const (newNode NInput)) (topInputs top)
  (out, order) <- within ("in def " <> unName (topDef top)) $ do
    g <- globalThunk ("top entity def " <> unName (topDef top) <> " is not defined") (topDef top)
    f <- force g
    out <- applyAll f [Ready (DSig n) | n <- inputs] >>= asNode "the top entity's result"
    order <- network out
    pure (out, order)
  let machines = filter stateful order
      step acc (t, row) = withCharge PerCycle $ do
        sim <- askSim
        liftST $ do
          writeSTRef (simCycle sim) t
          writeSTRef (simSteps sim) 0
        zipWithM_ (\n v -> liftST (writeSTRef (nodeCell n) (Just (t, Ready (fromValue v))))) inputs row
        outs <- within ("in cycle " <> showT t) $ do
          traverse_ (\n -> tick >> tryBottom (cellOf n >>= force)) order
          v <- cellOf out >>= force >>= deepValue
          either (failWith . Abort) pure (splitOutputs (topOutputs top) v)
        commits <- within ("in cycle " <> showT t) (traverse (advance t) machines)
        liftST (sequence_ commits)
        pure (outs : acc)
  reverse <$> foldM step [] (zip [0 ..] rows)
  where
    stateful n = case nodeKind n of
      NRegister {} -> True
      NMealy {} -> True
      _ -> False

-- | Recursion among globals is rejected up front: a global is evaluated
-- at most once, so it must not need itself.
noGlobalRecursion :: Program -> Either GinError ()
noGlobalRecursion prog =
  case [NonEmpty.toList ds | NECyclicSCC ds <- stronglyConnComp graph] of
    [] -> Right ()
    ds : _ ->
      Left . simError $
        "recursion among globals: " <> Text.intercalate ", " (fmap (unName . defName) ds)
  where
    graph = [(d, defName d, Set.toList (globalRefs (defBody d))) | d <- progDefs prog]

-- | Every global def, as a value computed on first use.
defineGlobals :: Program -> Eval s ()
defineGlobals prog = do
  defs <- traverse global (progDefs prog)
  sim <- askSim
  liftST (writeSTRef (simGlobals sim) (Map.fromList defs))
  where
    global d = do
      th <- delay Nothing (Just ("in def " <> unName (defName d))) (eval Map.empty (defBody d))
      pure (defName d, th)

globalThunk :: Text -> Name -> Eval s (Thunk s)
globalThunk missing n = do
  sim <- askSim
  globals <- liftST (readSTRef (simGlobals sim))
  maybe (abort missing) pure (Map.lookup n globals)

-- | Every node the network rooted at a node depends on, each after the
-- nodes it reads (except around loops). Recursive binders are resolved
-- on the way, so the whole network is built before the first cycle.
network :: Node s -> Eval s [Node s]
network root = go Set.empty [Enter root] []
  where
    go _ [] order = pure (reverse order)
    go seen (visit : rest) order = case visit of
      Leave n -> go seen rest (n : order)
      Enter n
        | Set.member (nodeId n) seen -> go seen rest order
        | otherwise -> do
            next <- successors n
            go (Set.insert (nodeId n) seen) (fmap Enter next <> (Leave n : rest)) order
    successors n = case nodeKind n of
      NInput -> pure []
      NPure _ -> pure []
      NLift _ ns -> pure ns
      NRegister _ s -> pure [s]
      NMealy _ _ s _ -> pure [s]
      NPlaceholder _ target ->
        tryBottom (force target) >>= \case
          Right (DSig m) -> pure [m]
          _ -> pure []

-- | A step of the depth-first walk in 'network'.
data Visit s = Enter (Node s) | Leave (Node s)

-- | Compute the next state of a register or mealy node, with every
-- component that is not productive marked as such, and return the action
-- that stores it. All next states are computed before any is stored.
advance :: Int -> Node s -> Eval s (ST s ())
advance t n = tick >> case nodeKind n of
  NRegister st s -> store st <$> settle (cellOf s >>= force)
  NMealy f st i memo -> store st <$> settle (mealyStep f st i memo >>= force >>= pairPart 0 >>= force)
  _ -> pure (pure ())
  where
    store st th = writeSTRef st (t + 1, th)

-- | Compute a value completely, keeping each component that is not
-- productive as 'Undefined'.
settle :: Eval s (D s) -> Eval s (Thunk s)
settle m =
  tick >> tryBottom m >>= \case
    Left l -> pure (Undefined l)
    Right d -> case d of
      DTuple ths -> Ready . DTuple <$> traverse (settle . force) ths
      DBool _ -> pure (Ready d)
      DBV _ _ -> pure (Ready d)
      _ -> abort "the state of a register or mealy machine is not a value"

deepValue :: D s -> Eval s Value
deepValue = \case
  DBool b -> pure (VBool b)
  DBV w x -> pure (VBV w x)
  DTuple ths -> VTuple <$> traverse (force >=> deepValue) ths
  DFun _ -> abort "expected a value, got a function"
  DSig _ -> abort "expected a value, got a signal"

-- | Split an output value along the right-nested product spine into one
-- value per output port.
splitOutputs :: [Port] -> Value -> Either GinError [Value]
splitOutputs ports v = case ports of
  [p] -> pure <$> port p v
  p : rest -> case v of
    VTuple [o, more] -> (:) <$> port p o <*> splitOutputs rest more
    _ ->
      Left . simError $
        "expected a pair ("
          <> portName p
          <> ", remaining outputs) on the output spine, got "
          <> showT v
  [] -> Left (simError "the top entity has no outputs")
  where
    port p = hasType ("output " <> portName p) (portTy p)

----------------------------------------------------------------------
-- Core IR: signals

-- | A new node. Nodes created by work done once ('Once') are counted
-- against 'maxNetworkNodes': those of the network, and those of a value
-- computed once, such as a global signal a cycle is the first to need,
-- which keeps them for the rest of the run. A node created in a cycle,
-- by a function that makes a signal it cannot return (signals carry only
-- data), is dropped when the cycle ends and is not counted.
newNode :: NodeKind s -> Eval s (Node s)
newNode kind = do
  sim <- askSim
  kept <- (== Once) <$> currentCharge
  when kept $ do
    count <- liftST (readSTRef (simNodes sim))
    when (count >= maxNetworkNodes) . failWith . Abort . budgetError $
      "the signal network has more than " <> showT maxNetworkNodes <> " nodes"
    liftST (writeSTRef (simNodes sim) $! count + 1)
  i <- fresh
  Node i kind <$> liftST (newSTRef Nothing)

asNode :: Text -> D s -> Eval s (Node s)
asNode what = \case
  DSig n -> pure n
  _ -> abort (what <> " is not a signal")

-- | The value of a signal at the current cycle, not yet computed.
cellOf :: Node s -> Eval s (Thunk s)
cellOf n = case nodeKind n of
  NPure x -> pure x
  NRegister st _ -> stateAt st
  NInput -> cached (nodeCell n) (abort "internal error: an input has no value at this cycle")
  NLift f ns -> cached (nodeCell n) . delay Nothing Nothing $ do
    fv <- force f
    traverse cellOf ns >>= applyAll fv
  NMealy f st i memo ->
    cached (nodeCell n) . delay Nothing Nothing $
      mealyStep f st i memo >>= force >>= pairPart 1 >>= force
  NPlaceholder name target ->
    cached (nodeCell n) . delay (Just name) Nothing $
      force target >>= asNode name >>= cellOf >>= force

-- | A per-cycle value, created at most once per cycle.
cached :: STRef s (Maybe (Int, Thunk s)) -> Eval s (Thunk s) -> Eval s (Thunk s)
cached ref make = do
  t <- currentCycle
  liftST (readSTRef ref) >>= \case
    Just (t', th) | t' == t -> pure th
    _ -> do
      th <- make
      th <$ liftST (writeSTRef ref (Just (t, th)))

-- | The state of a register or mealy machine at the current cycle.
stateAt :: STRef s (Int, Thunk s) -> Eval s (Thunk s)
stateAt st = do
  t <- currentCycle
  (t', th) <- liftST (readSTRef st)
  if t' == t
    then pure th
    else abort "internal error: a register or mealy state is not available at this cycle"

-- | The step function applied to the current state and input.
mealyStep
  :: Thunk s -> STRef s (Int, Thunk s) -> Node s -> STRef s (Maybe (Int, Thunk s)) -> Eval s (Thunk s)
mealyStep f st i memo = cached memo . delay Nothing Nothing $ do
  fv <- force f
  s <- stateAt st
  x <- cellOf i
  applyAll fv [s, x]

pairPart :: Int -> D s -> Eval s (Thunk s)
pairPart k = \case
  DTuple [s, o] -> pure (if k == 0 then s else o)
  _ -> abort "sig.mealy step function did not return a (state, output) pair"

----------------------------------------------------------------------
-- Core IR: expressions

eval :: Env s -> Expr -> Eval s (D s)
eval env expr = do
  tick
  case expr of
    EVar n -> maybe (abort ("unbound variable " <> unName n)) force (Map.lookup n env)
    EGlobal n -> globalThunk ("unknown global " <> unName n) n >>= force
    ELit v -> literal v
    EPrim op _ -> pure (primValue op)
    EApp f args -> do
      fv <- eval env f
      traverse (eager Nothing env) args >>= applyAll fv
    ELam binders body -> case binders of
      [] -> abort "lambda without binders"
      _ -> pure (closure env (fmap fst binders) body)
    ELet False binds body -> do
      let bind e b = do
            th <- eager (Just ("in bind " <> unName (bindName b))) e (bindExpr b)
            pure (Map.insert (bindName b) th e)
      env' <- foldM bind env binds
      eval env' body
    ELet True binds body -> letRec env binds >>= (`eval` body)
    ETuple es -> DTuple <$> traverse (eager Nothing env) es
    EProj i e -> eval env e >>= project i >>= force
    EIf c t e -> conditional env c t e

-- | An argument, @let@ bind or tuple component, computed now so chains of
-- them do not nest. One that needs a value still being computed is left
-- to be computed when it is used, which is what makes evaluation by need.
-- Binding one costs a step, even a variable or a literal, so binding many
-- of them (a wide tuple of copies of a variable) is not free.
eager :: Maybe Text -> Env s -> Expr -> Eval s (Thunk s)
eager ctx env expr =
  tick >> case expr of
    EVar n | Just th <- Map.lookup n env -> pure th
    ELit v -> Ready <$> literal v
    e ->
      attempt (eval env e) >>= \case
        Right d -> pure (Ready d)
        Left (Bottom loop) -> retry ctx loop (eval env e)
        Left (Abort err) -> failWith (Abort (maybe err (`nestedIn` err) ctx))

-- | A literal, costing a step for each component of a tuple, as tuples
-- and scalars in it are counted by 'valueSize', beyond the step already
-- charged for the expression.
literal :: Value -> Eval s (D s)
literal v = case v of
  VTuple _ -> fromValue v <$ charge (valueSize v - 1)
  _ -> pure (fromValue v)

-- | The tuples and scalars a value is made of.
valueSize :: Value -> Int
valueSize = go 0
  where
    go !n = \case
      VTuple vs -> foldl' go (n + 1) vs
      _ -> n + 1

project :: Natural -> D s -> Eval s (Thunk s)
project i = \case
  DTuple ths | Just th <- listToMaybe (genericDrop i ths) -> pure th
  _ -> abort ("projection " <> showT i <> " out of a value without that component")

-- | @if c t e@ computes @c@, then one branch. When the condition needs the
-- value being computed, the result is what both branches agree on
-- ('agree').
conditional :: Env s -> Expr -> Expr -> Expr -> Eval s (D s)
conditional env c t e =
  tryBottom (eval env c) >>= \case
    Right d -> choose d (eval env t) (eval env e)
    Left loop -> do
      cond <- retry Nothing loop (eval env c)
      th <- delay Nothing Nothing (eval env t)
      el <- delay Nothing Nothing (eval env e)
      agree loop cond th el

choose :: D s -> Eval s a -> Eval s a -> Eval s a
choose d th el = case d of
  DBool True -> th
  DBool False -> el
  _ -> abort "if condition is not a Bool"

-- | The value of an @if@ whose condition could not be computed: equal
-- scalar branches give that scalar, and tuple branches give a tuple of
-- component-wise @if@s, each of which tries the condition again when it
-- is needed. Otherwise the loop that stopped the condition is reported.
agree :: Loop s -> Thunk s -> Thunk s -> Thunk s -> Eval s (D s)
agree loop cond th el = do
  a <- force th
  b <- force el
  case (a, b) of
    (DTuple as, DTuple bs)
      | length as == length bs ->
          DTuple <$> zipWithM (\x y -> delay Nothing Nothing (select x y)) as bs
    (DBool x, DBool y) | x == y -> pure a
    (DBV w x, DBV w' y) | w == w' && x == y -> pure a
    _ -> failWith (Bottom loop)
  where
    select x y =
      tryBottom (force cond) >>= \case
        Right d -> choose d (force x) (force y)
        Left loop' -> agree loop' cond x y

closure :: Env s -> [Name] -> Expr -> D s
closure env names body = DFun $ \arg -> case names of
  [x] -> eval (Map.insert x arg env) body
  x : xs -> pure (closure (Map.insert x arg env) xs body)
  [] -> eval env body

apply :: D s -> Thunk s -> Eval s (D s)
apply f arg = do
  tick
  case f of
    DFun g -> deeper Nothing (g arg)
    _ -> abort "applied a value that is not a function"

applyAll :: D s -> [Thunk s] -> Eval s (D s)
applyAll = foldM apply

-- | A prim as a curried function of 'primArity' arguments.
primValue :: PrimOp -> D s
primValue op = collect (primArity op) []
  where
    collect k acc = DFun $ \arg ->
      if k <= 1
        then runPrim op (reverse (arg : acc))
        else pure (collect (k - 1) (arg : acc))

-- | A saturated prim application. Combinational prims need the values of
-- all their arguments; signal prims build a node, needing only which
-- nodes their signal arguments are.
runPrim :: PrimOp -> [Thunk s] -> Eval s (D s)
runPrim op args
  | isCombinational op = do
      vs <- traverse (force >=> scalar) args
      either (failWith . Abort) (pure . fromValue) (evalPrim op vs)
  | otherwise = case (op, args) of
      (SigPure, [x]) -> DSig <$> newNode (NPure x)
      (SigLift _, f : ss@(_ : _)) -> do
        ns <- traverse signal ss
        DSig <$> newNode (NLift f ns)
      (SigRegister v, [s]) -> do
        n <- signal s
        st <- liftST (newSTRef (0, Ready (fromValue v)))
        DSig <$> newNode (NRegister st n)
      (SigMealy v, [f, s]) -> do
        n <- signal s
        st <- liftST (newSTRef (0, Ready (fromValue v)))
        memo <- liftST (newSTRef Nothing)
        DSig <$> newNode (NMealy f st n memo)
      _ -> abort (primName op <> " applied to unexpected arguments")
  where
    signal th = force th >>= asNode (primName op <> " argument")
    scalar = \case
      DBool b -> pure (VBool b)
      DBV w x -> pure (VBV w x)
      _ -> abort (primName op <> " applied to a value that is not a Bool or a bit vector")

----------------------------------------------------------------------
-- Core IR: recursive lets

-- | Every binder of a recursive @let@ is computed when it is first
-- needed, in an environment where all of them are bound. A binder of
-- signal type is bound to a placeholder node that stands for the node
-- its expression builds, so the expression can refer to it before that
-- node exists; tuples are bound component by component. Binding each
-- binder costs a step.
letRec :: Env s -> [Bind] -> Eval s (Env s)
letRec env binds = do
  work <- currentCharge
  refs <- traverse (const (tick >> liftST (newSTRef (Pending Nothing unset)))) binds
  let cell b = Lazy . Cell (Just (unName (bindName b))) (Just ("in bind " <> unName (bindName b))) work
      cells = zipWith cell binds refs
  slots <- sequence [recSlot (unName (bindName b)) (bindTy b) c | (b, c) <- zip binds cells]
  let env' = foldr (\(b, s) -> Map.insert (bindName b) s) env (zip binds slots)
  zipWithM_ (\b r -> liftST (writeSTRef r (Pending Nothing (eval env' (bindExpr b))))) binds refs
  pure env'
  where
    unset = abort "internal error: a recursive binder was used before it was defined"

-- | What a recursive binder of the given type is bound to, given the
-- binder's value.
recSlot :: Text -> Ty -> Thunk s -> Eval s (Thunk s)
recSlot name ty value = case ty of
  TSignal _ _ -> do
    target <- delay (Just name) Nothing $ do
      n <- force value >>= asNode name
      DSig <$> case nodeKind n of
        NPlaceholder _ t -> force t >>= asNode name
        _ -> pure n
    Ready . DSig <$> newNode (NPlaceholder name target)
  TProd ts | any carriesSignal ts -> do
    let part i t = delay Nothing Nothing (force value >>= project i >>= force) >>= recSlot name t
    Ready . DTuple <$> zipWithM part [0 ..] ts
  _ -> pure value
  where
    carriesSignal = \case
      TSignal _ _ -> True
      TProd ts -> any carriesSignal ts
      _ -> False

-- | Globals an expression refers to.
globalRefs :: Expr -> Set.Set Name
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
