{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}

-- | Fixed-latency pipelining of combinational kernels. Every output describes
-- the same input frame; initialization/warmup is outside the frame contract.
-- Stateful transition systems remain on the exact-cycle optimization path.
module Gin.Schedule
  ( TimingContract (..)
  , PipelineDepth
  , PipelineCycles
  , mkPipelineDepth
  , Scheduled
  , scheduledModule
  , scheduledLatency
  , scheduledStageDepth
  , scheduledContract
  , pipelineCircuit
  , pipelineVectors

    -- * Optics
  , scheduledModuleL
  , scheduledLatencyL
  , scheduledStageDepthL
  , timedAtomL
  , timedTypeL
  , timedStageL
  , timedDepthL
  , builtL
  , bindCountL
  , reservedL
  , nextNameL
  , delayedL
  , maxDepthL
  , _ExactCycles
  , _FixedLatency
  ) where

import Control.Lens (makePrisms, view)
import Control.Monad (foldM, when)
import Control.Monad.State.Strict (StateT, get, gets, modify', runStateT)
import Control.Monad.Trans.Class (lift)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as M
import Data.Set (Set)
import Data.Set qualified as S
import Data.Text qualified as T
import Gin.Core.Bounded
import Gin.Core.Normal
import Gin.Core.Optics (makeFieldLenses)
import Gin.Core.Syntax (Name (..), Ty (..), Value (..), valueTy)
import Gin.Error (GinError, Stage (..), ginError)
import Gin.Limits (maxNormalBinds, maxVectorBits)
import Gin.Normalize (checkNormal)
import Gin.Sim (simulateNormal)
import Gin.Vectors (Cycle (..), Vectors (..), maxCycles)

-- | After each reset, a fixed-latency output at cycle @t + latency@
-- corresponds to input frame @t@. The first @latency@ cycles are warmup.
-- The pipeline accepts a frame every cycle and cannot be backpressured.
type PipelineDepth = BoundedInt 1 4096

type PipelineCycles = BoundedInt 0 4096

mkPipelineDepth :: Int -> Either GinError PipelineDepth
mkPipelineDepth = either (Left . problem . T.pack) Right . mkBoundedInt

data TimingContract = ExactCycles | FixedLatency !PipelineCycles
  deriving stock (Eq, Show)

data Scheduled = Scheduled
  { scheduledModule :: !NModule
  , scheduledLatency :: !PipelineCycles
  , scheduledStageDepth :: !PipelineCycles
  }
  deriving stock (Eq, Show)

scheduledContract :: Scheduled -> TimingContract
scheduledContract s
  | view boundedIntValue (scheduledLatency s) == 0 = ExactCycles
  | otherwise = FixedLatency (scheduledLatency s)

data Timed = Timed
  { timedAtom :: !Atom
  , timedType :: !Ty
  , timedStage :: !Int
  , timedDepth :: !Int
  }

data Builder = Builder
  { built :: ![NBind]
  , bindCount :: !Int
  , reserved :: !(Set Name)
  , nextName :: !Int
  , delayed :: !(Map (Name, Int) Timed)
  , maxDepth :: !Int
  }

type Build = StateT Builder (Either GinError)

pipelineCircuit :: PipelineDepth -> NModule -> Either GinError Scheduled
pipelineCircuit depthLimit source = do
  let limit = view boundedIntValue depthLimit
  checkNormal source
  when
    (any isState (nmBinds source))
    (Left (problem "fixed-latency pipelining requires a combinational kernel"))
  let names = S.fromList (map fst (nmInputs source) <> map nbName (nmBinds source))
      initial = Builder [] 0 names 0 M.empty 0
      inputs = M.fromList [(n, Timed (AVar n) ty 0 0) | (n, ty) <- nmInputs source]
  ((outputs, latency), state) <-
    runStateT
      ( do
          env <- foldM (scheduleBind limit) inputs (nmBinds source)
          timed <- traverse (atomTime env . noAtom) (nmOutputs source)
          let latency = maximum (0 : map timedStage timed)
          when (latency > 4096) (lift (Left (problem
            "pipeline latency exceeds 4096 cycles")))
          aligned <- traverse (align latency) timed
          pure
            (zipWith (\out (Timed a _ _ _) -> out {noAtom =
              a}) (nmOutputs source) aligned, latency)
      )
      initial
  let result = source {nmBinds = reverse (built state), nmOutputs = outputs}
  checkNormal result
  Scheduled result
    <$> either (Left . problem . T.pack) Right (mkBoundedInt latency)
    <*> either (Left . problem . T.pack) Right (mkBoundedInt (maxDepth state))
 where
  isState b = case nbRhs b of NReg {} -> True; _ -> False

scheduleBind :: Int -> Map Name Timed -> NBind -> Build (Map Name Timed)
scheduleBind limit env bind = do
  let atoms = case nbRhs bind of
        NPrim _ as -> as
        NMux c x y -> [c, x, y]
        NAtom a -> [a]
        NReg {} -> []
  ts <- traverse (atomTime env) atoms
  let baseStage = maximum (0 : map timedStage ts)
  sameStage <- traverse (align baseStage) ts
  let parentDepth = maximum (0 : map timedDepth sameStage)
      stage = baseStage + if parentDepth >= limit then 1 else 0
  aligned <- traverse (align stage) sameStage
  let args = map timedAtom aligned
      depth = 1 + maximum (0 : map timedDepth aligned)
  rhs <- case (nbRhs bind, args) of
    (NPrim op _, as) -> pure (NPrim op as)
    (NMux {}, [c, x, y]) -> pure (NMux c x y)
    (NAtom _, [a]) -> pure (NAtom a)
    _ -> lift (Left (problem "invalid pipeline binding"))
  emit bind {nbRhs = rhs}
  modify' (\s -> s {maxDepth = max depth (maxDepth s)})
  pure (M.insert (nbName bind) (Timed (AVar (nbName bind)) (nbTy bind) stage depth) env)

atomTime :: Map Name Timed -> Atom -> Build Timed
atomTime _ a@(ALit v) = pure (Timed a (valueTy v) 0 0)
atomTime env (AVar name) =
  maybe (lift (Left (problem "missing pipeline dependency"))) pure (M.lookup name env)

align :: Int -> Timed -> Build Timed
align target t
  | stage == target = pure t
  | stage > target = lift (Left (problem "pipeline would move a value backwards in time"))
  | ALit _ <- atom = pure (Timed atom ty target 0)
  | AVar name <- atom = do
      cached <- gets (M.lookup (name, target) . delayed)
      case cached of
        Just value -> pure value
        Nothing -> do
          Timed a _ _ _ <- align (target - 1) t
          fresh <- freshName
          zero <- case ty of
            TBool -> pure (VBool False)
            TBitVec width -> pure (VBV width 0)
            _ -> lift (Left (problem "pipeline encountered a nonscalar type"))
          emit (NBind fresh ty (NReg zero a))
          let result = Timed (AVar fresh) ty target 0
          modify' (\s -> s {delayed = M.insert (name, target) result (delayed s)})
          pure result
 where
  atom = timedAtom t
  ty = timedType t
  stage = timedStage t

freshName :: Build Name
freshName = do
  state <- get
  let name = Name ("gin_pipeline_" <> T.pack (show (nextName state)))
  modify' (\s -> s {nextName = nextName s + 1})
  if name `S.member` reserved state
    then freshName
    else do
      modify' (\s -> s {reserved = S.insert name (reserved s)})
      pure name

emit :: NBind -> Build ()
emit bind = do
  n <- gets bindCount
  when
    (n >= maxNormalBinds)
    (lift (Left (problem "pipeline exceeds normal-form binding limit")))
  modify' (\s -> s {built = bind : built s, bindCount = n + 1})

problem :: T.Text -> GinError
problem = ginError StNormalize

-- | Replay source vectors under the latency contract, adding drain cycles.
-- Warmup outputs are implementation-defined and are sampled only to create
-- a deterministic testbench prefix; all post-warmup expected values come
-- from the supplied source vectors. Validate those vectors against the
-- original program before using this function as evidence.
pipelineVectors :: Scheduled -> Vectors -> Either GinError Vectors
pipelineVectors scheduled vectors = do
  let latency = view boundedIntValue (scheduledLatency scheduled)
      nm = scheduledModule scheduled
      zero TBool = VBool False
      zero (TBitVec w) = VBV w 0
      zero _ = VBool False
      drain = replicate latency (map (zero . snd) (nmInputs nm))
      rows = map cycInputs (vecCycles vectors) <> drain
      width TBool = 1
      width (TBitVec w) = toInteger w
      width _ = 0
      bits =
        sum (map (width . snd) (nmInputs nm)) + sum (map (width . noTy) (nmOutputs nm))
  when (length rows > maxCycles || toInteger (length rows) * bits > maxVectorBits) $
    Left (problem "pipeline vector warmup/drain exceeds vector resource limits")
  prefix <- simulateNormal nm (take latency rows)
  pure
    vectors {vecCycles =
      zipWith Cycle rows (prefix <> map cycOutputs (vecCycles vectors))}

-- Optics use the same field-name + L convention as Gin.Core.
makeFieldLenses ''Scheduled
makeFieldLenses ''Timed
makeFieldLenses ''Builder
makePrisms ''TimingContract
