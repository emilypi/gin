{-# LANGUAGE TemplateHaskell #-}

-- | Evaluate a finite collection of generated memory architectures under
-- named, explicit traffic models. This frontier is modeled, not measured.
module Gin.Evaluate.Memory
  ( MemoryKernel (..)
  , MemoryPortfolio
  , EvaluatedMemory
  , memoryDesigns
  , memoryFrontier
  , evaluatedIdentity
  , evaluatedDesign
  , evaluateMemoryPortfolio
  , encodeMemoryPortfolio

    -- * Optics
  , kernelIdentityL
  , kernelModuleL
  , kernelProxyCostsL
  , evaluatedIdentityL
  , evaluatedDesignL
  , evaluatedKernelL
  , evaluatedRunsL
  , evaluatedCostsL
  , memoryDesignsL
  , memoryFrontierL
  , memoryObjectiveNamesL
  , memoryScenariosL
  , memoryInputDigestL
  ) where

import Control.Lens (view)
import Control.Monad (unless, when)
import Data.Aeson qualified as A
import Data.Aeson.Types ((.=))
import Data.ByteString.Lazy qualified as B
import Data.List (nub)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Encoding qualified as T
import Gin.Core.Bounded (boundedIntValue)
import Gin.Core.Optics (makeFieldLenses)
import Gin.Core.Normal (NModule (..))
import Gin.Core.Type (Ty (..))
import Gin.Error (GinError, Stage (..), ginError)
import Gin.Hash (sha256Hex)
import Gin.Memory
import Numeric.Natural (Natural)

data MemoryKernel = MemoryKernel
  { kernelIdentity :: !Text
  , kernelModule :: !NModule
  , kernelProxyCosts :: ![Natural]
  } deriving stock (Eq, Show)

data EvaluatedMemory = EvaluatedMemory
  { evaluatedIdentity :: !Text
  , evaluatedDesign :: !MemoryDesign
  , evaluatedKernel :: !Text
  , evaluatedRuns :: ![MemoryRun]
  , evaluatedCosts :: ![Natural]
  } deriving stock (Eq, Show)

data MemoryPortfolio = MemoryPortfolio
  { memoryDesigns :: ![EvaluatedMemory]
  , memoryFrontier :: ![Text]
  , memoryObjectiveNames :: ![Text]
  , memoryScenarios :: ![TrafficScenario]
  , memoryInputDigest :: !Text
  } deriving stock (Eq, Show)

evaluateMemoryPortfolio :: [Text] -> [MemoryKernel] -> [MemoryConfig] -> [TrafficScenario] -> [Integer]
  -> Either GinError MemoryPortfolio
evaluateMemoryPortfolio names kernels configs scenarios words_ = do
  unless (not (null names) && length (take 17 names) <= 16 && nub names == names) $
    Left (problem "memory evaluation requires 1 to 16 unique objective names")
  unless (not (null kernels) && length (take 65 kernels) <= 64 && all ((== length names) . length . take 17 . kernelProxyCosts) kernels) $
    Left (problem "memory evaluation requires 1 to 64 kernels with matching objective dimensions")
  unless (nub (map kernelIdentity kernels) == map kernelIdentity kernels) $
    Left (problem "memory kernel identities must be unique")
  unless (not (null configs) && length (take 17 configs) <= 16) $
    Left (problem "memory evaluation requires 1 to 16 configurations")
  unless (not (null scenarios) && length (take 17 scenarios) <= 16 && nub (map trafficName scenarios) == map trafficName scenarios) $
    Left (problem "memory evaluation requires 1 to 16 uniquely named traffic scenarios")
  let inputWords = take 100001 words_
      unique = nub configs
      width nm = sum [toInteger w | (_,TBitVec w) <- nmInputs nm]
      payload = sum (map (width . kernelModule) kernels) * toInteger (length unique)
        * toInteger (length scenarios) * toInteger (length inputWords)
      work = toInteger (length kernels) * sum [toInteger (view boundedIntValue (memoryLanes cfg)) * toInteger (view boundedIntValue (trafficChannels s))
        * toInteger (view boundedIntValue (trafficCycleLimit s)) | cfg <- unique, s <- scenarios]
  when (length inputWords > 100000) (Left (problem "memory input exceeds 100000 words"))
  when (work > 100000000) (Left (problem "memory portfolio exceeds 100000000 lane/channel/cycle work units"))
  when (length kernels * length unique > 128 || payload > 2 ^ (24 :: Int)) $
    Left (problem "memory portfolio exceeds 128 designs or 16777216 modeled word bits; select fewer candidates")
  designs <- traverse (evaluate inputWords) [(kernel,config) | kernel <- kernels, config <- unique]
  let complete d = all ((== Completed) . memoryRunStatus) (evaluatedRuns d)
      completed = filter complete designs
      frontier = [evaluatedIdentity d | d <- completed,
        not (any (\other -> dominates (evaluatedCosts other) (evaluatedCosts d)) completed)]
  pure (MemoryPortfolio designs frontier
    (map ("kernel-proxy/" <>) names <> ["lanes"] <> map (("modeled-cycles/" <>) . trafficName) scenarios)
    scenarios (digest (T.pack (show inputWords))))
  where
    evaluate inputWords (kernel,config) = do
      design <- generateMemoryAccelerator config (kernelModule kernel)
      runs <- traverse (\scenario -> simulateMemory config scenario (kernelModule kernel) inputWords) scenarios
      let identity = digest ("gin-memory/1\n" <> kernelIdentity kernel <> "\n" <> memorySystemVerilog design)
          costs = map (* fromIntegral (view boundedIntValue (memoryLanes config))) (kernelProxyCosts kernel)
            <> [fromIntegral (view boundedIntValue (memoryLanes config))] <> map (fromIntegral . memoryCycles) runs
      pure (EvaluatedMemory identity design (kernelIdentity kernel) runs costs)

dominates :: [Natural] -> [Natural] -> Bool
dominates a b = a /= b && and (zipWith (<=) a b)

encodeMemoryPortfolio :: MemoryPortfolio -> B.ByteString
encodeMemoryPortfolio portfolio = A.encode $ A.object
  [ "format" .= ("gin-memory-portfolio/1" :: Text)
  , "evidence" .= ("deterministic traffic simulation; no physical HBM timing or power measurements" :: Text)
  , "coverage" .= ("nondominated completed designs in the enumerated kernel/configuration set" :: Text)
  , "incompleteRuns" .= ("CycleLimit is inconclusive; excluded from the completed frontier" :: Text)
  , "objectives" .= memoryObjectiveNames portfolio
  , "inputDigest" .= memoryInputDigest portfolio
  , "scenarios" .= map scenarioJ (memoryScenarios portfolio)
  , "frontier" .= memoryFrontier portfolio
  , "designs" .= map designJ (memoryDesigns portfolio)
  ]
  where
    scenarioJ s = A.object
      [ "name" .= trafficName s, "channels" .= trafficChannels s
      , "readLatency" .= trafficReadLatency s, "writeLatency" .= trafficWriteLatency s
      , "acceptEvery" .= trafficAcceptEvery s, "responseEvery" .= trafficResponseEvery s
      , "cycleLimit" .= trafficCycleLimit s ]
    designJ d = A.object
      [ "id" .= evaluatedIdentity d, "kernel" .= evaluatedKernel d
      , "lanes" .= memoryLanes (memoryConfig (evaluatedDesign d))
      , "addressWidth" .= memoryAddressWidth (memoryConfig (evaluatedDesign d))
      , "costs" .= evaluatedCosts d
      , "completed" .= all ((== Completed) . memoryRunStatus) (evaluatedRuns d)
      , "runs" .= zipWith runJ (memoryScenarios portfolio) (evaluatedRuns d) ]
    runJ scenario run = A.object
      [ "scenario" .= trafficName scenario, "status" .= show (memoryRunStatus run)
      , "cycles" .= memoryCycles run, "reads" .= memoryReads run, "writes" .= memoryWrites run
      , "output" .= memoryOutput run ]

digest :: Text -> Text
digest = sha256Hex . T.encodeUtf8

problem :: Text -> GinError
problem = ginError StDriver

-- Optics use the same field-name + L convention as Gin.Core.
makeFieldLenses ''MemoryKernel
makeFieldLenses ''EvaluatedMemory
makeFieldLenses ''MemoryPortfolio
