-- | Candidate identity, whole-circuit scoring and provenance. Extraction
-- coverage, semantic evidence and physical measurements are independent.
module Gin.Optimize.Portfolio
  ( Portfolio
  , Candidate
  , Metrics (..)
  , buildPortfolio
  , portfolioBaseline
  , portfolioCandidates
  , portfolioSearch
  , portfolioFrontier
  , candidateId
  , candidateModule
  , candidateModuleDigest
  , candidateObjectives
  , candidateMetrics
  , selectCandidate
  , encodePortfolio
  , measureCircuit
  ) where

import Data.Aeson qualified as A
import Data.Aeson.Types ((.=))
import Data.ByteString.Lazy qualified as B
import Data.List (find, sortOn)
import Data.Map.Strict qualified as M
import Data.Maybe (fromMaybe)
import Data.Set qualified as S
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Encoding qualified as T
import Gin.Core.Normal
import Gin.Core.Syntax (Name, Ty (..), Value)
import Gin.Error (GinError, Stage (..), ginError)
import Gin.Hash (sha256Hex)
import Gin.Normalize (checkNormal)
import Gin.Optimize.Circuit
import Gin.Optimize.Policy
import Numeric.Natural (Natural)
import Yolk qualified as Y

data Metrics = Metrics
  { metricOperators :: !Int
  , metricRegisters :: !Int
  , metricRegisterBits :: !Natural
  , metricLogicDepth :: !Int
  } deriving stock (Eq, Show)

data Candidate = Candidate
  { candidateId :: !Text
  , candidateModule :: !NModule
  , candidateObjectives :: ![Natural]
  , candidateExtractionCost :: ![Natural]
  , candidateMetrics :: !Metrics
  } deriving stock (Eq, Show)

data Portfolio = Portfolio
  { portfolioPolicy :: !Policy
  , portfolioBaseline :: !Candidate
  , portfolioCandidates :: ![Candidate]
  , portfolioSearch :: !CircuitResult
  } deriving stock (Eq, Show)

buildPortfolio :: Policy -> NModule -> Either GinError Portfolio
buildPortfolio policy baseline = do
  validatePolicy policy
  checkNormal baseline
  let options = policyOptions policy
      -- Dead-state cleanup can reduce a candidate's final costs. Pruning
      -- with final bounds before cleanup would incorrectly exclude it.
      unbounded = options {circuitExtractionOptions = (circuitExtractionOptions options) {Y.paretoUpperBounds = Nothing}}
  result <- optimizeCircuit unbounded (policyCosts policy) baseline
  let make nm extraction = Candidate
        { candidateId = digest ("gin-candidate/1\n" <> context <> "\n" <> T.pack (show nm))
        , candidateModule = nm
        , candidateObjectives = score policy nm
        , candidateExtractionCost = extraction
        , candidateMetrics = measureCircuit nm
        }
      original = make baseline (score policy baseline)
      candidates = filter feasible . M.elems . M.fromList $
        (candidateId original, original) : [(candidateId c, c) | r <- circuitCandidates result,
           let c = make (optimizedModule r) (extractionCost r)]
  pure (Portfolio policy original candidates result)
  where
    feasible c = maybe True (and . zipWith (<=) (candidateObjectives c)) (policyUpperBounds policy)
    context = T.intercalate "\n"
      [policyDigest policy, circuitRuleSetVersion, digest (T.pack (show baseline))]

-- | Select by the manifest's context-bound digest, or lexicographically by
-- the requested preference order. A feasible baseline is an explicit fallback;
-- its inclusion does not change the reported coverage of Yolk's search.
selectCandidate :: Maybe Text -> Portfolio -> Either GinError Candidate
selectCandidate requested portfolio = case requested of
  Just ident -> maybe (Left (problem "candidate digest is absent from this source/policy portfolio")) Right $
    find ((== ident) . candidateId) (portfolioCandidates portfolio)
  Nothing -> case sortOn rank (portfolioCandidates portfolio) of
    [] -> Left (problem "no feasible candidate found; inspect coverage and feasibility in the portfolio")
    x : _ -> Right x
  where
    policy = portfolioPolicy portfolio
    names = map objectiveName (policyObjectives policy)
    order = policyPreferences policy <> filter (`notElem` policyPreferences policy) names
    rank c = (map (\n -> fromMaybe 0 (lookup n (zip names (candidateObjectives c)))) order, candidateId c)

-- | Nondominated final vectors among the feasible evaluated candidates,
-- including the baseline. This is not global final-circuit completeness.
portfolioFrontier :: Portfolio -> [Text]
portfolioFrontier p = [candidateId c | c <- portfolioCandidates p,
  not (any (\d -> let a = candidateObjectives d; b = candidateObjectives c
                  in a /= b && and (zipWith (<=) a b)) (portfolioCandidates p))]

-- | Final graph metrics after cleanup; register inputs start at depth zero.
-- This is logic-level depth, not a timing estimate or a frequency claim.
measureCircuit :: NModule -> Metrics
measureCircuit nm = Metrics ops regs bits depth
  where
    (ops, regs, bits, depths) = foldl' step (0, 0, 0, M.empty) (nmBinds nm)
    depth = maximum (0 : map (atomDepth depths . noAtom) (nmOutputs nm)
      <> [atomDepth depths a | NBind _ _ (NReg _ a) <- nmBinds nm])
    step (o, r, b, ds) bind =
      let (newOps, newRegs, newBits, d) = case nbRhs bind of
            NPrim _ as -> (1, 0, 0, 1 + maximum (0 : map (atomDepth ds) as))
            NMux c x y -> (1, 0, 0, 1 + maximum (map (atomDepth ds) [c,x,y]))
            NReg _ _ -> (0, 1, width (nbTy bind), 0)
            NAtom a -> (0, 0, 0, atomDepth ds a)
       in (o + newOps, r + newRegs, b + newBits, M.insert (nbName bind) d ds)
    width (TBitVec w) = w
    width _ = 1

atomDepth :: M.Map Name Int -> Atom -> Int
atomDepth ds (AVar n) = M.findWithDefault 0 n ds
atomDepth _ (ALit _) = 0

score :: Policy -> NModule -> [Natural]
score p nm = foldl' (zipWith (+)) zero (operatorCosts <> literalCosts)
  where
    zero = replicate (length (policyObjectives p)) 0
    weights = policyCosts p
    operatorCosts = [case nbRhs b of
        NPrim op _ -> circuitPrimitiveCost weights (nbTy b) op
        NMux {} -> circuitMuxCost weights (nbTy b)
        _ -> zero | b <- nmBinds nm]
    literalCosts = map (circuitLiteralCost weights) . S.toList . S.fromList $
      concatMap (rhsLiterals . nbRhs) (nmBinds nm) <> concatMap (atomLiterals . noAtom) (nmOutputs nm)

rhsLiterals :: NRhs -> [Value]
rhsLiterals = concatMap atomLiterals . \case
  NPrim _ as -> as
  NMux c x y -> [c,x,y]
  NReg _ a -> [a]
  NAtom a -> [a]

atomLiterals :: Atom -> [Value]
atomLiterals (ALit v) = [v]
atomLiterals _ = []

encodePortfolio :: Portfolio -> B.ByteString
encodePortfolio p = A.encode $ A.object
  [ "format" .= ("gin-portfolio/1" :: Text)
  , "policyDigest" .= policyDigest (portfolioPolicy p)
  , "ruleSet" .= circuitRuleSetVersion
  , "timingContract" .= ("exact-cycle" :: Text)
  , "objectives" .= map objectiveName (policyObjectives (portfolioPolicy p))
  , "upperBounds" .= policyUpperBounds (portfolioPolicy p)
  , "finalFeasibility" .= (if null (portfolioCandidates p) then "NoFeasibleCandidateInPortfolio" else "FeasibleFound" :: Text)
  , "finalFrontier" .= portfolioFrontier p
  , "costEvidence" .= ("user-defined structural proxies; not physical measurements" :: Text)
  , "semanticEvidence" .= ("typed built-in rewrites; independent equivalence replay not yet run" :: Text)
  , "physicalEvaluation" .= ("unavailable: no target or toolchain configured" :: Text)
  , "coverageScope" .= ("nondominated extraction vectors in the frozen e-graph, one representative per e-class" :: Text)
  , "saturation" .= A.object
      [ "stopReason" .= show (Y.stopReason run), "iterations" .= Y.iterations run
      , "applications" .= Y.applications run, "nodes" .= Y.finalNodes run ]
  , "extraction" .= A.object
      [ "coverage" .= show (circuitCoverage result)
      , "feasibility" .= show (circuitFeasibility result)
      , "termination" .= show (circuitTermination result)
      , "expansions" .= circuitExpansions result
      , "pendingBounds" .= circuitPendingBounds result
      , "witnessesComplete" .= circuitWitnessesComplete result ]
  , "baseline" .= candidateJ (portfolioBaseline p)
  , "candidates" .= map candidateJ (portfolioCandidates p)
  ]
  where
    result = portfolioSearch p
    run = circuitRunResult result
    candidateJ c = A.object
      [ "id" .= candidateId c, "moduleDigest" .= candidateModuleDigest c, "objectives" .= candidateObjectives c
      , "origin" .= (if candidateId c == candidateId (portfolioBaseline p) then "baseline" else "extracted" :: Text)
      , "extractionCost" .= candidateExtractionCost c
      , "metrics" .= metricsJ (candidateMetrics c) ]
    metricsJ m = A.object
      [ "operators" .= metricOperators m, "registers" .= metricRegisters m
      , "registerBits" .= metricRegisterBits m, "logicDepth" .= metricLogicDepth m ]

digest :: Text -> Text
digest = sha256Hex . T.encodeUtf8

candidateModuleDigest :: Candidate -> Text
candidateModuleDigest = digest . T.pack . show . candidateModule

problem :: Text -> GinError
problem = ginError StNormalize
