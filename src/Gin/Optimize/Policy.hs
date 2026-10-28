-- | Bounded, reproducible preferences for structural circuit search.
-- Costs are user-defined proxies, never physical measurements. All coordinates
-- are minimized; preference order chooses a witness after Pareto extraction.
module Gin.Optimize.Policy
  ( Policy
  , Objective
  , objectiveName
  , policyObjectives
  , policyPreferences
  , policyTimeoutSeconds
  , policyOptions
  , policyCosts
  , policyUpperBounds
  , validatePolicy
  , decodePolicy
  , encodePolicy
  , policyDigest
  ) where

import Control.Monad (unless, when)
import Data.Aeson qualified as A
import Data.Aeson.Key qualified as K
import Data.Aeson.KeyMap qualified as KM
import Data.Aeson.Types (Parser, (.:), (.:?), (.!=), (.=))
import Data.ByteString.Lazy qualified as B
import Data.Char (isAsciiLower, isAsciiUpper, isDigit)
import Data.List (nub)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as M
import Data.Text (Text)
import Data.Text qualified as T
import Gin.Core.Json (decodeWith)
import Gin.Core.Prim (PrimOp (..), primName)
import Gin.Core.Type (Ty (..))
import Gin.Core.Value (valueTy)
import Gin.Error (GinError, Stage (..), ginError)
import Gin.Hash (sha256Hex)
import Gin.Optimize.Circuit (CircuitBackend (..), CircuitCosts (..), CircuitOptions (..))
import Numeric.Natural (Natural)
import Yolk qualified as Y

data Objective = Objective
  { objectiveName :: !Text
  , objectiveDefault :: !Natural
  , objectiveOperators :: !(Map Text Natural)
  , objectiveWidthWeighted :: !Bool
  } deriving stock (Eq, Show)

-- | Constructed by the checked parser and revalidated at consumption, since
-- exported selectors also support ordinary Haskell record updates.
data Policy = Policy
  { policyObjectives :: ![Objective]
  , policyPreferences :: ![Text]
  , policyTimeoutSeconds :: !Int
  , policyBackend :: !Text
  , policyLimits :: !Y.Limits
  , policyPareto :: !Y.ParetoOptions
  } deriving stock (Eq, Show)

decodePolicy :: B.ByteString -> Either GinError Policy
decodePolicy bytes
  | B.length (B.take (65536 + 1) bytes) > 65536 =
      Left (ginError StDecode "optimization policy exceeds 65536 bytes")
  | otherwise = decodeWith policyP bytes

-- | Exported record selectors support normal record updates. Recheck at
-- consumption, including consistency with the stored extraction dimensions.
validatePolicy :: Policy -> Either GinError ()
validatePolicy p = do
  unless (length (take 17 (policyObjectives p)) <= 16
       && length (take 17 (policyPreferences p)) <= 16
       && all ((<= 64) . T.length . objectiveName) (policyObjectives p)
       && all ((<= 64) . T.length) (policyPreferences p)) $
    Left (ginError StDecode "optimization policy exceeds objective or name limits")
  reparsed <- decodePolicy (encodePolicy p)
  unless (reparsed == p) $
    Left (ginError StDecode "optimization policy record update is inconsistent with its extraction dimensions")

policyP :: A.Value -> Parser Policy
policyP = A.withObject "optimization policy" $ \o -> do
  keys ["format", "objectives", "prefer", "upperBounds", "backend", "search", "timeoutSeconds"] o
  fmt <- o .: "format"
  unless (fmt == ("gin-policy/1" :: Text)) (fail "expected gin-policy/1")
  os <- o .: "objectives" >>= A.withArray "objectives" (traverse objectiveP . foldr (:) [])
  when (null os || length os > 16) (fail "expected between 1 and 16 objectives")
  let names = map objectiveName os
  unless (nub names == names) (fail "objective names must be unique")
  preference <- o .:? "prefer" .!= names
  unless (nub preference == preference && all (`elem` names) preference) $
    fail "prefer must contain unique objective names from objectives"
  backend <- o .:? "backend" .!= "mutable"
  unless (backend `elem` ["mutable", "persistent"]) (fail "unknown backend")
  seconds <- o .:? "timeoutSeconds" .!= 60 >>= bounded "timeoutSeconds" 1 3600
  bounds <- o .:? "upperBounds"
  case bounds of
    Just bs -> unless (length bs == length os) (fail "upperBounds must match objective dimensions")
    Nothing -> pure ()
  search <- o .:? "search" .!= KM.empty
  keys ["iterations", "nodes", "matches", "expansions", "archive", "witnesses"] search
  iters <- search .:? "iterations" .!= 8 >>= bounded "iterations" 0 1000
  nodes <- search .:? "nodes" .!= 10000 >>= bounded "nodes" 1 100000
  matches <- search .:? "matches" .!= 10000 >>= bounded "matches" 0 100000
  expansions <- search .:? "expansions" .!= 10000 >>= bounded "expansions" 0 10000000
  archive <- search .:? "archive" .!= 64 >>= bounded "archive" 1 4096
  witnesses <- search .:? "witnesses" .!= 2 >>= bounded "witnesses" 1 64
  let pareto = (Y.defaultParetoOptions (length os))
        { Y.paretoUpperBounds = bounds
        , Y.paretoExpansionLimit = Just (fromIntegral expansions)
        , Y.paretoArchiveLimit = archive
        , Y.paretoWitnessLimit = witnesses
        , Y.paretoNodeLimit = 100000
        , Y.paretoRootLimit = 10000
        , Y.paretoCostBitLimit = 64
        }
  pure (Policy os preference seconds backend (Y.Limits iters nodes matches) pareto)

objectiveP :: A.Value -> Parser Objective
objectiveP = A.withObject "objective" $ \o -> do
  keys ["name", "default", "operators", "widthWeighted"] o
  name <- o .: "name"
  unless (not (T.null name) && T.length name <= 64 && T.all nameChar name) $
    fail "objective name must contain 1 to 64 ASCII letters, digits, underscores or hyphens"
  def <- o .:? "default" .!= 1
  operators <- o .:? "operators" .!= M.empty
  unless (all (`elem` operatorNames) (M.keys operators)) (fail "unknown cost operator")
  weighted <- o .:? "widthWeighted" .!= False
  pure (Objective name def operators weighted)
  where
    nameChar c = isAsciiLower c || isAsciiUpper c || isDigit c || c == '_' || c == '-'

keys :: [Text] -> A.Object -> Parser ()
keys allowed o = unless (all ((`elem` allowed) . K.toText) (KM.keys o)) $
  fail "unknown policy field"

bounded :: String -> Int -> Int -> Int -> Parser Int
bounded label lo hi n
  | n >= lo && n <= hi = pure n
  | otherwise = fail (label <> " must be between " <> show lo <> " and " <> show hi)

operatorNames :: [Text]
operatorNames = ["mux", "literal"] <> map primName
  [ BoolAnd, BoolOr, BoolXor, BoolNot, BoolEq, BvAdd, BvSub, BvMul, BvNeg
  , BvAnd, BvOr, BvXor, BvNot, BvShl 0, BvLshr 0, BvEq, BvUlt, BvUle
  , BvConcat, BvExtract 0 0, BvZext 1, BvOfBool ]

policyOptions :: Policy -> CircuitOptions
policyOptions p = CircuitOptions
  { circuitBackend = if policyBackend p == "mutable" then MutableBackend else PersistentBackend
  , circuitSaturationLimits = policyLimits p
  , circuitExtractionOptions = policyPareto p
  }

policyCosts :: Policy -> CircuitCosts
policyCosts p = CircuitCosts
  { circuitPrimitiveCost = \ty op -> costs ty (primName op)
  , circuitMuxCost = (`costs` "mux")
  , circuitLiteralCost = \v -> costs (valueTy v) "literal"
  }
  where
    costs ty op = map (cost ty op) (policyObjectives p)
    cost ty op obj =
      let fallback = if op == "literal" then 0 else objectiveDefault obj
          weight = M.findWithDefault fallback op (objectiveOperators obj)
          width = case ty of TBitVec w -> w; _ -> 1
       in weight * if objectiveWidthWeighted obj then width else 1

policyUpperBounds :: Policy -> Maybe [Natural]
policyUpperBounds = Y.paretoUpperBounds . policyPareto

encodePolicy :: Policy -> B.ByteString
encodePolicy p = A.encode $ A.object
  [ "format" .= ("gin-policy/1" :: Text)
  , "objectives" .= map objectiveJ (policyObjectives p)
  , "prefer" .= policyPreferences p
  , "upperBounds" .= Y.paretoUpperBounds options
  , "backend" .= policyBackend p
  , "timeoutSeconds" .= policyTimeoutSeconds p
  , "search" .= A.object
      [ "iterations" .= Y.iterationLimit limits, "nodes" .= Y.nodeLimit limits
      , "matches" .= Y.matchLimit limits, "expansions" .= Y.paretoExpansionLimit options
      , "archive" .= Y.paretoArchiveLimit options, "witnesses" .= Y.paretoWitnessLimit options ]
  ]
  where
    options = policyPareto p
    limits = policyLimits p
    objectiveJ o = A.object
      [ "name" .= objectiveName o, "default" .= objectiveDefault o
      , "operators" .= objectiveOperators o, "widthWeighted" .= objectiveWidthWeighted o ]

policyDigest :: Policy -> Text
policyDigest = sha256Hex . B.toStrict . encodePolicy
