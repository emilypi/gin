{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}

-- | Bounded, reproducible preferences for structural circuit search.
-- Costs are user-defined proxies, never physical measurements. All coordinates
-- are minimized; preference order chooses a witness after Pareto extraction.
module Gin.Optimize.Policy
  ( Policy
  , Objective
  , PolicySearch (..)
  , TimeoutSeconds
  , CostWeight
  , defaultPolicySearch
  , mkPolicy
  , mkObjective
  , objectiveName
  , objectiveDefault
  , objectiveOperators
  , objectiveWidthWeighted
  , policyObjectives
  , policyPreferences
  , policyTimeoutSeconds
  , policyBackend
  , policySearch
  , policyOptions
  , policyCosts
  , policyUpperBounds
  , validatePolicy
  , decodePolicy
  , encodePolicy
  , policyDigest

    -- * Optics
  , objectiveNameL
  , objectiveDefaultL
  , objectiveOperatorsL
  , objectiveWidthWeightedL
  , policyObjectivesL
  , policyPreferencesL
  , policyTimeoutSecondsL
  , policyBackendL
  , policySearchL
  , policyUpperBoundsL
  , searchIterationsL
  , searchNodesL
  , searchMatchesL
  , searchExpansionsL
  , searchArchiveL
  , searchWitnessesL
  ) where

import Control.Lens (view)
import Control.Monad (unless, when)
import Data.Aeson qualified as A
import Data.Aeson.Key qualified as K
import Data.Aeson.KeyMap qualified as KM
import Data.Aeson.Types (Parser, (.!=), (.:), (.:?), (.=))
import Data.ByteString.Lazy qualified as B
import Data.Char (isAsciiLower, isAsciiUpper, isDigit)
import Data.List (nub)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as M
import Data.Text (Text)
import Data.Text qualified as T
import Gin.Core.Bounded
import Gin.Core.Json (decodeWith)
import Gin.Core.Optics (makeFieldLenses)
import Gin.Core.Prim (PrimOp (..), primName)
import Gin.Core.Type (Ty (..))
import Gin.Core.Value (valueTy)
import Gin.Error (GinError, Stage (StDecode), ginError)
import Gin.Hash (sha256Hex)
import Gin.Optimize.Circuit (CircuitBackend (..), CircuitCosts (..), CircuitOptions (..))
import Yolk qualified as Y

type TimeoutSeconds = BoundedInt 1 3600
type CostWeight = BoundedInt 0 2147483647

data Objective = Objective
  { objectiveName :: !Text
  , objectiveDefault :: !CostWeight
  , objectiveOperators :: !(Map Text CostWeight)
  , objectiveWidthWeighted :: !Bool
  }
  deriving stock (Eq, Show)

-- | Numeric settings are checked values. Cross-field relationships remain
-- checked at consumption because ordinary record and lens updates are allowed.
data Policy = Policy
  { policyObjectives :: ![Objective]
  , policyPreferences :: ![Text]
  , policyTimeoutSeconds :: !TimeoutSeconds
  , policyBackend :: !CircuitBackend
  , policySearch :: !PolicySearch
  , policyUpperBounds :: !(Maybe [CostWeight])
  }
  deriving stock (Eq, Show)

data PolicySearch = PolicySearch
  { searchIterations :: !(BoundedInt 0 1000)
  , searchNodes :: !(BoundedInt 1 100000)
  , searchMatches :: !(BoundedInt 0 100000)
  , searchExpansions :: !(BoundedInt 0 10000000)
  , searchArchive :: !(BoundedInt 1 4096)
  , searchWitnesses :: !(BoundedInt 1 64)
  }
  deriving stock (Eq, Show)

defaultPolicySearch :: PolicySearch
defaultPolicySearch =
  PolicySearch
    (boundedIntLiteral @8)
    (boundedIntLiteral @10000)
    (boundedIntLiteral @10000)
    (boundedIntLiteral @10000)
    (boundedIntLiteral @64)
    (boundedIntLiteral @2)

mkPolicy ::
  [Objective] ->
  [Text] ->
  TimeoutSeconds ->
  CircuitBackend ->
  PolicySearch ->
  Maybe [CostWeight] ->
  Either GinError Policy
mkPolicy objectives preferences seconds backend search bounds = do
  let result = Policy objectives preferences seconds backend search bounds
  validatePolicy result
  pure result

mkObjective ::
  Text -> CostWeight -> Map Text CostWeight -> Bool -> Either GinError Objective
mkObjective name def operators weighted = do
  validateName name
  unless
    (all (`elem` operatorNames) (M.keys operators))
    (Left (policyError "unknown cost operator"))
  pure (Objective name def operators weighted)

validateName :: Text -> Either GinError ()
validateName name =
  unless
    (not (T.null name) && T.length name <= 64 && T.all nameChar name)
    ( Left
        ( policyError
            "objective name must contain 1 to 64 ASCII letters, digits, underscores or \
              \hyphens"
        )
    )
 where
  nameChar c = isAsciiLower c || isAsciiUpper c || isDigit c || c == '_' || c == '-'

policyError :: Text -> GinError
policyError = ginError StDecode

decodePolicy :: B.ByteString -> Either GinError Policy
decodePolicy bytes
  | B.length (B.take (65536 + 1) bytes) > 65536 =
      Left (policyError "optimization policy exceeds 65536 bytes")
  | otherwise = decodeWith policyP bytes

-- | Recheck relationships after record updates, without a JSON round trip.
-- Individual numeric settings cannot be replaced with unchecked integers.
validatePolicy :: Policy -> Either GinError ()
validatePolicy p = do
  let objectives = policyObjectives p
      names = map objectiveName objectives
      preference = policyPreferences p
  when (null objectives || length (take 17 objectives) > 16) $
    Left (policyError "expected between 1 and 16 objectives")
  unless (length (take 17 preference) <= 16) $
    Left (policyError "at most 16 preferences are accepted")
  mapM_
    ( \o ->
        mkObjective
          (objectiveName o)
          (objectiveDefault o)
          (objectiveOperators o)
          (objectiveWidthWeighted o)
    )
    objectives
  unless (nub names == names) (Left (policyError "objective names must be unique"))
  unless (nub preference == preference && all (`elem` names) preference) $
    Left (policyError "prefer must contain unique objective names from objectives")
  case policyUpperBounds p of
    Just bs ->
      unless (length (take 17 bs) == length objectives) $
        Left (policyError "upperBounds must match objective dimensions and the JSON \
          \number limit")
    Nothing -> pure ()

policyP :: A.Value -> Parser Policy
policyP = A.withObject "optimization policy" $ \o -> do
  keys
    ["format", "objectives", "prefer", "upperBounds", "backend", "search"
      , "timeoutSeconds"]
    o
  fmt <- o .: "format"
  unless (fmt == ("gin-policy/1" :: Text)) (fail "expected gin-policy/1")
  os <-
    o .: "objectives" >>= A.withArray "objectives" (traverse objectiveP . foldr (:) [])
  preference <- o .:? "prefer" .!= map objectiveName os
  backend <- o .:? "backend" .!= "mutable"
  chosenBackend <- case backend :: Text of
    "mutable" -> pure MutableBackend
    "persistent" -> pure PersistentBackend
    _ -> fail "unknown backend"
  seconds <- o .:? "timeoutSeconds" .!= boundedIntLiteral @60
  bounds <- o .:? "upperBounds"
  search <- o .:? "search" .!= KM.empty
  keys ["iterations", "nodes", "matches", "expansions", "archive", "witnesses"] search
  iters <- search .:? "iterations" .!= boundedIntLiteral @8
  nodes <- search .:? "nodes" .!= boundedIntLiteral @10000
  matches <- search .:? "matches" .!= boundedIntLiteral @10000
  expansions <- search .:? "expansions" .!= boundedIntLiteral @10000
  archive <- search .:? "archive" .!= boundedIntLiteral @64
  witnesses <- search .:? "witnesses" .!= boundedIntLiteral @2
  either
    (fail . show)
    pure
    ( mkPolicy
        os
        preference
        seconds
        chosenBackend
        (PolicySearch iters nodes matches expansions archive witnesses)
        bounds
    )

objectiveP :: A.Value -> Parser Objective
objectiveP = A.withObject "objective" $ \o -> do
  keys ["name", "default", "operators", "widthWeighted"] o
  name <- o .: "name"
  def <- o .:? "default" .!= boundedIntLiteral @1
  operators <- o .:? "operators" .!= M.empty
  weighted <- o .:? "widthWeighted" .!= False
  either (fail . show) pure (mkObjective name def operators weighted)

keys :: [Text] -> A.Object -> Parser ()
keys allowed o =
  unless (all ((`elem` allowed) . K.toText) (KM.keys o)) $
    fail "unknown policy field"

operatorNames :: [Text]
operatorNames =
  ["mux", "literal"]
    <> map
      primName
      [ BoolAnd
      , BoolOr
      , BoolXor
      , BoolNot
      , BoolEq
      , BvAdd
      , BvSub
      , BvMul
      , BvNeg
      , BvAnd
      , BvOr
      , BvXor
      , BvNot
      , BvShl 0
      , BvLshr 0
      , BvEq
      , BvUlt
      , BvUle
      , BvConcat
      , BvExtract 0 0
      , BvZext 1
      , BvOfBool
      ]

policyOptions :: Policy -> CircuitOptions
policyOptions p =
  CircuitOptions
    { circuitBackend = policyBackend p
    , circuitSaturationLimits =
        Y.Limits
          (view boundedIntValue (searchIterations search))
          (view boundedIntValue (searchNodes search))
          (view boundedIntValue (searchMatches search))
    , circuitExtractionOptions =
        (Y.defaultParetoOptions (length (policyObjectives p)))
          { Y.paretoUpperBounds =
              fmap (map (fromIntegral . view boundedIntValue)) (policyUpperBounds p)
          , Y.paretoExpansionLimit =
              Just (fromIntegral (view boundedIntValue (searchExpansions search)))
          , Y.paretoArchiveLimit = view boundedIntValue (searchArchive search)
          , Y.paretoWitnessLimit = view boundedIntValue (searchWitnesses search)
          , Y.paretoNodeLimit = 100000
          , Y.paretoRootLimit = 10000
          , Y.paretoCostBitLimit = 64
          }
    }
 where
  search = policySearch p

policyCosts :: Policy -> CircuitCosts
policyCosts p =
  CircuitCosts
    { circuitPrimitiveCost = \ty op -> costs ty (primName op)
    , circuitMuxCost = (`costs` "mux")
    , circuitLiteralCost = \v -> costs (valueTy v) "literal"
    }
 where
  costs ty op = map (cost ty op) (policyObjectives p)
  cost ty op obj =
    let fallback = if op == "literal" then boundedIntLiteral @0 else objectiveDefault obj
        weight = M.findWithDefault fallback op (objectiveOperators obj)
        width = case ty of TBitVec w -> w; _ -> 1
     in fromIntegral (view boundedIntValue weight)
          * if objectiveWidthWeighted obj then width else 1

encodePolicy :: Policy -> B.ByteString
encodePolicy p =
  A.encode $
    A.object
      [ "format" .= ("gin-policy/1" :: Text)
      , "objectives" .= map objectiveJ (policyObjectives p)
      , "prefer" .= policyPreferences p
      , "upperBounds" .= policyUpperBounds p
      , "backend"
          .= ( case policyBackend p of
                MutableBackend -> "mutable" :: Text
                PersistentBackend -> "persistent"
             )
      , "timeoutSeconds" .= policyTimeoutSeconds p
      , "search"
          .= A.object
            [ "iterations" .= searchIterations search
            , "nodes" .= searchNodes search
            , "matches" .= searchMatches search
            , "expansions" .= searchExpansions search
            , "archive" .= searchArchive search
            , "witnesses" .= searchWitnesses search
            ]
      ]
 where
  search = policySearch p
  objectiveJ o =
    A.object
      [ "name" .= objectiveName o
      , "default" .= objectiveDefault o
      , "operators" .= objectiveOperators o
      , "widthWeighted" .= objectiveWidthWeighted o
      ]

policyDigest :: Policy -> Text
policyDigest = sha256Hex . B.toStrict . encodePolicy

-- Optics use the same field-name + L convention as Gin.Core.
makeFieldLenses ''Objective
makeFieldLenses ''Policy
makeFieldLenses ''PolicySearch
