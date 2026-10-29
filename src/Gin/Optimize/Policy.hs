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
import Control.Monad (forM_, unless, void, when)
import Data.Aeson qualified as A
import Data.Aeson.Key qualified as K
import Data.Aeson.KeyMap qualified as KM
import Data.Aeson.Types (JSONPathElement (..), Parser, (<?>), (.!=), (.:), (.:?), (.=))
import Data.ByteString.Lazy qualified as B
import Data.Char (isAsciiLower, isAsciiUpper, isDigit)
import Data.List (nub)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as M
import Data.Text (Text)
import Data.Text qualified as T
import Data.Vector qualified as V
import Gin.Core.Bounded
import Gin.Core.Json (decodeWith)
import Gin.Core.Optics (makeFieldLenses)
import Gin.Core.Prim (PrimOp (..), primName)
import Gin.Core.Type (Ty (..))
import Gin.Core.Value (valueTy)
import Gin.Error (GinError, Stage (StDecode), ginError, withContext)
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
mkPolicy objectives preferences seconds backend search bounds =
  parsePolicy (Policy objectives preferences seconds backend search bounds)

mkObjective ::
  Text -> CostWeight -> Map Text CostWeight -> Bool -> Either GinError Objective
mkObjective name def operators weighted =
  parseObjectiveAt "objective" (Objective name def operators weighted)

parseObjectiveAt :: Text -> Objective -> Either GinError Objective
parseObjectiveAt path objective = do
  let name = objectiveName objective
  check (path <> ".name")
    "objective name must contain 1 to 64 ASCII letters, digits, underscores or hyphens"
    (not (T.null name) && T.length name <= 64 && T.all nameChar name)
  check (path <> ".operators") "unknown cost operator"
    (all (`elem` operatorNames) (M.keys (objectiveOperators objective)))
  pure objective
 where
  nameChar c = isAsciiLower c || isAsciiUpper c || isDigit c || c == '_' || c == '-'

policyError :: Text -> GinError
policyError = ginError StDecode

check :: Text -> Text -> Bool -> Either GinError ()
check path message valid =
  withContext ("at $." <> path) (unless valid (Left (policyError message)))

-- Inspect only a bounded prefix before traversing a caller-supplied list.
boundedList :: Text -> Int -> [a] -> Either GinError [a]
boundedList path lower values =
  values <$ check path message (size >= lower && size <= 16)
 where
  size = length (take 17 values)
  message
    | lower == 1 = "expected between 1 and 16 objectives"
    | otherwise = "at most 16 entries are accepted"

parsePolicy :: Policy -> Either GinError Policy
parsePolicy p = do
  objectives <- boundedList "objectives" 1 (policyObjectives p)
  preference <- boundedList "prefer" 0 (policyPreferences p)
  bounds <- traverse (boundedList "upperBounds" 0) (policyUpperBounds p)
  forM_ (zip [0 :: Int ..] objectives) $ \(index, objective) ->
    parseObjectiveAt ("objectives[" <> T.pack (show index) <> "]") objective
  let names = map objectiveName objectives
  check "objectives" "objective names must be unique" (nub names == names)
  check "prefer" "preferences must be unique" (nub preference == preference)
  check "prefer" "preferences must name existing objectives"
    (all (`elem` names) preference)
  forM_ bounds $ \values ->
    check "upperBounds" "upperBounds must match objective dimensions"
      (length values == length objectives)
  pure p

-- | Recheck edits through the same smart-construction boundary as JSON input.
-- Stop at the first error, bounding collections before traversing their values.
validatePolicy :: Policy -> Either GinError ()
validatePolicy = void . parsePolicy

decodePolicy :: B.ByteString -> Either GinError Policy
decodePolicy bytes
  | B.length (B.take (65536 + 1) bytes) > 65536 =
      Left (policyError "optimization policy exceeds 65536 bytes")
  | otherwise = decodeWith policyP bytes >>= parsePolicy

-- The shared decoder checks syntax, duplicate keys and numeric resource bounds.
-- Aeson then parses typed fields; smart construction checks their relationships.
policyP :: A.Value -> Parser Policy
policyP = A.withObject "optimization policy" $ \o -> do
  keys
    [ "format", "objectives", "prefer", "upperBounds", "backend", "search"
    , "timeoutSeconds"
    ] o
  format <- o .: "format"
  unless (format == ("gin-policy/1" :: Text)) (fail "expected gin-policy/1")
    <?> Key "format"
  rawObjectives <- o .: "objectives"
  objectives <- A.withArray "objectives" objectivesP rawObjectives <?> Key "objectives"
  preference <- o .:? "prefer" .!= map objectiveName objectives
  seconds <- o .:? "timeoutSeconds" .!= boundedIntLiteral @60
  backend <- o .:? "backend" .!= "mutable"
  chosenBackend <- backendP backend <?> Key "backend"
  rawSearch <- o .:? "search" .!= KM.empty
  search <- searchP rawSearch <?> Key "search"
  bounds <- o .:? "upperBounds"
  pure Policy
    { policyObjectives = objectives
    , policyPreferences = preference
    , policyTimeoutSeconds = seconds
    , policyBackend = chosenBackend
    , policySearch = search
    , policyUpperBounds = bounds
    }
 where
  objectivesP values = do
    when (V.null values || V.length values > 16) $
      fail "expected between 1 and 16 objectives"
    V.toList <$> V.imapM (\i value -> objectiveP value <?> Index i) values
  backendP = \case
    "mutable" -> pure MutableBackend
    "persistent" -> pure PersistentBackend
    (_ :: Text) -> fail "unknown backend"

searchP :: A.Object -> Parser PolicySearch
searchP o = do
  keys ["iterations", "nodes", "matches", "expansions", "archive", "witnesses"] o
  PolicySearch
    <$> o .:? "iterations" .!= boundedIntLiteral @8
    <*> o .:? "nodes" .!= boundedIntLiteral @10000
    <*> o .:? "matches" .!= boundedIntLiteral @10000
    <*> o .:? "expansions" .!= boundedIntLiteral @10000
    <*> o .:? "archive" .!= boundedIntLiteral @64
    <*> o .:? "witnesses" .!= boundedIntLiteral @2

objectiveP :: A.Value -> Parser Objective
objectiveP = A.withObject "objective" $ \o -> do
  keys ["name", "default", "operators", "widthWeighted"] o
  Objective
    <$> o .: "name"
    <*> o .:? "default" .!= boundedIntLiteral @1
    <*> o .:? "operators" .!= M.empty
    <*> o .:? "widthWeighted" .!= False

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
