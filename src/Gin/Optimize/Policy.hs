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
  , validatePolicyAll
  , PolicyIssue (..)
  , PolicyErrors (..)
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
  , policyIssuePathL
  , policyIssueMessageL
  , _PolicyErrors
  ) where

import Control.Lens (view)
import Control.Monad (void)
import Data.Aeson qualified as A
import Data.Aeson.Key qualified as K
import Data.Aeson.KeyMap qualified as KM
import Data.Aeson.Types (Parser, parseEither, (.!=), (.:), (.:?), (.=))
import Data.ByteString.Lazy qualified as B
import Data.Char (isAsciiLower, isAsciiUpper, isDigit)
import Data.List (nub)
import Data.List.NonEmpty (NonEmpty (..))
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as M
import Data.Text (Text)
import Data.Text qualified as T
import Data.Validation (Validation (..), foldValidation)
import Gin.Core.Bounded
import Gin.Core.Json (decodeWith)
import Gin.Core.Optics (makeFieldLenses)
import Gin.Core.Prim (PrimOp (..), primName)
import Gin.Core.Type (Ty (..))
import Gin.Core.Value (valueTy)
import Gin.Error (GinError, Stage (StDecode), ginError)
import Gin.Hash (sha256Hex)
import Gin.Optimize.Circuit (CircuitBackend (..), CircuitCosts (..), CircuitOptions (..))
import Gin.Optimize.Policy.Error
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
mkObjective name def operators weighted =
  policyEither (validateObjectiveAt "objective" (Objective name def operators weighted))

policyError :: Text -> GinError
policyError = ginError StDecode

policyEither :: Validation PolicyErrors a -> Either GinError a
policyEither = foldValidation (Left . policyErrorsToGin) Right

-- Dependent stages short-circuit; sibling checks combine with Applicative.
andThen :: Validation e a -> (a -> Validation e b) -> Validation e b
andThen value next = foldValidation Failure next value

issue :: Text -> Text -> Validation PolicyErrors a
issue path message = Failure (PolicyErrors (PolicyIssue path message :| []))

check :: Text -> Text -> Bool -> Validation PolicyErrors ()
check path message valid = if valid then Success () else issue path message

validateName :: Text -> Text -> Validation PolicyErrors Text
validateName path name = name <$ check path
  "objective name must contain 1 to 64 ASCII letters, digits, underscores or hyphens"
  (not (T.null name) && T.length name <= 64 && T.all nameChar name)
 where
  nameChar c = isAsciiLower c || isAsciiUpper c || isDigit c || c == '_' || c == '-'

validateOperators :: Text -> Map Text CostWeight -> Validation PolicyErrors ()
validateOperators path operators =
  check path "unknown cost operator" (all (`elem` operatorNames) (M.keys operators))

validateObjectiveAt :: Text -> Objective -> Validation PolicyErrors Objective
validateObjectiveAt path objective =
  objective <$ validateName (path <> ".name") (objectiveName objective)
    <* validateOperators (path <> ".operators") (objectiveOperators objective)

-- Inspect only a bounded prefix before traversing a caller-supplied list.
boundedList :: Text -> Int -> [a] -> Validation PolicyErrors [a]
boundedList path lower values =
  values <$ check path message (size >= lower && size <= 16)
 where
  size = length (take 17 values)
  message
    | lower == 1 = "expected between 1 and 16 objectives"
    | otherwise = "at most 16 entries are accepted"

uniqueObjectives :: [Objective] -> Validation PolicyErrors [Objective]
uniqueObjectives values =
  values <$ check "objectives" "objective names must be unique" (nub names == names)
 where
  names = map objectiveName values

validateObjectives :: [Objective] -> Validation PolicyErrors [Objective]
validateObjectives raw = boundedList "objectives" 1 raw `andThen` \values ->
  traverse (uncurry validateObjectiveAt) (zip objectivePaths values)
    <* uniqueObjectives values

objectivePaths :: [Text]
objectivePaths = ["objectives[" <> T.pack (show i) <> "]" | i <- [0 :: Int ..]]

validatePreferences :: [Text] -> Validation PolicyErrors [Text]
validatePreferences raw = boundedList "prefer" 0 raw `andThen` \values ->
  values <$ check "prefer" "preferences must be unique" (nub values == values)

validateBounds :: Maybe [CostWeight] -> Validation PolicyErrors (Maybe [CostWeight])
validateBounds = traverse (boundedList "upperBounds" 0)

validateRelationships ::
  Validation PolicyErrors [Objective] ->
  Validation PolicyErrors [Text] ->
  Validation PolicyErrors (Maybe [CostWeight]) ->
  Validation PolicyErrors ()
validateRelationships objectives preferences bounds = preferenceCheck <* boundsCheck
 where
  preferenceCheck = case (objectives, preferences) of
    (Success os, Success names) ->
      check "prefer" "preferences must name existing objectives"
        (all (`elem` map objectiveName os) names)
    _ -> Success ()
  boundsCheck = case (objectives, bounds) of
    (Success os, Success (Just values)) ->
      check "upperBounds" "upperBounds must match objective dimensions"
        (length values == length os)
    _ -> Success ()

-- | Recheck edits and accumulate independent field and relationship errors.
-- Collection limits gate traversal; failed prerequisites are reported once.
validatePolicyAll :: Policy -> Validation PolicyErrors ()
validatePolicyAll p =
  void objectives <* preferences <* bounds
    <* validateRelationships objectives preferences bounds
 where
  objectives = validateObjectives (policyObjectives p)
  preferences = validatePreferences (policyPreferences p)
  bounds = validateBounds (policyUpperBounds p)

-- | Render every issue through the existing stage-error interface.
validatePolicy :: Policy -> Either GinError ()
validatePolicy = policyEither . validatePolicyAll

decodePolicy :: B.ByteString -> Either GinError Policy
decodePolicy bytes
  | B.length (B.take (65536 + 1) bytes) > 65536 =
      Left (policyError "optimization policy exceeds 65536 bytes")
  | otherwise = do
      value <- decodeWith pure bytes
      policyEither (policyValue value)

-- JSON syntax, duplicate keys and structure are checked before domain fields.
-- Each Parser handles one field; Validation combines independent field errors.
field :: Text -> Parser a -> Validation PolicyErrors a
field path parser =
  either (issue path . T.pack) Success (parseEither (const parser) ())

checkKeys :: Text -> [Text] -> A.Object -> Validation PolicyErrors ()
checkKeys path allowed object =
  check path "unknown policy field" (all ((`elem` allowed) . K.toText) (KM.keys object))

policyValue :: A.Value -> Validation PolicyErrors Policy
policyValue value =
  field "policy" (A.withObject "optimization policy" pure value) `andThen` \o ->
  field "format" (o .: "format") `andThen` \format ->
  check "format" "expected gin-policy/1" (format == ("gin-policy/1" :: Text))
    `andThen` \() -> policyObject o

policyObject :: A.Object -> Validation PolicyErrors Policy
policyObject o =
  Policy <$> objectives <*> preferences <*> seconds <*> backend <*> search <*> bounds
    <* checkKeys "policy"
      [ "format", "objectives", "prefer", "upperBounds", "backend", "search"
      , "timeoutSeconds"
      ] o
    <* validateRelationships objectives preferences bounds
 where
  objectives = field "objectives" (o .: "objectives") `andThen` \raw ->
    boundedList "objectives" 1 raw `andThen` \values ->
      traverse (uncurry objectiveValue) (zip objectivePaths values)
        `andThen` uniqueObjectives
  preferences = field "prefer" (o .:? "prefer") `andThen` \case
    Just names -> validatePreferences names
    Nothing -> Success $ case objectives of
      Success os -> map objectiveName os
      Failure _ -> []
  seconds = field "timeoutSeconds" (o .:? "timeoutSeconds" .!= boundedIntLiteral @60)
  backend = field "backend" (o .:? "backend" .!= "mutable") `andThen` \case
    "mutable" -> Success MutableBackend
    "persistent" -> Success PersistentBackend
    (_ :: Text) -> issue "backend" "unknown backend"
  search = field "search" (o .:? "search" .!= KM.empty) `andThen` searchObject
  bounds = field "upperBounds" (o .:? "upperBounds") `andThen` validateBounds

searchObject :: A.Object -> Validation PolicyErrors PolicySearch
searchObject o =
  PolicySearch
    <$> field "search.iterations" (o .:? "iterations" .!= boundedIntLiteral @8)
    <*> field "search.nodes" (o .:? "nodes" .!= boundedIntLiteral @10000)
    <*> field "search.matches" (o .:? "matches" .!= boundedIntLiteral @10000)
    <*> field "search.expansions" (o .:? "expansions" .!= boundedIntLiteral @10000)
    <*> field "search.archive" (o .:? "archive" .!= boundedIntLiteral @64)
    <*> field "search.witnesses" (o .:? "witnesses" .!= boundedIntLiteral @2)
    <* checkKeys "search"
      ["iterations", "nodes", "matches", "expansions", "archive", "witnesses"] o

objectiveValue :: Text -> A.Value -> Validation PolicyErrors Objective
objectiveValue path value =
  field path (A.withObject "objective" pure value) `andThen` \o ->
    Objective
      <$> (field (path <> ".name") (o .: "name") `andThen` validateName (path <> ".name"))
      <*> field (path <> ".default") (o .:? "default" .!= boundedIntLiteral @1)
      <*> (field (path <> ".operators") (o .:? "operators" .!= M.empty)
        `andThen` \operators ->
          operators <$ validateOperators (path <> ".operators") operators)
      <*> field (path <> ".widthWeighted") (o .:? "widthWeighted" .!= False)
      <* checkKeys path ["name", "default", "operators", "widthWeighted"] o

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
