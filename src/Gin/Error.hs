-- | Uniform error type for every compiler stage.
--
-- Every stage function returns @Either GinError a@; stages never throw.
module Gin.Error
  ( Stage (..)
  , GinError (..)
  , ginError
  , withContext
  , renderError
  ) where

import Data.Text (Text)
import Data.Text qualified as Text

-- | The pipeline stage that produced an error.
data Stage
  = StDecode
  | StCheck
  | StCertificate
  | StNormalize
  | StNetlist
  | StBackend
  | StSim
  | StDriver
  deriving stock (Eq, Ord, Show, Enum, Bounded)

data GinError = GinError
  { errStage :: !Stage
  , errMessage :: !Text
  , errContext :: ![Text]
  -- ^ Innermost context first, e.g. @["in bind next", "in def Counter.counter"]@.
  }
  deriving stock (Eq, Show)

ginError :: Stage -> Text -> GinError
ginError stage msg = GinError stage msg []

-- | Push a context line onto an error produced by an inner computation.
withContext :: Text -> Either GinError a -> Either GinError a
withContext ctx = \case
  Left e -> Left e {errContext = errContext e <> [ctx]}
  Right a -> Right a

-- | One-line-per-fact rendering used by the CLI.
renderError :: GinError -> Text
renderError (GinError stage msg ctx) =
  Text.intercalate "\n" $
    (stageName stage <> " error: " <> msg) : fmap ("  " <>) ctx
  where
    stageName = \case
      StDecode -> "decode"
      StCheck -> "type"
      StCertificate -> "certificate"
      StNormalize -> "normalize"
      StNetlist -> "netlist"
      StBackend -> "backend"
      StSim -> "simulation"
      StDriver -> "driver"
