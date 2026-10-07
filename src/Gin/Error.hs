-- | Uniform error type for every compiler stage.
--
-- Every stage function returns @Either GinError a@; stages never throw. I
-- want every failure to say which stage it came from, so the CLI can name
-- where the pipeline stopped.
module Gin.Error
  ( Stage (..)
  , GinError (..)
  , ginError
  , withContext
  , renderError
  , safeLine
  , maxRenderedLine
  , invisible
  ) where

import Data.Char (GeneralCategory (..), generalCategory, ord)
import Data.Text (Text)
import Data.Text qualified as Text
import Numeric (showHex)

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

-- | One-line-per-fact rendering used by the CLI. Messages and context
-- lines may quote untrusted input, so control and format characters (and
-- other characters that would break or disguise a line) are written as
-- @\\u{XXXX}@, and each line is cut to 'maxRenderedLine' characters.
renderError :: GinError -> Text
renderError (GinError stage msg ctx) =
  Text.intercalate "\n" $
    (stageName stage <> " error: " <> safeLine msg) : fmap (("  " <>) . safeLine) ctx
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

-- | Longest rendered line, in characters, before it is cut.
maxRenderedLine :: Int
maxRenderedLine = 4096

-- | Make untrusted text safe to print on one terminal line: escape every
-- character in Unicode categories Cc, Cf, Zl, Zp, Cs, Co and Cn, and cut
-- the result to 'maxRenderedLine' characters.
safeLine :: Text -> Text
safeLine t =
  let escaped = Text.concatMap escape t
   in if Text.length escaped <= maxRenderedLine
        then escaped
        else
          Text.take maxRenderedLine escaped
            <> " ... ("
            <> Text.pack (show (Text.length escaped - maxRenderedLine))
            <> " more characters)"
  where
    escape c
      | invisible c = "\\u{" <> Text.pack (showHex (ord c) "") <> "}"
      | otherwise = Text.singleton c

-- | Characters in the Unicode categories Cc, Cf, Zl, Zp, Cs, Co and Cn: they
-- break lines or hide, reorder or disguise text.
invisible :: Char -> Bool
invisible c =
  generalCategory c
    `elem` [Control, Format, LineSeparator, ParagraphSeparator, Surrogate, PrivateUse, NotAssigned]
