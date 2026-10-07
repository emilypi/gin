-- | Helpers every stage shares: failing with a stage's error, adding
-- context to one, and the text functions that build messages and HDL. I
-- keep one definition of each here, so every stage words, quotes and
-- escapes things the same way.
module Gin.Core.Utils
  ( -- * Errors
    failAt
  , withContextM

    -- * Messages
  , showT
  , quote
  , invisible
  , replaceInvisible

    -- * Layout
  , punctuate
  , hexDigits
  ) where

import Control.Monad.Except (MonadError, catchError, liftEither, throwError)
import Data.Text (Text)
import Data.Text qualified as Text
import Gin.Error (GinError, Stage, ginError, invisible, withContext)
import Numeric (showHex)
import Numeric.Natural (Natural)

----------------------------------------------------------------------
-- Errors

-- | Fail with an error from the given stage, without context. Works in
-- @Either GinError@ and in every monad stacked on it.
failAt :: (MonadError GinError m) => Stage -> Text -> m a
failAt stage = throwError . ginError stage

-- | 'withContext' for any monad that can fail with a 'GinError'.
withContextM :: (MonadError GinError m) => Text -> m a -> m a
withContextM ctx m = m `catchError` (liftEither . withContext ctx . Left)

----------------------------------------------------------------------
-- Messages

showT :: (Show a) => a -> Text
showT = Text.pack . show

-- | Quote and escape a name from the IR for an error message.
quote :: Text -> Text
quote = showT

-- | Replace every 'invisible' character with the given one.
replaceInvisible :: Char -> Text -> Text
replaceInvisible r = Text.map (\c -> if invisible c then r else c)

----------------------------------------------------------------------
-- Layout

-- | Append a separator to every element but the last.
punctuate :: Text -> [Text] -> [Text]
punctuate sep = \case
  [] -> []
  [x] -> [x]
  x : xs -> (x <> sep) : punctuate sep xs

-- | Lowercase hex of @v mod 2^w@, zero-padded to @ceil(w/4)@ digits (at
-- least one).
hexDigits :: Natural -> Integer -> Text
hexDigits w v = Text.justifyRight digits '0' (Text.pack (showHex (v `mod` (2 ^ w)) ""))
  where
    digits = max 1 (fromIntegral ((w + 3) `div` 4))
