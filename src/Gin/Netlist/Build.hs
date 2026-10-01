-- | Normal form ("Gin.Core.Normal") to netlist ("Gin.Netlist.Types").
module Gin.Netlist.Build
  ( buildNetlist
  , sanitize
  ) where

import Data.Char (isAsciiLower, isAsciiUpper, isDigit, toLower)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as Text
import Gin.Core.Normal (NModule)
import Gin.Error (GinError)
import Gin.Netlist.Types (Module, isLegalIdent, reservedWords)

-- | Precondition: 'Gin.Normalize.checkNormal' succeeded. Errors use
-- 'StNetlist'.
buildNetlist :: NModule -> Either GinError Module
buildNetlist = error "not yet implemented: buildNetlist"

-- | @sanitize taken name@ turns @name@ into a legal identifier
-- ('isLegalIdent') that differs, case-insensitively, from every name in
-- @taken@:
--
--   1. lowercase ASCII letters, keep @[a-z0-9]@ and map every other
--      character to @_@;
--   2. collapse runs of @_@ to one and strip leading and trailing @_@;
--   3. use @n@ if nothing is left; prepend @n_@ if the result does not
--      start with a letter, is a reserved word ('reservedWords'), is @gin@
--      or starts with @gin_@;
--   4. truncate to 56 characters and strip a trailing @_@;
--   5. if the result is taken, append @_k@ for the least @k >= 1@ that
--      gives a free, legal identifier.
--
-- Steps 1–4 make a legal identifier of at most 56 characters, so the
-- suffix of step 5 fits within the 64-character limit while fewer than
-- 9999999 names are taken.
sanitize :: Set Text -> Text -> Text
sanitize taken = freshName (Set.map Text.toLower taken)

-- | 'sanitize' against a set of names that are already lowercase.
freshName :: Set Text -> Text -> Text
freshName taken name
  | base `Set.notMember` taken = base
  | otherwise = suffixed (1 :: Int)
  where
    base = baseName name
    suffixed k
      | candidate `Set.notMember` taken && isLegalIdent candidate = candidate
      | otherwise = suffixed (k + 1)
      where
        candidate = base <> "_" <> Text.pack (show k)

-- | Steps 1–4 of 'sanitize'.
baseName :: Text -> Text
baseName =
  Text.dropWhileEnd (== '_')
    . Text.take 56
    . avoidReserved
    . Text.intercalate "_"
    . filter (not . Text.null)
    . Text.splitOn "_"
    . Text.map legalChar
  where
    legalChar c
      | isAsciiUpper c = toLower c
      | isAsciiLower c || isDigit c = c
      | otherwise = '_'
    avoidReserved t
      | needsPrefix nonEmpty = "n_" <> nonEmpty
      | otherwise = nonEmpty
      where
        nonEmpty = if Text.null t then "n" else t
    needsPrefix t =
      not (startsWithLetter t)
        || t `Set.member` reservedWords
        || t == "gin"
        || "gin_" `Text.isPrefixOf` t
    startsWithLetter = maybe False (isAsciiLower . fst) . Text.uncons
