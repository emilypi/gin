-- | The rule every module generates its lenses with. Record fields keep
-- their names, so code that reads them is unchanged, and each field gets a
-- lens named after it with an @L@ suffix: @defName@ gets @defNameL@.
-- Prisms keep lens's own names (@_EVar@).
module Gin.Core.Optics
  ( makeFieldLenses
  ) where

import Control.Lens (lensField, lensRules, makeLensesWith, mappingNamer, (&), (.~))
import Language.Haskell.TH (DecsQ, Name)

-- | A lens for every field of the record, named after the field with an
-- @L@ suffix. A field that only some constructors have gets a traversal.
makeFieldLenses :: Name -> DecsQ
makeFieldLenses = makeLensesWith (lensRules & lensField .~ mappingNamer (\field -> [field <> "L"]))
