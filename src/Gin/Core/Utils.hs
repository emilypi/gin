module Gin.Core.Utils 
( showT 
) where

import Data.Text qualified as Text 
import Data.Text (Text)

showT :: Show a => a -> Text 
showT = Text.pack . show

