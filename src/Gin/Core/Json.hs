-- | JSON encoding of the core IR and test vectors, as specified in
-- @docs/file-formats.md@. Explicit functions rather than instances, so
-- the core types carry no aeson dependency and no orphan instances.
module Gin.Core.Json
  ( decodeProgram
  , encodeProgram
  , decodeVectors
  , encodeVectors
  ) where

import Data.ByteString.Lazy (LazyByteString)
import Gin.Core.Syntax (Program)
import Gin.Error (GinError)
import Gin.Vectors (Vectors)

-- | Decode and structurally validate (format tag, value invariants, width
-- and size bounds). Type checking is 'Gin.Core.Check.checkProgram'.
decodeProgram :: LazyByteString -> Either GinError Program
decodeProgram = error "not yet implemented: decodeProgram"

encodeProgram :: Program -> LazyByteString
encodeProgram = error "not yet implemented: encodeProgram"

decodeVectors :: LazyByteString -> Either GinError Vectors
decodeVectors = error "not yet implemented: decodeVectors"

encodeVectors :: Vectors -> LazyByteString
encodeVectors = error "not yet implemented: encodeVectors"
