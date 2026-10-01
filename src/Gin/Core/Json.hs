-- | JSON encoding of the core IR (c-ir-json) and test vectors
-- (c-vectors-json). Explicit functions rather than instances, so the
-- frozen types carry no orphan instances.
--
-- Owner: p3.
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
decodeProgram = error "TODO(p3): decodeProgram"

encodeProgram :: Program -> LazyByteString
encodeProgram = error "TODO(p3): encodeProgram"

decodeVectors :: LazyByteString -> Either GinError Vectors
decodeVectors = error "TODO(p3): decodeVectors"

encodeVectors :: Vectors -> LazyByteString
encodeVectors = error "TODO(p3): encodeVectors"
