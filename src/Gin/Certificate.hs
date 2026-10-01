-- | Certificate policy: which axioms a proof may depend on.
module Gin.Certificate
  ( CertPolicy (..)
  , defaultPolicy
  , checkCertificate
  ) where

import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Gin.Core.Syntax (Certificate)
import Gin.Error (GinError)

newtype CertPolicy = CertPolicy
  { allowedAxioms :: Set Text
  }
  deriving stock (Eq, Show)

-- | Lean's three standard axioms. @sorryAx@ is never allowed.
defaultPolicy :: CertPolicy
defaultPolicy = CertPolicy (Set.fromList ["propext", "Classical.choice", "Quot.sound"])

-- | Reject an empty theorem name or statement, any axiom outside the
-- policy in either 'certAxioms' or 'certImplAxioms', and @sorryAx@ even
-- if a caller's policy lists it. Errors use 'StCertificate'.
checkCertificate :: CertPolicy -> Certificate -> Either GinError ()
checkCertificate = error "not yet implemented: checkCertificate"
