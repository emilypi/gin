{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE TemplateHaskell #-}

-- | Structured, accumulated policy diagnostics and their CLI rendering.
module Gin.Optimize.Policy.Error
  ( PolicyIssue (..)
  , PolicyErrors (..)
  , policyErrorsToGin
  , policyIssuePathL
  , policyIssueMessageL
  , _PolicyErrors
  ) where

import Control.Lens (Iso', iso)
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NE
import Data.Text (Text)
import Gin.Core.Optics (makeFieldLenses)
import Gin.Error (GinError (..), Stage (StDecode), ginError)

data PolicyIssue = PolicyIssue
  { policyIssuePath :: !Text
  , policyIssueMessage :: !Text
  }
  deriving stock (Eq, Show)

newtype PolicyErrors = PolicyErrors {getPolicyErrors :: NonEmpty PolicyIssue}
  deriving stock (Eq, Show)
  deriving (Semigroup) via NonEmpty PolicyIssue

-- | Retain the compiler's stage error API. Each accumulated issue gets its
-- own context line; 'Gin.Error.renderError' escapes all untrusted text.
policyErrorsToGin :: PolicyErrors -> GinError
policyErrorsToGin (PolicyErrors issues) = case issues of
  issue :| [] ->
    (ginError StDecode (policyIssueMessage issue))
      {errContext = [policyIssuePath issue]}
  _ ->
    (ginError StDecode "invalid optimization policy")
      { errContext =
          [ policyIssuePath issue <> ": " <> policyIssueMessage issue
          | issue <- NE.toList issues
          ]
      }

_PolicyErrors :: Iso' PolicyErrors (NonEmpty PolicyIssue)
_PolicyErrors = iso getPolicyErrors PolicyErrors

makeFieldLenses ''PolicyIssue
