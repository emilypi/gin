-- | Cycle-by-cycle test vectors: produced by the Lean exporter from the
-- Lean semantics, consumed by the simulators and HDL testbenches.
--
-- The JSON form is specified in @docs/file-formats.md@.
module Gin.Vectors
  ( Vectors (..)
  , Cycle (..)
  , maxCycles
  ) where

import Data.Text (Text)
import Gin.Core.Syntax (Port, Value)

data Vectors = Vectors
  { vecTop :: !Text
  , vecInputs :: ![Port]
  , vecOutputs :: ![Port]
  , vecCycles :: ![Cycle]
  }
  deriving stock (Eq, Show)

-- | One clock cycle: input values applied during the cycle, and output
-- values observed during it (before the next rising edge), each in port
-- order.
data Cycle = Cycle
  { cycInputs :: ![Value]
  , cycOutputs :: ![Value]
  }
  deriving stock (Eq, Show)

-- | Largest vector set gin accepts.
maxCycles :: Int
maxCycles = 100000
