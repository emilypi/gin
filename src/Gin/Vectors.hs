-- | Cycle-by-cycle test vectors: produced by the Lean exporter from the
-- Lean semantics, consumed by the simulators and HDL testbenches. They
-- are how we answer "does the generated hardware still implement the
-- functionality described by Lean?": the Lean model, the simulators and
-- the HDL runs must agree on them (the core simulator may report an
-- inconclusive @SKIP@).
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
