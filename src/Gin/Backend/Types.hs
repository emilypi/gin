-- | The interface every HDL backend implements.
module Gin.Backend.Types
  ( Target (..)
  , targetName
  , parseTarget
  , Backend (..)
  , passMarker
  , failMarker
  , mismatchMarker
  ) where

import Data.Text (Text)
import Gin.Netlist.Types (Module)
import Gin.Vectors (Vectors)

data Target = Verilog | SystemVerilog | VHDL
  deriving stock (Eq, Ord, Show, Enum, Bounded)

-- | CLI spelling.
targetName :: Target -> Text
targetName = \case
  Verilog -> "verilog"
  SystemVerilog -> "systemverilog"
  VHDL -> "vhdl"

parseTarget :: Text -> Maybe Target
parseTarget t = lookup t [(targetName x, x) | x <- [minBound .. maxBound]]

data Backend = Backend
  { backendTarget :: !Target
  , backendFileExt :: !String
  -- ^ Without the dot: @v@, @sv@, @vhd@.
  , backendRender :: Module -> Text
  -- ^ The design file. Defines one module/entity named 'modName'.
  , backendTestbench :: Module -> Vectors -> Text
  -- ^ A self-checking testbench (module/entity @<modName>_tb@) that
  -- instantiates the design, replays the vectors per the testbench
  -- protocol in @docs/semantics.md@, and prints exactly one
  -- 'passMarker' or 'failMarker' line at the end.
  }

-- | Testbench output protocol. The driver only looks for lines
-- containing these markers (simulators may prefix report lines);
-- everything after a marker is informational.
--
-- > GIN-PASS cycles=<n>
-- > GIN-FAIL mismatches=<k>
-- > GIN-MISMATCH cycle=<t> port=<name> expected=<hex> got=<hex>
passMarker, failMarker, mismatchMarker :: Text
passMarker = "GIN-PASS"
failMarker = "GIN-FAIL"
mismatchMarker = "GIN-MISMATCH"
