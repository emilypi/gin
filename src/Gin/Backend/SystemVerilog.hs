-- |
-- Module       : Gin.Backend.SystemVerilog
-- Copyright    : (c) 2026 Emily Pillmore
-- License      : BSD-3-Clause
--
-- Maintainer   : Emily Pillmore <emilypi@cohomolo.gy>
-- Stability    : experimental
-- Portability  : non-portable (GHC extensions)
--
-- SystemVerilog-2017 backend: the Verilog design renderer and
-- testbench generator of "Gin.Backend.Verilog" in the SystemVerilog
-- dialect (@logic@ declarations, @always_ff@ register blocks).
module Gin.Backend.SystemVerilog
  ( systemVerilog
  ) where

import Gin.Backend.Types (Backend (..), Target (..))
import Gin.Backend.Verilog (Dialect (..), renderDesign)
import Gin.Backend.Verilog.Testbench (renderTestbench)

-- | The SystemVerilog backend (files @<modName>.sv@ and
-- @<modName>_tb.sv@).
systemVerilog :: Backend
systemVerilog =
  Backend
    { backendTarget = SystemVerilog
    , backendFileExt = "sv"
    , backendRender = renderDesign SystemVerilog2017
    , backendTestbench = renderTestbench SystemVerilog2017
    }
