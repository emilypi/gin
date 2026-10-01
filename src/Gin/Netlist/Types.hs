-- | Target-independent netlist: one operator per net, every net typed.
--
-- FROZEN CONTRACT (c-netlist). Invariants (established by
-- 'Gin.Netlist.Build.buildNetlist', assumed by every backend):
--
--   1. Every 'Ident' satisfies 'isLegalIdent'.
--   2. Net names (inputs, outputs, declared nets, clock, reset) are
--      pairwise distinct, and case-insensitively distinct (VHDL).
--   3. Every 'Operand' reference names an input or a declared net (never
--      an output port, the clock or the reset).
--   4. Expressions are well-typed per the table on 'HExpr'.
--   5. The 'DAssign' dependency graph is acyclic.
--
-- Clocking: every 'DReg' updates on the rising edge of 'modClock'; when
-- 'modReset' is high at that edge it loads its reset value, otherwise
-- its next operand (synchronous, active-high reset, C-3).
module Gin.Netlist.Types
  ( Ident (..)
  , isLegalIdent
  , reservedWords
  , HwType (..)
  , hwWidth
  , Net (..)
  , HLit (..)
  , hlitType
  , Operand (..)
  , UnOp (..)
  , BinOp (..)
  , HExpr (..)
  , Decl (..)
  , declNet
  , Output (..)
  , Module (..)
  , moduleNets
  , operandType
  ) where

import Data.Char (isAsciiLower, isDigit)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as Text
import Numeric.Natural (Natural)

-- | An identifier legal in Verilog-2005, SystemVerilog-2017 and VHDL-2008.
newtype Ident = Ident {unIdent :: Text}
  deriving stock (Show)
  deriving newtype (Eq, Ord)

-- | @[a-z][a-z0-9_]*@, at most 64 characters, no @__@, no trailing @_@,
-- and not a reserved word of any target language.
isLegalIdent :: Text -> Bool
isLegalIdent t = case Text.uncons t of
  Just (c, rest) ->
    isAsciiLower c
      && Text.all (\x -> isAsciiLower x || isDigit x || x == '_') rest
      && Text.length t <= 64
      && not ("__" `Text.isInfixOf` t)
      && not ("_" `Text.isSuffixOf` t)
      && not (t `Set.member` reservedWords)
  Nothing -> False

-- | Union of Verilog-2005, SystemVerilog-2017 and VHDL-2008 reserved
-- words, plus names gin's testbenches use internally.
reservedWords :: Set Text
reservedWords =
  Set.fromList . Text.words $
    -- Verilog-2005 (IEEE 1364-2005 Annex B)
    "always and assign automatic begin buf bufif0 bufif1 case casex casez cell \
    \cmos config deassign default defparam design disable edge else end endcase \
    \endconfig endfunction endgenerate endmodule endprimitive endspecify endtable \
    \endtask event for force forever fork function generate genvar highz0 highz1 \
    \if ifnone incdir include initial inout input instance integer join large \
    \liblist library localparam macromodule medium module nand negedge nmos nor \
    \noshowcancelled not notif0 notif1 or output parameter pmos posedge primitive \
    \pull0 pull1 pulldown pullup pulsestyle_onevent pulsestyle_ondetect rcmos real \
    \realtime reg release repeat rnmos rpmos rtran rtranif0 rtranif1 scalared \
    \showcancelled signed small specify specparam strong0 strong1 supply0 supply1 \
    \table task time tran tranif0 tranif1 tri tri0 tri1 triand trior trireg unsigned \
    \use uwire vectored wait wand weak0 weak1 while wire wor xnor xor "
      -- SystemVerilog-2017 additions (IEEE 1800-2017 Annex B)
      <> "accept_on alias always_comb always_ff always_latch assert assume before bind \
         \bins binsof bit break byte chandle checker class clocking const constraint \
         \context continue cover covergroup coverpoint cross dist do endchecker endclass \
         \endclocking endgroup endinterface endpackage endprogram endproperty endsequence \
         \enum eventually expect export extends extern final first_match foreach forkjoin \
         \global iff ignore_bins illegal_bins implements implies import inside int \
         \interconnect interface intersect join_any join_none let local logic longint \
         \matches modport nettype new nexttime null package packed priority program \
         \property protected pure rand randc randcase randsequence ref reject_on restrict \
         \return s_always s_eventually s_nexttime s_until s_until_with sequence shortint \
         \shortreal soft solve static string strong struct super sync_accept_on \
         \sync_reject_on tagged this throughout timeprecision timeunit type typedef union \
         \unique unique0 until until_with untyped var virtual void wait_order weak \
         \wildcard with within "
      -- VHDL-2008 (IEEE 1076-2008 15.10)
      <> "abs access after alias all architecture array assert assume assume_guarantee \
         \attribute begin block body buffer bus case component configuration constant \
         \context cover default disconnect downto else elsif end entity exit fairness file \
         \for force function generate generic group guarded if impure in inertial inout is \
         \label library linkage literal loop map mod nand new next nor not null of on open \
         \or others out package parameter port postponed procedure process property \
         \protected pure range record register reject release rem report restrict \
         \restrict_guarantee return rol ror select sequence severity shared signal sla sll \
         \sra srl strong subtype then to transport type unaffected units until use \
         \variable vmode vprop vunit wait when while with xnor xor "
      -- VHDL standard library names gin's output imports, and testbench internals
      <> "std ieee std_logic std_logic_vector std_ulogic numeric_std unsigned signed \
         \resize to_unsigned to_integer rising_edge natural integer boolean \
         \gin_tb gin_cycle gin_errors gin_dut"

-- | Hardware types: Bool maps to a single bit, @BitVec n@ to an n-bit vector.
data HwType
  = HBit
  | -- | Width >= 1. Distinct from 'HBit' even at width 1.
    HVec !Natural
  deriving stock (Eq, Ord, Show)

hwWidth :: HwType -> Natural
hwWidth = \case
  HBit -> 1
  HVec n -> n

data Net = Net
  { netName :: !Ident
  , netType :: !HwType
  }
  deriving stock (Eq, Show)

data HLit
  = HLitBit !Bool
  | -- | @HLitVec width value@, @0 <= value < 2^width@.
    HLitVec !Natural !Integer
  deriving stock (Eq, Show)

hlitType :: HLit -> HwType
hlitType = \case
  HLitBit _ -> HBit
  HLitVec w _ -> HVec w

data Operand
  = ORef !Ident
  | OConst !HLit
  deriving stock (Eq, Show)

data UnOp
  = -- | Bitwise / logical not. @HBit -> HBit@ or @HVec n -> HVec n@.
    UNot
  | -- | Two's complement negation. @HVec n -> HVec n@.
    UNeg
  deriving stock (Eq, Ord, Show, Enum, Bounded)

data BinOp
  = -- | Bitwise. Both operands and the result share one type (HBit or HVec n).
    BAnd
  | BOr
  | BXor
  | -- | Modular arithmetic. @HVec n -> HVec n -> HVec n@.
    BAdd
  | BSub
  | BMul
  | -- | Comparison. Operands share one type; result 'HBit'. 'BEq' accepts
    -- HBit operands; 'BUlt' and 'BUle' take HVec operands only.
    BEq
  | BUlt
  | BUle
  deriving stock (Eq, Ord, Show, Enum, Bounded)

-- | One operator per net. Result types:
--
-- > HOperand o          : type of o
-- > HUn op o            : see 'UnOp'
-- > HBin op a b         : see 'BinOp'
-- > HMux c t e          : c is HBit; t and e share the result type
-- > HShl k o, HLshr k o : HVec n -> HVec n
-- > HSlice hi lo o      : HVec n -> HVec (hi - lo + 1), n > hi >= lo
-- > HConcat a b         : HVec x -> HVec y -> HVec (x + y), a is most significant
-- > HZext m o           : HVec n -> HVec m, m >= n
-- > HBitToVec o         : HBit -> HVec 1
data HExpr
  = HOperand !Operand
  | HUn !UnOp !Operand
  | HBin !BinOp !Operand !Operand
  | HMux !Operand !Operand !Operand
  | HShl !Natural !Operand
  | HLshr !Natural !Operand
  | HSlice !Natural !Natural !Operand
  | HConcat !Operand !Operand
  | HZext !Natural !Operand
  | HBitToVec !Operand
  deriving stock (Eq, Show)

data Decl
  = -- | Continuous assignment of a combinational net.
    DAssign !Net !HExpr
  | -- | @DReg net resetValue next@.
    DReg !Net !HLit !Operand
  deriving stock (Eq, Show)

declNet :: Decl -> Net
declNet = \case
  DAssign n _ -> n
  DReg n _ _ -> n

-- | An output port and the operand driving it.
data Output = Output
  { outNet :: !Net
  , outDriver :: !Operand
  }
  deriving stock (Eq, Show)

data Module = Module
  { modName :: !Ident
  , modHeader :: ![Text]
  -- ^ Comment lines (no comment markers) emitted at the top of every
  -- generated file: provenance and the certificate statement.
  , modClock :: !Ident
  , modReset :: !Ident
  , modInputs :: ![Net]
  , modOutputs :: ![Output]
  , modDecls :: ![Decl]
  }
  deriving stock (Eq, Show)

-- | Types of every name an operand may reference: inputs and declared nets.
moduleNets :: Module -> Map Ident HwType
moduleNets m =
  Map.fromList
    [(netName n, netType n) | n <- modInputs m <> fmap declNet (modDecls m)]

operandType :: Module -> Operand -> Maybe HwType
operandType m = \case
  ORef i -> Map.lookup i (moduleNets m)
  OConst l -> Just (hlitType l)
