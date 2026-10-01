-- | VHDL-2008 backend.
--
-- A netlist becomes one design file holding one entity named after the
-- module, with ports in the order clock, reset, inputs, outputs
-- (@std_logic@ for 'HBit', @unsigned(n-1 downto 0)@ from @ieee.numeric_std@
-- for @'HVec' n@), and one architecture, @gin_rtl@, containing
--
--   * a signal and a concurrent assignment per combinational net,
--   * a signal and an unlabeled clocked process per register: rising edge
--     of the clock, synchronous active-high reset loading the initial value,
--   * one concurrent assignment per output port.
--
-- Operators map onto @numeric_std@ at the operand width: @+@ and @-@ wrap
-- modulo @2^n@; @*@ doubles the width, so products are @resize@d back to
-- @n@; negation is @0 - a@; shifts use @shift_left@ / @shift_right@ (the
-- amount is below the width, so it fits @natural@); comparisons and muxes
-- are conditional assignments; zero extension is @resize@; a bit becomes a
-- vector through a one-element aggregate. Every constant operand is
-- qualified (see 'Gin.Backend.VHDL.Testbench.literal').
--
-- The design references no predeclared name outside
-- 'Gin.Netlist.Types.reservedWords', so no net can shadow one, and the only
-- identifier it introduces is @gin_rtl@, whose prefix no net may use.
-- Register signals deliberately have no initial value: the testbench must
-- see the reset load it. (Until the first rising edge they are @'U'@, so
-- nvc may print @numeric_std@ metavalue warnings at time 0 on standard
-- error; the protocol never reads standard error.)
--
-- Unread inputs, an unread clock and reset in a register-free module, and
-- partly read vectors need no lint suppressions: nvc's analysis
-- (@nvc --std=2008 -a@) reports none of them.
module Gin.Backend.VHDL
  ( vhdl
  ) where

import Data.Bits (shiftR)
import Data.List (intercalate)
import Data.Text (Text)
import Data.Text qualified as Text
import Gin.Backend.Types (Backend (..), Target (..))
import Gin.Backend.VHDL.Testbench
  ( contextClause
  , headerComments
  , literal
  , renderTestbench
  , vhdlType
  )
import Gin.Netlist.Types
  ( BinOp (..)
  , Decl (..)
  , HExpr (..)
  , HLit (..)
  , HwType (..)
  , Ident (..)
  , Module (..)
  , Net (..)
  , Operand (..)
  , Output (..)
  , UnOp (..)
  , declNet
  , hwWidth
  )
import Numeric.Natural (Natural)

-- | The VHDL-2008 backend: design files @\<modName\>.vhd@ and testbenches
-- @\<modName\>_tb.vhd@ (see "Gin.Backend.VHDL.Testbench"), analysed and run
-- with nvc.
vhdl :: Backend
vhdl =
  Backend
    { backendTarget = VHDL
    , backendFileExt = "vhd"
    , backendRender = renderDesign
    , backendTestbench = renderTestbench
    }

renderDesign :: Module -> Text
renderDesign m =
  Text.unlines $
    headerComments (modHeader m)
      <> contextClause
      <> [""]
      <> entity m
      <> [""]
      <> architecture m

entity :: Module -> [Text]
entity m =
  ["entity " <> modText <> " is", "  port ("]
    <> fmap ("    " <>) (punctuate ";" ports)
    <> ["  );", "end entity " <> modText <> ";"]
  where
    modText = unIdent (modName m)
    ports =
      [port i "in" HBit | i <- [modClock m, modReset m]]
        <> [port (netName n) "in" (netType n) | n <- modInputs m]
        <> [port (netName n) "out" (netType n) | n <- fmap outNet (modOutputs m)]
    port i dir ty = unIdent i <> " : " <> dir <> " " <> vhdlType ty

architecture :: Module -> [Text]
architecture m =
  ["architecture gin_rtl of " <> unIdent (modName m) <> " is"]
    <> ["  signal " <> unIdent (netName n) <> " : " <> vhdlType (netType n) <> ";" | n <- nets]
    <> ["begin"]
    <> fmap indent (intercalate [""] (filter (not . null) sections))
    <> ["end architecture gin_rtl;"]
  where
    nets = fmap declNet (modDecls m)
    -- combinational nets, then one block per register, then the outputs
    sections =
      [[assign n (expr (netType n) e) | DAssign n e <- modDecls m]]
        <> [process m n r o | DReg n r o <- modDecls m]
        <> [[assign (outNet o) (operand (outDriver o)) | o <- modOutputs m]]
    indent l = if Text.null l then l else "  " <> l

-- | Append a separator to every element but the last.
punctuate :: Text -> [Text] -> [Text]
punctuate sep = \case
  [] -> []
  [x] -> [x]
  x : xs -> (x <> sep) : punctuate sep xs

assign :: Net -> Text -> Text
assign n rhs = unIdent (netName n) <> " <= " <> rhs <> ";"

-- | One register: rising edge, synchronous active-high reset.
process :: Module -> Net -> HLit -> Operand -> [Text]
process m n reset next =
  [ "process (" <> unIdent (modClock m) <> ")"
  , "begin"
  , "  if rising_edge(" <> unIdent (modClock m) <> ") then"
  , "    if " <> unIdent (modReset m) <> " = " <> literal (HLitBit True) <> " then"
  , "      " <> assign n (literal reset)
  , "    else"
  , "      " <> assign n (operand next)
  , "    end if;"
  , "  end if;"
  , "end process;"
  ]

operand :: Operand -> Text
operand = \case
  ORef i -> unIdent i
  OConst l -> literal l

nat :: Natural -> Text
nat = Text.pack . show

call :: Text -> [Text] -> Text
call f args = f <> "(" <> Text.intercalate ", " args <> ")"

-- | The right-hand side for a net of the given type.
expr :: HwType -> HExpr -> Text
expr ty = \case
  HOperand o -> operand o
  HUn UNot o -> "not " <> operand o
  HUn UNeg o -> literal (HLitVec (hwWidth ty) 0) <> " - " <> operand o
  HBin op a b -> binary ty op (operand a) (operand b)
  HMux c t e -> operand t <> " when " <> isHigh c <> " else " <> operand e
  HShl k o -> call "shift_left" [operand o, nat k]
  HLshr k o -> call "shift_right" [operand o, nat k]
  HSlice hi lo o -> slice hi lo o
  HConcat a b -> operand a <> " & " <> operand b
  HZext w o -> call "resize" [operand o, nat w]
  HBitToVec o -> "unsigned'(0 => " <> operand o <> ")"
  where
    isHigh c = operand c <> " = " <> literal (HLitBit True)

binary :: HwType -> BinOp -> Text -> Text -> Text
binary ty op a b = case op of
  BAnd -> infixOp "and"
  BOr -> infixOp "or"
  BXor -> infixOp "xor"
  BAdd -> infixOp "+"
  BSub -> infixOp "-"
  BMul -> call "resize" [infixOp "*", nat (hwWidth ty)]
  BEq -> flag (infixOp "=")
  BUlt -> flag (infixOp "<")
  BUle -> flag (infixOp "<=")
  where
    infixOp sym = a <> " " <> sym <> " " <> b
    flag cond = literal (HLitBit True) <> " when " <> cond <> " else " <> literal (HLitBit False)

-- | Slices take a signal. A slice of a constant (which the netlist builder
-- folds away) is folded here too rather than slicing a qualified literal.
slice :: Natural -> Natural -> Operand -> Text
slice hi lo = \case
  ORef i -> unIdent i <> "(" <> nat hi <> " downto " <> nat lo <> ")"
  OConst l -> literal (HLitVec width (value l `shiftR` fromIntegral lo))
  where
    width = fromInteger (max 0 (toInteger hi - toInteger lo + 1))
    value = \case
      HLitBit b -> if b then 1 else 0
      HLitVec _ x -> x
