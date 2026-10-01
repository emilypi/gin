-- | Verilog-2005 backend, and the design renderer it shares with
-- "Gin.Backend.SystemVerilog".
--
-- A design is one module with ports in the order clock, reset, inputs,
-- outputs; one declaration per net; then one statement per netlist
-- declaration: an @assign@ for each combinational net and one clocked
-- block per register, with the synchronous, active-high reset of
-- @docs/semantics.md@; and finally one @assign@ per output.
--
-- Every right-hand side is a single operator over identifiers and sized
-- literals ('literal'), so Verilog's expression-width rules never widen
-- or truncate anything: each net's declared width is its operator's
-- result width, arithmetic wraps at the operand width, and comparisons
-- yield one bit. Shift amounts are sized literals too; a slice of a
-- constant (excluded by the netlist invariants) is folded to a literal,
-- since Verilog cannot slice a literal.
--
-- The output passes @verilator --lint-only -Wall@. The only warnings it
-- would otherwise raise are for signals some bit of which nothing reads:
-- the clock and reset of a register-free module, unread inputs, and
-- signals read only through slices that leave bits out. Exactly those
-- declarations are wrapped in @verilator lint_off UNUSEDSIGNAL@ /
-- @lint_on@ pragmas; nothing is suppressed file-wide.
module Gin.Backend.Verilog
  ( verilog
  , renderDesign
  , Dialect (..)
  ) where

import Data.Bits (shiftR)
import Data.List (sortOn)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (catMaybes, isNothing)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as Text
import Gin.Backend.Types (Backend (..), Target (..))
import Gin.Backend.Verilog.Testbench
  ( Dialect (..)
  , commaSeparated
  , headerComments
  , indent
  , literal
  , renderTestbench
  , showNat
  , sizedHex
  , typeRange
  )
import Gin.Netlist.Types
import Numeric.Natural (Natural)

-- | The Verilog-2005 backend (files @<modName>.v@ and @<modName>_tb.v@).
verilog :: Backend
verilog =
  Backend
    { backendTarget = Verilog
    , backendFileExt = "v"
    , backendRender = renderDesign Verilog2005
    , backendTestbench = renderTestbench Verilog2005
    }

-- | The design file in the given dialect: Verilog-2005 declares @wire@s
-- and @reg@s and uses @always@; SystemVerilog-2017 declares @logic@ and
-- uses @always_ff@.
renderDesign :: Dialect -> Module -> Text
renderDesign dialect m =
  Text.unlines $
    headerComments m
      <> ["module " <> unIdent (modName m) <> " ("]
      <> concat (zipWith suppressIf portIdents (commaSeparated (fmap indent portLines)))
      <> [");"]
      <> section (concatMap declaration (modDecls m))
      <> section (concatMap statement (modDecls m))
      <> section [indent ("assign " <> name n <> " = " <> operand o <> ";") | Output n o <- outs]
      <> ["endmodule"]
  where
    nets = moduleNets m
    unread = notFullyRead m
    name = unIdent . netName
    outs = modOutputs m
    portKeyword = case dialect of
      Verilog2005 -> "wire "
      SystemVerilog2017 -> "logic "
    ports =
      [("input", Net (modClock m) HBit), ("input", Net (modReset m) HBit)]
        <> fmap ("input",) (modInputs m)
        <> [("output", outNet o) | o <- outs]
    portIdents = fmap (netName . snd) ports
    portLines = [dir <> " " <> portKeyword <> typeRange (netType n) <> name n | (dir, n) <- ports]
    declaration d =
      suppressIf (netName n) (indent (keyword <> typeRange (netType n) <> name n <> ";"))
      where
        n = declNet d
        keyword = case (dialect, d) of
          (SystemVerilog2017, _) -> "logic "
          (Verilog2005, DAssign {}) -> "wire "
          (Verilog2005, DReg {}) -> "reg "
    statement = fmap indent . \case
      DAssign n e -> ["assign " <> name n <> " = " <> expression nets e <> ";"]
      DReg n r o ->
        [ always <> " @(posedge " <> unIdent (modClock m) <> ") begin"
        , indent ("if (" <> unIdent (modReset m) <> ") begin")
        , indent (indent (name n <> " <= " <> literal r <> ";"))
        , indent "end else begin"
        , indent (indent (name n <> " <= " <> operand o <> ";"))
        , indent "end"
        , "end"
        ]
    always = case dialect of
      Verilog2005 -> "always"
      SystemVerilog2017 -> "always_ff"
    suppressIf i l
      | i `Set.member` unread =
          [ indent "/* verilator lint_off UNUSEDSIGNAL */"
          , l
          , indent "/* verilator lint_on UNUSEDSIGNAL */"
          ]
      | otherwise = [l]

-- | Precede a non-empty block with a blank line.
section :: [Text] -> [Text]
section = \case
  [] -> []
  ls -> "" : ls

operand :: Operand -> Text
operand = \case
  ORef i -> unIdent i
  OConst l -> literal l

-- | The right-hand side of a continuous assignment.
expression :: Map Ident HwType -> HExpr -> Text
expression nets = \case
  HOperand o -> operand o
  HUn op o -> unOp op <> operand o
  HBin op a b -> operand a <> " " <> binOp op <> " " <> operand b
  HMux c t e -> operand c <> " ? " <> operand t <> " : " <> operand e
  HShl k o -> operand o <> " << " <> amount k
  HLshr k o -> operand o <> " >> " <> amount k
  HSlice hi lo o -> case o of
    ORef i -> unIdent i <> "[" <> showNat hi <> ":" <> showNat lo <> "]"
    OConst l -> sizedHex (minus (hi + 1) lo) (litBits l `shiftR` fromIntegral lo)
  HConcat a b -> "{" <> operand a <> ", " <> operand b <> "}"
  HZext w o -> case operandWidth o of
    Just n | w > n -> "{{" <> showNat (w - n) <> "{1'b0}}, " <> operand o <> "}"
    _ -> operand o
  HBitToVec o -> operand o
  where
    operandWidth = \case
      ORef i -> hwWidth <$> Map.lookup i nets
      OConst l -> Just (hwWidth (hlitType l))
    amount k = sizedHex (bitLength k) (toInteger k)

unOp :: UnOp -> Text
unOp = \case
  UNot -> "~"
  UNeg -> "-"

binOp :: BinOp -> Text
binOp = \case
  BAnd -> "&"
  BOr -> "|"
  BXor -> "^"
  BAdd -> "+"
  BSub -> "-"
  BMul -> "*"
  BEq -> "=="
  BUlt -> "<"
  BUle -> "<="

litBits :: HLit -> Integer
litBits = \case
  HLitBit b -> if b then 1 else 0
  HLitVec _ v -> v

-- | Number of bits needed to write the value, at least one.
bitLength :: Natural -> Natural
bitLength = go 1
  where
    go acc k = if k < 2 then acc else go (acc + 1) (k `div` 2)

-- | Truncated subtraction.
minus :: Natural -> Natural -> Natural
minus a b = if a >= b then a - b else 0

-- | Signals some bit of which no declaration or output reads: the clock
-- and reset when there is no register, and every input or declared net
-- whose reads (whole operands, or bit ranges through slices) leave a
-- bit out.
notFullyRead :: Module -> Set Ident
notFullyRead m =
  Set.fromList $
    [i | not (any isRegister (modDecls m)), i <- [modClock m, modReset m]]
      <> [ netName n
         | n <- modInputs m <> fmap declNet (modDecls m)
         , not (covered (hwWidth (netType n)) (Map.findWithDefault [] (netName n) bitReads))
         ]
  where
    isRegister = \case
      DReg {} -> True
      DAssign {} -> False
    bitReads :: Map Ident [Maybe (Natural, Natural)]
    bitReads =
      Map.fromListWith
        (<>)
        [ (i, [r])
        | (i, r) <- concatMap declReads (modDecls m) <> concatMap (whole . outDriver) (modOutputs m)
        ]
    declReads = \case
      DReg _ _ o -> whole o
      DAssign _ e -> case e of
        HSlice hi lo (ORef i) -> [(i, Just (lo, hi))]
        _ -> concatMap whole (exprOperands e)
    whole = \case
      ORef i -> [(i, Nothing)]
      OConst _ -> []
    covered w rs = any isNothing rs || cover w 0 (sortOn fst (catMaybes rs))
    cover w next = \case
      _ | next >= w -> True
      [] -> False
      (lo, hi) : rest -> lo <= next && cover w (max next (hi + 1)) rest

exprOperands :: HExpr -> [Operand]
exprOperands = \case
  HOperand o -> [o]
  HUn _ o -> [o]
  HBin _ a b -> [a, b]
  HMux c t e -> [c, t, e]
  HShl _ o -> [o]
  HLshr _ o -> [o]
  HSlice _ _ o -> [o]
  HConcat a b -> [a, b]
  HZext _ o -> [o]
  HBitToVec o -> [o]
