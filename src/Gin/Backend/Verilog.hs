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
-- Verilator @-Wall@ rejects four comparison forms over an n-bit @x@,
-- unless both operands are literals: UNSIGNED for @0 <= x@ and @x < 0@,
-- CMPCONST for @x <= 2^n-1@ and @2^n-1 < x@. Comparisons are handled in
-- two steps:
--
-- * A comparison in one of those forms with a literal zero or all ones
--   is printed as its one-bit result, and its other operand is not read
--   there ('printedExpr').
--
-- * Verilator also propagates constants through continuous assignments
--   (a net assigned a literal, @b & 0@, @a ^ a@, a folded comparison
--   widened and negated, and so on), so a net can supply the zero or the
--   all ones as well. Rather than predict which nets it proves constant,
--   I wrap every comparison still printed as one in
--   @verilator lint_off UNSIGNED@ and @lint_off CMPCONST@ pragmas, closed
--   by the matching @lint_on@ right after its @assign@
--   ('comparisonPragmas').
--
-- The output passes @verilator --lint-only -Wall@ (Verilator 5.052).
-- Besides those comparison warnings, the only warnings it would raise
-- are for signals some bit of which nothing reads: the clock and reset
-- of a register-free module, unread inputs, signals read only by folded
-- comparisons, and signals read only through slices that leave bits
-- out. Exactly those declarations are wrapped in
-- @verilator lint_off UNUSEDSIGNAL@ / @lint_on@ pragmas. Every
-- suppression covers one declaration or one statement; nothing is
-- suppressed file-wide. I measured, rather than derived, that constants
-- propagated into any operator other than a comparison raise no warning:
-- the test suite lints nets holding 0, 1 and all ones fed into every
-- operator at widths 1, 8 and 4096.
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
  , headerComments
  , indent
  , literal
  , renderTestbench
  , sizedHex
  , typeRange
  )
import Gin.Core.Utils (punctuate, showT)
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
      <> concat (zipWith suppressIf portIdents (punctuate "," (fmap indent portLines)))
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
      DAssign n e ->
        let printed = printedExpr e
         in comparisonPragmas
              printed
              ["assign " <> name n <> " = " <> expression nets printed <> ";"]
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

-- | The expression a continuous assignment prints, and whose operands
-- count as read: a comparison its constant operand decides becomes its
-- one-bit result (see the module header); every other expression is
-- unchanged.
printedExpr :: HExpr -> HExpr
printedExpr = \case
  HBin BUle (OConst l) _ | isZero l -> decided True
  HBin BUlt _ (OConst l) | isZero l -> decided False
  HBin BUle _ (OConst l) | isAllOnes l -> decided True
  HBin BUlt (OConst l) _ | isAllOnes l -> decided False
  e -> e
  where
    decided = HOperand . OConst . HLitBit
    -- The value 'literal' prints, which is reduced modulo 2^width.
    value l = litBits l `mod` (2 ^ width l)
    width = hwWidth . hlitType
    isZero l = value l == 0
    isAllOnes l = value l == 2 ^ width l - 1

-- | Wrap the statement printing the given expression, when that is an
-- unsigned comparison, in pragmas turning off Verilator's warnings for a
-- comparison it decides at compile time (see the module header). The
-- pragmas cover only that statement; every other one is unchanged.
comparisonPragmas :: HExpr -> [Text] -> [Text]
comparisonPragmas e ls = case e of
  HBin op _ _ | op `elem` [BUlt, BUle] -> fmap (pragma "off") codes <> ls <> fmap (pragma "on") back
  _ -> ls
  where
    codes = ["UNSIGNED", "CMPCONST"]
    back = reverse codes
    pragma onOff code = "/* verilator lint_" <> onOff <> " " <> code <> " */"

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
    ORef i -> unIdent i <> "[" <> showT hi <> ":" <> showT lo <> "]"
    OConst l -> sizedHex (minus (hi + 1) lo) (litBits l `shiftR` fromIntegral lo)
  HConcat a b -> "{" <> operand a <> ", " <> operand b <> "}"
  HZext w o -> case operandWidth o of
    Just n | w > n -> "{{" <> showT (w - n) <> "{1'b0}}, " <> operand o <> "}"
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
-- whose reads in the printed design (whole operands, or bit ranges
-- through slices; none in a folded comparison, see 'printedExpr') leave
-- a bit out.
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
      DAssign _ e -> case printedExpr e of
        HSlice hi lo (ORef i) -> [(i, Just (lo, hi))]
        printed -> concatMap whole (exprOperands printed)
    whole = \case
      ORef i -> [(i, Nothing)]
      OConst _ -> []
    covered w rs = any isNothing rs || cover w 0 (sortOn fst (catMaybes rs))
    cover w next = \case
      _ | next >= w -> True
      [] -> False
      (lo, hi) : rest -> lo <= next && cover w (max next (hi + 1)) rest
