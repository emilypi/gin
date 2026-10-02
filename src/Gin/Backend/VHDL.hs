-- | VHDL-2008 backend.
--
-- A netlist becomes one design file holding one entity named after the
-- module, with ports in the order clock, reset, inputs, outputs
-- (@std_logic@ for 'HBit', @unsigned(n-1 downto 0)@ from @ieee.numeric_std@
-- for @'HVec' n@), and one architecture, @gin_rtl@, containing
--
--   * the combinational nets in dependency order, split into unlabeled
--     @process (all)@ blocks of at most 1000 nets; each process computes
--     its nets into variables @gin_v_\<net\>@ and copies those that a
--     register, an output or a later process reads into signals named
--     after the nets,
--   * a signal and an unlabeled clocked process per register: rising edge
--     of the clock, synchronous active-high reset loading the initial value,
--   * one concurrent assignment per output port.
--
-- Combinational logic is computed in variables because its settling time
-- must not depend on the logic depth. With one signal and one concurrent
-- assignment per net, a chain of @d@ nets needs @d@ delta cycles to settle,
-- and nvc stops a run after 10000 delta cycles (@--stop-delta@, which the
-- run command does not raise), so a valid netlist only 10000 nets deep
-- would fail. Variables update immediately, so each process settles its
-- nets in one pass, and since a process reads only inputs, registers and
-- signals of earlier processes, the outputs are stable at most one delta
-- cycle per process, plus a constant, after an input or a register
-- changes. The logic is not put in a single process because nvc 1.23 needs
-- time quadratic in the length of a process to compile it (measured with
-- the run command on a chain of nets: one process of 32000 assignments
-- takes about 40 s and one of 65535 three minutes or more, against a 300 s
-- tool limit; processes of 1000 bring 65535 nets down to about 5 s).
--
-- Operators map onto @numeric_std@ at the operand width: @+@ and @-@ wrap
-- modulo @2^n@; @*@ doubles the width, so products are @resize@d back to
-- @n@; negation is @0 - a@; shifts use @shift_left@ / @shift_right@ (the
-- amount is below the width, so it fits @natural@); comparisons and muxes
-- are conditional variable assignments; zero extension is @resize@; a bit
-- becomes a vector through a one-element aggregate. Every constant operand
-- is qualified (see 'Gin.Backend.VHDL.Testbench.literal').
--
-- The design references no predeclared name outside
-- 'Gin.Netlist.Types.reservedWords', so no net can shadow one, and the only
-- identifiers it introduces are @gin_rtl@ and the @gin_v_@ variables, whose
-- prefix no net may use. Register signals deliberately have no initial
-- value: the testbench must see the reset load it. (Until the first rising
-- edge they are @'U'@, so nvc may print @numeric_std@ metavalue warnings at
-- time 0 on standard error; the protocol never reads standard error.)
--
-- Unread inputs, an unread clock and reset in a register-free module, and
-- partly read vectors need no lint suppressions: nvc's analysis
-- (@nvc --std=2008 -a@) reports none of them.
module Gin.Backend.VHDL
  ( vhdl
  ) where

import Data.Bits (shiftR)
import Data.IntSet qualified as IntSet
import Data.List (intercalate)
import Data.Map.Strict qualified as Map
import Data.Maybe (mapMaybe)
import Data.Set (Set)
import Data.Set qualified as Set
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
    <> ["  " <> declare "signal" signalName n | n <- signals]
    <> ["begin"]
    <> fmap indent (intercalate [""] (filter (not . null) sections))
    <> ["end architecture gin_rtl;"]
  where
    groups = zip [0 :: Int ..] (chunksOf processSize (dependencyOrder assigns))
    assigns = [(n, e) | DAssign n e <- modDecls m]
    groupOf = Map.fromList [(netName n, g) | (g, as) <- groups, (n, _) <- as]
    -- names read through a signal: by a register, an output or another process
    shared =
      Set.fromList $
        [i | ORef i <- [o | DReg _ _ o <- modDecls m] <> fmap outDriver (modOutputs m)]
          <> [ i
             | (g, as) <- groups
             , (_, e) <- as
             , ORef i <- exprOperands e
             , Map.lookup i groupOf /= Just g
             ]
    -- registers, and the combinational nets read through a signal
    signals = [declNet d | d <- modDecls m, isRegister d || netName (declNet d) `Set.member` shared]
    isRegister = \case
      DReg {} -> True
      DAssign {} -> False
    -- the combinational processes, then one block per register, then the outputs
    sections =
      [combinational shared as | (_, as) <- groups]
        <> [process m n r o | DReg n r o <- modDecls m]
        <> [[assign (outNet o) (operand signalName (outDriver o)) | o <- modOutputs m]]
    indent l = if Text.null l then l else "  " <> l

-- | Most combinational nets computed by one process. Bounds both the nvc
-- compile time of a process, which grows quadratically with its length,
-- and the number of processes a change can ripple through: 65536 nets (the
-- 'Gin.Limits.maxNormalBinds' bound on normal forms) make at most 66
-- processes, far below nvc's limit of 10000 delta cycles.
processSize :: Int
processSize = 1000

-- | Consecutive groups of @k@ elements (the last may be shorter), for
-- @k >= 1@.
chunksOf :: Int -> [a] -> [[a]]
chunksOf k xs = case splitAt (max 1 k) xs of
  ([], _) -> []
  (chunk, rest) -> chunk : chunksOf k rest

-- | Append a separator to every element but the last.
punctuate :: Text -> [Text] -> [Text]
punctuate sep = \case
  [] -> []
  [x] -> [x]
  x : xs -> (x <> sep) : punctuate sep xs

assign :: Net -> Text -> Text
assign n rhs = signalName (netName n) <> " <= " <> rhs <> ";"

-- | A signal or variable declaration for a net.
declare :: Text -> (Ident -> Text) -> Net -> Text
declare kind nameOf n = kind <> " " <> nameOf (netName n) <> " : " <> vhdlType (netType n) <> ";"

-- | The signal of an input, a register or a combinational net read through
-- a signal: the net's own name.
signalName :: Ident -> Text
signalName = unIdent

-- | The variable holding a combinational net inside the process computing
-- it.
variableName :: Ident -> Text
variableName i = "gin_v_" <> unIdent i

-- | A process computing the given combinational nets, which are in
-- dependency order. It reads the nets it computes from its own variables,
-- and every other name from a signal: inputs, registers and nets of earlier
-- processes. @process (all)@ makes it sensitive to exactly those signals,
-- and one pass settles every net it computes however deep the logic is.
-- The nets in @shared@ are then copied into their signals.
combinational :: Set Ident -> [(Net, HExpr)] -> [Text]
combinational shared assigns
  | null assigns = []
  | otherwise =
      ["process (all)"]
        <> ["  " <> declare "variable" variableName n | n <- nets]
        <> ["begin"]
        <> ["  " <> variable n <> " := " <> expr ref (netType n) e <> ";" | (n, e) <- assigns]
        <> ["  " <> assign n (variable n) | n <- nets, netName n `Set.member` shared]
        <> ["end process;"]
  where
    nets = fmap fst assigns
    variable = variableName . netName
    local = Set.fromList (fmap netName nets)
    ref i = if i `Set.member` local then variableName i else signalName i

-- | Combinational assignments reordered so that each follows every
-- combinational net it reads, keeping the declaration order wherever the
-- dependencies allow (an already ordered list is unchanged). The result is
-- always a permutation of the argument: the netlist's dependency graph is
-- acyclic, and should it not be, a reference back into a cycle is ignored.
dependencyOrder :: [(Net, HExpr)] -> [(Net, HExpr)]
dependencyOrder assigns = reverse (snd (foldl' visit (IntSet.empty, []) indexed))
  where
    indexed = zip [0 :: Int ..] assigns
    byName = Map.fromList [(netName n, x) | x@(_, (n, _)) <- indexed]
    -- depth first: an assignment is emitted after its dependencies
    visit st@(seen, done) (i, a@(_, e))
      | i `IntSet.member` seen = st
      | otherwise =
          let (seen', done') =
                foldl' visit (IntSet.insert i seen, done) (mapMaybe dependency (exprOperands e))
           in (seen', a : done')
    dependency = \case
      ORef i -> Map.lookup i byName
      OConst _ -> Nothing

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

-- | One register: rising edge, synchronous active-high reset.
process :: Module -> Net -> HLit -> Operand -> [Text]
process m n reset next =
  [ "process (" <> unIdent (modClock m) <> ")"
  , "begin"
  , "  if rising_edge(" <> unIdent (modClock m) <> ") then"
  , "    if " <> unIdent (modReset m) <> " = " <> literal (HLitBit True) <> " then"
  , "      " <> assign n (literal reset)
  , "    else"
  , "      " <> assign n (operand signalName next)
  , "    end if;"
  , "  end if;"
  , "end process;"
  ]

-- | An operand, naming references with the given function.
operand :: (Ident -> Text) -> Operand -> Text
operand ref = \case
  ORef i -> ref i
  OConst l -> literal l

nat :: Natural -> Text
nat = Text.pack . show

call :: Text -> [Text] -> Text
call f args = f <> "(" <> Text.intercalate ", " args <> ")"

-- | The right-hand side for a net of the given type, naming references with
-- the given function.
expr :: (Ident -> Text) -> HwType -> HExpr -> Text
expr ref ty = \case
  HOperand o -> arg o
  HUn UNot o -> "not " <> arg o
  HUn UNeg o -> literal (HLitVec (hwWidth ty) 0) <> " - " <> arg o
  HBin op a b -> binary ty op (arg a) (arg b)
  HMux c t e -> arg t <> " when " <> isHigh c <> " else " <> arg e
  HShl k o -> call "shift_left" [arg o, nat k]
  HLshr k o -> call "shift_right" [arg o, nat k]
  HSlice hi lo o -> slice ref hi lo o
  HConcat a b -> arg a <> " & " <> arg b
  HZext w o -> call "resize" [arg o, nat w]
  HBitToVec o -> "unsigned'(0 => " <> arg o <> ")"
  where
    arg = operand ref
    isHigh c = arg c <> " = " <> literal (HLitBit True)

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

-- | Slices take a net. A slice of a constant (which the netlist builder
-- folds away) is folded here too rather than slicing a qualified literal.
slice :: (Ident -> Text) -> Natural -> Natural -> Operand -> Text
slice ref hi lo = \case
  ORef i -> ref i <> "(" <> nat hi <> " downto " <> nat lo <> ")"
  OConst l -> literal (HLitVec width (value l `shiftR` fromIntegral lo))
  where
    width = fromInteger (max 0 (toInteger hi - toInteger lo + 1))
    value = \case
      HLitBit b -> if b then 1 else 0
      HLitVec _ x -> x
