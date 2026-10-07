-- | VHDL-2008 backend. Like the Verilog and SystemVerilog backends, it
-- exists so that a simulator can answer the README's third question:
-- does the generated hardware still implement the functionality
-- described by Lean?
--
-- A netlist becomes one design file holding one entity named after the
-- module, with ports in the order clock, reset, inputs, outputs
-- (@std_logic@ for 'HBit', @unsigned(n-1 downto 0)@ from @ieee.numeric_std@
-- for @'HVec' n@), and one architecture, @gin_rtl@, containing
--
--   * the combinational nets in dependency order, split into unlabeled
--     @process (all)@ blocks of at most 'processSize' nets. A net that its
--     own process reads soon after computing it (within the process's
--     'window') is computed into a process variable @gin_v\<k\>@ chosen by
--     its position, and those reads take it from there. A net read by a
--     register, an output, another process or a net of its own process
--     beyond the window, and a net not read at all, is assigned to a signal
--     named after it (a net can be in both),
--   * a signal and an unlabeled clocked process per register: rising edge
--     of the clock, synchronous active-high reset loading the initial value,
--   * one concurrent assignment per output port.
--
-- Two limits of nvc that the run command does not raise shape the
-- combinational processes (see 'processSize' and 'window' for the bounds
-- and measurements):
--
--   * nvc stops a run after 10000 delta cycles at one simulation time
--     (@--stop-delta@). Each read of a net through its signal can cost a
--     delta cycle, so with one signal per net a chain of 10000 nets fails;
--     reading a variable costs none.
--   * nvc keeps the variables of every process for the whole run on its
--     16 MiB simulation heap (@-H@), so one variable per net does not fit
--     wide designs (4100 nets of 4096 bits fill it). Signals live outside
--     that heap.
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
-- identifiers it introduces are @gin_rtl@ and the @gin_v\<k\>@ variables,
-- whose prefix no net may use. I give register signals no initial value
-- on purpose: the testbench must see the reset load it. (Until the first
-- rising edge they are @'U'@, so nvc may print @numeric_std@ metavalue
-- warnings at time 0 on standard error; the protocol never reads standard
-- error.)
--
-- Unread inputs, an unread clock and reset in a register-free module, and
-- partly read vectors need no lint suppressions: nvc's analysis
-- (@nvc --std=2008 -a@) reports none of them.
module Gin.Backend.VHDL
  ( vhdl
  ) where

import Data.Bits (shiftR)
import Data.IntMap.Strict qualified as IntMap
import Data.IntSet qualified as IntSet
import Data.List (intercalate, sortOn)
import Data.Map.Strict qualified as Map
import Data.Maybe (mapMaybe)
import Data.Ord (Down (..))
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
    <> ["  " <> declare "signal" (signalName (netName n)) (netType n) | n <- signals]
    <> ["begin"]
    <> fmap indent (intercalate [""] (filter (not . null) sections))
    <> ["end architecture gin_rtl;"]
  where
    groups = zip [0 :: Int ..] (chunksOf processSize (dependencyOrder assigns))
    assigns = [(n, e) | DAssign n e <- modDecls m]
    groupOf = Map.fromList [(netName n, g) | (g, as) <- groups, (n, _) <- as]
    -- names read through a signal by a register, an output or another process
    external =
      Set.fromList $
        [i | ORef i <- [o | DReg _ _ o <- modDecls m] <> fmap outDriver (modOutputs m)]
          <> [ i
             | (g, as) <- groups
             , (_, e) <- as
             , ORef i <- exprOperands e
             , Map.lookup i groupOf /= Just g
             ]
    -- the elements each process needs to hold every net it computes
    needs = [sum [fromIntegral (hwWidth (netType n)) | (n, _) <- as] | (_, as) <- groups]
    budgets = shareByNeed variableBudget needs
    processes = zipWith (combinational external) budgets (fmap snd groups)
    -- registers, and the combinational nets a process assigns to a signal
    assigned = Set.unions (fmap snd processes)
    signals =
      [declNet d | d <- modDecls m, isRegister d || netName (declNet d) `Set.member` assigned]
    isRegister = \case
      DReg {} -> True
      DAssign {} -> False
    -- the combinational processes, then one block per register, then the outputs
    sections =
      fmap fst processes
        <> [process m n r o | DReg n r o <- modDecls m]
        <> [[assign (netName (outNet o)) (operand signalName (outDriver o)) | o <- modOutputs m]]
    indent l = if Text.null l then l else "  " <> l

-- | Most combinational nets computed by one process. nvc 1.23 needs time
-- quadratic in the length of a process to compile it (measured with the run
-- command on a chain of nets: one process of 32000 assignments takes about
-- 40 s and one of 65535 three minutes or more, against a 300 s tool limit;
-- processes of 1000 bring 65535 nets down to about 5 s).
--
-- Settling bound. Call a read of a combinational net through its signal by
-- another combinational net a signal read, and let @h@ be the largest
-- number of signal reads along any path of combinational nets. After an
-- input or a register changes, every output is stable within @h + 4@ delta
-- cycles, and nvc stops at 10000, so a design simulates whenever
-- @h <= 9996@. (Measured with the run command: a chain of 9997 nets with
-- one signal each, @h = 9996@, passes, and one of 9998 fails. Measured
-- with @--stop-delta@: a design of 4096-bit nets in 17 processes whose
-- longest path makes 140 signal reads, inside and between processes, needs
-- exactly 144.)
--
-- Along a path the positions of the nets in the dependency order increase,
-- so a path enters each process at most once, and within a process of
-- window @d@ it makes a signal read only for a step of at least @d@
-- positions, at most @999 \`div\` d@ times. A netlist of @c@ combinational
-- nets has @P = ceiling (c / 1000)@ processes. Each gets at least the
-- lesser of its need and @variableBudget \`div\` P@ elements
-- ('shareByNeed'), and as no net is wider than 4096 bits
-- ('Gin.Core.Type.maxWidth'), a process's window is its whole length or at
-- least @variableBudget \`div\` P \`div\` 4096@. The largest normal form
-- ('Gin.Limits.maxNormalBinds') has 65536 nets, so @P <= 66@, every window
-- is at least 31, and
--
-- > h <= (P - 1) + (999 `div` 31) * P <= 65 + 32 * 66 = 2177
--
-- whatever the depth, width and shape of the logic.
--
-- Simulation time is not bounded this way: each signal read inside a
-- process runs the whole process again one delta cycle later. Only a
-- process given less than its need makes such reads, and that happens
-- only when the combinational nets of the whole design have more than
-- 'variableBudget' bits: a design whose nets fit reads every net its own
-- process computes from a variable, however its width is spread over the
-- processes. Wider designs whose logic is read beyond the window along long
-- paths can exceed the 300 s tool limit. Measured with the run command: 31
-- interleaved chains of 2113 nets of 4096 bits (65534 nets in 66 processes
-- of window 31, so every chain step is a signal read and the longest path
-- makes 2113) settle within the delta limit but take 400 s to 700 s for 4
-- cycles, depending on the load of the machine; the same shape with 16
-- chains of 8-bit nets reads only variables and takes 4 s.
processSize :: Int
processSize = 1000

-- | Most elements (bits; nvc stores one @std_logic@ per byte) that the
-- variables of all combinational processes hold together: 8 MiB, half of
-- nvc's 16 MiB simulation heap, which keeps every process's variables for
-- the whole run (signals live outside it). The rest is left for the
-- testbench's vector table and the temporaries of operators. The
-- processes share it by need ('shareByNeed'), and a process's share bounds
-- its 'window'. (Measured with the run command, one 4096-bit variable per
-- net: 4001 nets, 16.4 MB of variables, still start; 4100 fail at
-- initialisation with out of memory. A chain of 65535 nets of 4096 bits
-- fills the budget, 66 processes of 31 variables, and passes.)
variableBudget :: Int
variableBudget = 2 ^ (23 :: Int)

-- | Split @total@ elements between processes needing the given numbers,
-- smallest need first: each gets its need or an equal share of what is
-- still left, whichever is less. The shares, in the order of the needs, add
-- up to at most @total@, and each is at least the lesser of its need and
-- @total \`div\` P@ for @P@ processes, as a need below its share leaves
-- more for the rest. When the needs add up to at most @total@, every
-- process gets its need.
--
-- I share by need rather than equally: an equal share for every process
-- would leave a process holding many wide nets a short window even when the
-- other processes need little. Measured with the run command, 2017 nets
-- of 4096 bits next to a chain of 63000 8-bit nets ran 2000 cycles in 63 s
-- with every net in a variable and in 788 s with equal shares, reading most
-- wide nets through their signals.
shareByNeed :: Int -> [Int] -> [Int]
shareByNeed total needs = IntMap.elems (snd (foldl' give (total, IntMap.empty) ordered))
  where
    ordered = zip [length needs, length needs - 1 ..] (sortOn snd (zip [0 ..] needs))
    give (remaining, shares) (left, (i, need)) =
      let share = min need (remaining `div` left)
       in (remaining - share, IntMap.insert i share shares)

-- | The window @d@ of a process given its share @budget@ of
-- 'variableBudget': the largest @d@ such that its @d@ widest nets together
-- have at most @budget@ bits (at least 1, at most the number of nets).
--
-- The net at position @k@ of the process (counting from 0) that the
-- process reads less than @d@ positions after computing it is held in
-- variable @gin_v\<k mod d\>@, which no other net takes before position
-- @k + d@; those readers read the variable, later readers the net's signal.
-- A variable is as wide as the widest net it holds (a narrower vector
-- occupies its low bits, a bit its element 0), and the @d@ variables hold
-- distinct nets, so together they have at most @budget@ elements. A window
-- covering the whole process reads every net it computes from a variable.
window :: Int -> [(Net, HExpr)] -> Int
window budget assigns =
  max 1 (length (takeWhile (<= budget) (scanl1 (+) (sortOn Down widths))))
  where
    widths = [fromIntegral (hwWidth (netType n)) | (n, _) <- assigns] :: [Int]

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

-- | An assignment to a net's signal.
assign :: Ident -> Text -> Text
assign i rhs = signalName i <> " <= " <> rhs <> ";"

-- | A signal or variable declaration.
declare :: Text -> Text -> HwType -> Text
declare kind name ty = kind <> " " <> name <> " : " <> vhdlType ty <> ";"

-- | The signal of an input, a register or a combinational net read through
-- a signal: the net's own name.
signalName :: Ident -> Text
signalName = unIdent

-- | Where a statement finds a net: the signal or variable holding it, and
-- the net's value within that object (the whole object, its low bits or
-- its element 0). Nets are held from element 0, so a slice of a net is the
-- same slice of the object.
data Place = Place
  { placeObject :: !Text
  , placeValue :: !Text
  }

signalPlace :: Ident -> Place
signalPlace i = Place (signalName i) (signalName i)

-- | A process computing the given combinational nets, which are in
-- dependency order, in variables of at most @budget@ elements, and the nets
-- it assigns to their signals: those in @external@, those it reads at
-- least its 'window' after computing them, and those it does not read.
-- Every other net lives only in a variable. @process (all)@ makes the
-- process sensitive to every signal it reads, and every variable read
-- takes the value assigned earlier in the same pass, so no value carries
-- over from an earlier activation.
combinational :: Set Ident -> Int -> [(Net, HExpr)] -> ([Text], Set Ident)
combinational external budget assigns
  | null assigns = ([], Set.empty)
  | otherwise =
      ( ["process (all)"]
          <> ["  " <> declare "variable" (slotName j) ty | (j, ty) <- Map.toList slotTypes]
          <> ["begin"]
          <> ["  " <> l | (k, (n, e)) <- indexed, l <- statements k n e]
          <> ["end process;"]
      , inSignal
      )
  where
    indexed = zip [0 :: Int ..] assigns
    d = window budget assigns
    position = Map.fromList [(netName n, k) | (k, (n, _)) <- indexed]
    types = Map.fromList [(netName n, netType n) | (n, _) <- assigns]
    -- does the net at position k read net i from its variable?
    near k i = case Map.lookup i position of
      Just p -> k > p && k - p < d
      Nothing -> False
    localReads =
      [(k, i) | (k, (_, e)) <- indexed, ORef i <- exprOperands e, i `Map.member` position]
    inSlot = Set.fromList [i | (k, i) <- localReads, near k i]
    inSignal =
      Set.fromList $
        [i | (k, i) <- localReads, not (near k i)]
          <> [ i
             | (n, _) <- assigns
             , let i = netName n
             , i `Set.member` external || i `Set.notMember` inSlot
             ]
    slotTypes =
      Map.fromListWith
        widen
        [(k `mod` d, netType n) | (k, (n, _)) <- indexed, netName n `Set.member` inSlot]
    widen a b
      | a == HBit && b == HBit = HBit
      | otherwise = HVec (max (hwWidth a) (hwWidth b))
    slotName j = "gin_v" <> Text.pack (show j)
    slotPlace i = case (Map.lookup i position, Map.lookup i types) of
      (Just k, Just ty) ->
        let j = k `mod` d
            v = slotName j
         in Place v (within v (Map.findWithDefault ty j slotTypes) ty)
      _ -> signalPlace i
    -- a net of type ty held in variable v of type held
    within v held ty
      | held == ty = v
      | otherwise = case ty of
          HBit -> v <> "(0)"
          HVec w -> v <> "(" <> nat (w - 1) <> " downto 0)"
    statements k n e
      | i `Set.member` inSlot =
          [held <> " := " <> rhs <> ";"] <> [assign i held | i `Set.member` inSignal]
      | otherwise = [assign i rhs]
      where
        i = netName n
        held = placeValue (slotPlace i)
        rhs = expr (\r -> if near k r then slotPlace r else signalPlace r) (netType n) e

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
  , "      " <> assign (netName n) (literal reset)
  , "    else"
  , "      " <> assign (netName n) (operand signalName next)
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

-- | The right-hand side for a net of the given type, finding references
-- with the given function.
expr :: (Ident -> Place) -> HwType -> HExpr -> Text
expr place ty = \case
  HOperand o -> arg o
  HUn UNot o -> "not " <> arg o
  HUn UNeg o -> literal (HLitVec (hwWidth ty) 0) <> " - " <> arg o
  HBin op a b -> binary ty op (arg a) (arg b)
  HMux c t e -> arg t <> " when " <> isHigh c <> " else " <> arg e
  HShl k o -> call "shift_left" [arg o, nat k]
  HLshr k o -> call "shift_right" [arg o, nat k]
  HSlice hi lo o -> slice (placeObject . place) hi lo o
  HConcat a b -> arg a <> " & " <> arg b
  HZext w o -> call "resize" [arg o, nat w]
  HBitToVec o -> "unsigned'(0 => " <> arg o <> ")"
  where
    arg = operand (placeValue . place)
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

-- | Slices take a net, slicing the object holding it (see 'Place'). A
-- slice of a constant (which the netlist builder folds away) is folded here
-- too rather than slicing a qualified literal.
slice :: (Ident -> Text) -> Natural -> Natural -> Operand -> Text
slice object hi lo = \case
  ORef i -> object i <> "(" <> nat hi <> " downto " <> nat lo <> ")"
  OConst l -> literal (HLitVec width (value l `shiftR` fromIntegral lo))
  where
    width = fromInteger (max 0 (toInteger hi - toInteger lo + 1))
    value = \case
      HLitBit b -> if b then 1 else 0
      HLitVec _ x -> x
