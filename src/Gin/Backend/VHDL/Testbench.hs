-- | VHDL-2008 testbench generation, and the pieces of VHDL syntax that the
-- design renderer in "Gin.Backend.VHDL" shares with it.
--
-- The testbench is table-driven: a record type with one field per input and
-- output port, a constant array of those records holding every cycle, and a
-- single loop that follows the testbench protocol of @docs/semantics.md@.
-- I avoid straight-line stimulus on purpose: nvc 1.23 cannot elaborate it
-- past roughly 2000 cycles, while a 25000-row table runs in well under a
-- second.
--
-- Protocol lines are written to standard output with @std.textio@
-- (@write@, then @writeline(output, …)@). They are never carried by
-- @report@ or @assert@, because nvc prints those on standard error, where
-- the driver does not look. Vectors are printed with @to_hstring@
-- (uppercase hex) and bits with @to_string@; the text after a marker is
-- informational only.
--
-- Every identifier the testbench introduces starts with @gin_@, which no net
-- may use: signals mirroring the design's ports are @gin_sig_\<port\>@, and
-- the other names (@gin_tb@, @gin_row@, @gin_rows@, @gin_vectors@, @gin_dut@,
-- @gin_stimulus@, @gin_line@, @gin_mismatches@, @gin_t@) never start with
-- @gin_sig_@, so the two groups cannot collide. Record fields carry the port
-- names themselves.
module Gin.Backend.VHDL.Testbench
  ( renderTestbench

    -- * VHDL syntax shared with the design renderer
  , headerComments
  , contextClause
  , vhdlType
  , literal
  ) where

import Data.Bits (testBit)
import Data.Char (GeneralCategory (..), generalCategory, toUpper)
import Data.Text (Text)
import Data.Text qualified as Text
import Gin.Backend.Types (failMarker, mismatchMarker, passMarker)
import Gin.Core.Value (Value (..))
import Gin.Netlist.Types
  ( HLit (..)
  , HwType (..)
  , Ident (..)
  , Module (..)
  , Net (..)
  , Output (..)
  )
import Gin.Vectors (Cycle (..), Vectors (..))
import Numeric (showHex)
import Numeric.Natural (Natural)

----------------------------------------------------------------------
-- Shared syntax

-- | Every header entry as @--@ line comments, in order.
--
-- Entries are split at every character a VHDL tool may treat as the end of
-- a line (LF, CR, VT and FF per IEEE 1076-2008, plus NEL and the Unicode
-- line and paragraph separators, which editors display as line breaks), so
-- header text can never escape its comment. nvc itself ends a comment only
-- at LF, but other tools follow the standard. CR LF counts as one break.
-- Tabs become spaces, and any remaining control or format character
-- (bidirectional overrides, NUL, …) becomes U+FFFD. Empty lines become a
-- bare @--@.
headerComments :: [Text] -> [Text]
headerComments = fmap comment . concatMap (Text.split isLineEnd . Text.replace "\r\n" "\n")
  where
    comment l
      | Text.null l = "--"
      | otherwise = "-- " <> Text.map scrub l
    isLineEnd c = c `elem` ("\n\r\v\f\x85\x2028\x2029" :: String)
    scrub c
      | c == '\t' = ' '
      | generalCategory c `elem` [Control, Format] = '\xFFFD'
      | otherwise = c

-- | The libraries and packages every generated file uses. Only
-- @ieee.std_logic_1164@ and @ieee.numeric_std@ are referenced, whose names
-- are all in 'Gin.Netlist.Types.reservedWords'.
contextClause :: [Text]
contextClause =
  [ "library ieee;"
  , "use ieee.std_logic_1164.all;"
  , "use ieee.numeric_std.all;"
  ]

-- | @std_logic@ for 'HBit' and @unsigned(n-1 downto 0)@ for @'HVec' n@.
vhdlType :: HwType -> Text
vhdlType = \case
  HBit -> "std_logic"
  HVec n -> "unsigned(" <> tshow (toInteger n - 1) <> " downto 0)"

-- | A constant operand, qualified so that its type never depends on
-- context: @std_logic'('0')@ / @std_logic'('1')@, or @unsigned'("…")@ with
-- exactly one binary digit per bit of the literal's width. Bare literals
-- are ambiguous in comparisons, mux conditions and @to_hstring@; integer
-- conversions such as @to_unsigned@ cannot represent widths above 31 bits.
literal :: HLit -> Text
literal = \case
  HLitBit b -> "std_logic'(" <> bitChar b <> ")"
  HLitVec w x -> "unsigned'(\"" <> binaryDigits w x <> "\")"

bitChar :: Bool -> Text
bitChar b = if b then "'1'" else "'0'"

-- | Exactly @w@ binary digits of @x mod 2^w@, most significant first.
binaryDigits :: Natural -> Integer -> Text
binaryDigits w x = Text.pack [if testBit v i then '1' else '0' | i <- [n - 1, n - 2 .. 0]]
  where
    n = fromIntegral w :: Int
    v = x `mod` 2 ^ w

-- | Exactly @ceil(w/4)@ uppercase hex digits of @x mod 2^w@.
hexDigits :: Natural -> Integer -> Text
hexDigits w x =
  Text.justifyRight (fromIntegral ((w + 3) `div` 4)) '0' $
    Text.pack (fmap toUpper (showHex (x `mod` 2 ^ w) ""))

tshow :: (Show a) => a -> Text
tshow = Text.pack . show

----------------------------------------------------------------------
-- Testbench

-- | The self-checking testbench, entity @\<modName\>_tb@ with architecture
-- @gin_tb@, instantiating @work.\<modName\>@.
--
-- It follows the protocol of @docs/semantics.md@ with a 10 ns clock period:
-- reset high and every input zero with the clock low, one rising edge, reset
-- low; then for each cycle the inputs are driven with the clock low, every
-- output is compared 1 ns later (one @GIN-MISMATCH@ line per differing
-- port), and one rising edge follows. A final @GIN-PASS cycles=\<N\>@ or
-- @GIN-FAIL mismatches=\<k\>@ line precedes @std.env.finish@.
--
-- Precondition (checked by the driver): the vectors' ports equal the
-- module's by name, order and type. The module's ports name and type every
-- field; a value of the wrong shape is coerced to the port's type (a vector
-- to its least significant bit, a bit to 0 or 1) and missing values count
-- as zero, so the function stays total. A malformed vector set still never
-- passes: every missing, ill-typed or extra value in a row counts as a
-- mismatch, reported in one line before the first cycle
-- (@GIN-MISMATCH malformed-values=\<k\> first-cycle=\<t\>@), as an unread
-- input would otherwise hide a wrong value.
renderTestbench :: Module -> Vectors -> Text
renderTestbench m vs =
  Text.unlines $
    headerComments (modHeader m)
      <> contextClause
      <> ["use std.textio.all;", ""]
      <> ["entity " <> tb <> " is", "end entity " <> tb <> ";", ""]
      <> ["architecture gin_tb of " <> tb <> " is"]
      <> indent (table m rows <> signalDecls m)
      <> ["begin"]
      <> indent (instantiation m <> [""] <> stimulus m (length rows) (malformed m rows))
      <> ["end architecture gin_tb;"]
  where
    tb = unIdent (modName m) <> "_tb"
    rows = vecCycles vs

indent :: [Text] -> [Text]
indent = fmap (\l -> if Text.null l then l else "  " <> l)

-- | Append a separator to every element but the last.
punctuate :: Text -> [Text] -> [Text]
punctuate sep = \case
  [] -> []
  [x] -> [x]
  x : xs -> (x <> sep) : punctuate sep xs

outputNets :: Module -> [Net]
outputNets = fmap outNet . modOutputs

name :: Net -> Text
name = unIdent . netName

-- | The port-mirroring testbench signal.
sig :: Ident -> Text
sig i = "gin_sig_" <> unIdent i

-- | The record type, the table type and the table itself. An empty vector
-- set needs none of them.
table :: Module -> [Cycle] -> [Text]
table _ [] = []
table m rows =
  ["type gin_row is record"]
    <> indent [name n <> " : " <> vhdlType (netType n) <> ";" | n <- fields]
    <> ["end record gin_row;", "type gin_rows is array (natural range <>) of gin_row;"]
    <> ["constant gin_vectors : gin_rows(0 to " <> tshow (length rows - 1) <> ") := ("]
    <> indent (punctuate "," (zipWith row [0 :: Int ..] rows))
    <> [");", ""]
  where
    fields = modInputs m <> outputNets m
    row t c =
      tshow t <> " => (" <> Text.intercalate ", " (entries c) <> ")"
    entries c = cells (modInputs m) (cycInputs c) <> cells (outputNets m) (cycOutputs c)
    cells ns vals = zipWith cell ns (vals <> repeat (VBool False))
    cell n v = name n <> " => " <> dataLiteral (netType n) v

-- | A table entry: @'0'@ / @'1'@ for 'HBit', an exact-width hex bit-string
-- @\<w\>x"\<hex\>"@ for 'HVec'. Entries only appear in named record
-- aggregates, where the field fixes the literal's type.
dataLiteral :: HwType -> Value -> Text
dataLiteral ty v = case ty of
  HBit -> bitChar (asBit v)
  HVec w -> tshow w <> "x\"" <> hexDigits w (asInteger v) <> "\""
  where
    asBit = \case
      VBool b -> b
      VBV _ x -> odd x
      VTuple _ -> False
    asInteger = \case
      VBool b -> if b then 1 else 0
      VBV _ x -> x
      VTuple _ -> 0

-- | Clock and reset start low and high; inputs start at zero; outputs are
-- left to the design.
signalDecls :: Module -> [Text]
signalDecls m =
  [ decl (modClock m) HBit (Just "'0'")
  , decl (modReset m) HBit (Just "'1'")
  ]
    <> [decl (netName n) (netType n) (Just (zero (netType n))) | n <- modInputs m]
    <> [decl (netName n) (netType n) Nothing | n <- outputNets m]
  where
    decl i ty initial =
      "signal " <> sig i <> " : " <> vhdlType ty <> maybe "" (" := " <>) initial <> ";"

zero :: HwType -> Text
zero = \case
  HBit -> "'0'"
  HVec _ -> "(others => '0')"

instantiation :: Module -> [Text]
instantiation m =
  ["gin_dut : entity work." <> unIdent (modName m), "  port map ("]
    <> fmap ("    " <>) (punctuate "," [unIdent i <> " => " <> sig i | i <- formals])
    <> ["  );"]
  where
    formals =
      [modClock m, modReset m] <> fmap netName (modInputs m <> outputNets m)

-- | The number of row values that do not fit the module's ports (missing,
-- ill-typed or extra, among inputs and outputs) and the first cycle
-- holding one, if any.
malformed :: Module -> [Cycle] -> Maybe (Int, Int)
malformed m rows = case filter ((> 0) . snd) (zip [0 ..] counts) of
  [] -> Nothing
  (first, _) : _ -> Just (sum counts, first)
  where
    counts = fmap misfits rows
    misfits c = mismatched (modInputs m) (cycInputs c) + mismatched (outputNets m) (cycOutputs c)
    mismatched ns vals =
      length (filter not (zipWith fits (fmap netType ns) vals))
        + abs (length ns - length vals)
    fits ty = \case
      VBool _ -> ty == HBit
      VBV w x -> ty == HVec w && x >= 0 && x < 2 ^ w
      VTuple _ -> False

-- | The process that drives the protocol for @n@ cycles, counting the
-- malformed values (see 'malformed') as mismatches up front.
stimulus :: Module -> Int -> Maybe (Int, Int) -> [Text]
stimulus m n bad =
  [ "gin_stimulus : process"
  , "  variable gin_line : line;"
  , "  variable gin_mismatches : natural := 0;"
  , "begin"
  ]
    <> indent body
    <> ["end process gin_stimulus;"]
  where
    clk = sig (modClock m)
    rst = sig (modReset m)
    body =
      [ "-- Reset: clock low, reset high, every input zero; one rising edge"
      , "-- loads the registers' initial values, then reset is released."
      , clk <> " <= '0';"
      , rst <> " <= '1';"
      ]
        <> [sig (netName i) <> " <= " <> zero (netType i) <> ";" | i <- modInputs m]
        <> [ "wait for 5 ns;"
           , clk <> " <= '1';"
           , "wait for 5 ns;"
           , clk <> " <= '0';"
           , rst <> " <= '0';"
           ]
        <> maybe [] reportMalformed bad
        <> cycles
        <> verdict
    reportMalformed (k, first) =
      [ "-- Missing, ill-typed or extra values in the vectors: each is a mismatch."
      , "gin_mismatches := " <> tshow k <> ";"
      , writeText
          (mismatchMarker <> " malformed-values=" <> tshow k <> " first-cycle=" <> tshow first)
      , "writeline(output, gin_line);"
      ]
    cycles
      | n <= 0 = []
      | otherwise =
          [ "-- Each cycle: drive the inputs with the clock low, compare every"
          , "-- output 1 ns later, then one rising edge."
          , "for gin_t in 0 to " <> tshow (n - 1) <> " loop"
          ]
            <> indent
              ( [sig (netName i) <> " <= " <> field i <> ";" | i <- modInputs m]
                  <> ["wait for 1 ns;"]
                  <> concatMap compareOutput (outputNets m)
                  <> [ "wait for 4 ns;"
                     , clk <> " <= '1';"
                     , "wait for 5 ns;"
                     , clk <> " <= '0';"
                     ]
              )
            <> ["end loop;"]
    verdict =
      [ "if gin_mismatches = 0 then"
      , "  " <> writeText (passMarker <> " cycles=" <> tshow (max 0 n))
      , "else"
      , "  " <> writeText (failMarker <> " mismatches=")
      , "  write(gin_line, gin_mismatches);"
      , "end if;"
      , "writeline(output, gin_line);"
      , "std.env.finish;"
      , "wait;"
      ]

-- | The table entry for a port in cycle @gin_t@.
field :: Net -> Text
field n = "gin_vectors(gin_t)." <> name n

writeText :: Text -> Text
writeText t = "write(gin_line, string'(\"" <> t <> "\"));"

-- | Compare one output with its expected value; on a difference count it and
-- print a mismatch line.
compareOutput :: Net -> [Text]
compareOutput n =
  ["if " <> actual <> " /= " <> field n <> " then"]
    <> indent
      [ "gin_mismatches := gin_mismatches + 1;"
      , writeText (mismatchMarker <> " cycle=")
      , "write(gin_line, gin_t);"
      , writeText (" port=" <> name n <> " expected=")
      , "write(gin_line, " <> render (field n) <> ");"
      , writeText " got="
      , "write(gin_line, " <> render actual <> ");"
      , "writeline(output, gin_line);"
      ]
    <> ["end if;"]
  where
    actual = sig (netName n)
    render x = case netType n of
      HBit -> "to_string(" <> x <> ")"
      HVec _ -> "to_hstring(" <> x <> ")"
