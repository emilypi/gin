-- | Verilog-2005 and SystemVerilog-2017 testbench generation, and the
-- lexical helpers that the Verilog-family design renderers share.
--
-- A testbench instantiates the design as @gin_dut@ and replays the
-- vectors in one straight-line @initial@ block, following the testbench
-- protocol of @docs/semantics.md@: 10 ns clock period starting low, one
-- reset edge with every input at zero, then per cycle drive the inputs,
-- wait 1 ns, compare every output with @!==@ (so X and Z count as
-- mismatches), and apply one rising edge. It prints one
-- 'Gin.Backend.Types.mismatchMarker' line per differing port and finally
-- exactly one 'Gin.Backend.Types.passMarker' or
-- 'Gin.Backend.Types.failMarker' line, then calls @$finish@.
--
-- Expected values appear only as text inside @$display@ format strings,
-- computed here; no literal is ever passed as a @$display@ argument
-- (Icarus Verilog 13 aborts on literal arguments of 4090 bits or more).
-- Straight-line code stays fast at the largest vector payload gin
-- accepts ('Gin.Limits.maxVectorBits'): 100000 one-bit cycles compile
-- and run in a few seconds under Icarus Verilog.
module Gin.Backend.Verilog.Testbench
  ( Dialect (..)
  , renderTestbench
  , headerComments
  , literal
  , sizedHex
  , hexDigits
  , typeRange
  , showNat
  , indent
  , commaSeparated
  ) where

import Data.Char (GeneralCategory (..), generalCategory)
import Data.Text (Text)
import Data.Text qualified as Text
import Gin.Backend.Types (failMarker, mismatchMarker, passMarker)
import Gin.Core.Value (Value (..))
import Gin.Netlist.Types
import Gin.Vectors (Cycle (..), Vectors (..))
import Numeric (showHex)
import Numeric.Natural (Natural)

-- | The two members of the Verilog family gin generates.
data Dialect
  = -- | IEEE 1364-2005: @wire@, @reg@ and @always \@(posedge ...)@.
    Verilog2005
  | -- | IEEE 1800-2017: @logic@ and @always_ff \@(posedge ...)@.
    SystemVerilog2017
  deriving stock (Eq, Show, Enum, Bounded)

-- | The self-checking testbench, module @<modName>_tb@.
--
-- Precondition (checked by the driver): the vectors' ports equal the
-- module's by name, order and type. Ports are taken from the module and
-- row values by position, and every value that does not fit counts as a
-- mismatch in its cycle, so a malformed vector set never passes: a missing
-- or ill-typed expected value is reported as @expected=none@; a missing or
-- ill-typed input value is driven as all X and reported as
-- @input=invalid@ (an input the design never reads would not pass the X
-- on); and values beyond the ports are reported as @extra-inputs=\<k\>@
-- or @extra-outputs=\<k\>@.
renderTestbench :: Dialect -> Module -> Vectors -> Text
renderTestbench dialect m vs =
  Text.unlines $
    headerComments m
      <> ["`timescale 1ns/1ps", "", "module " <> unIdent (modName m) <> "_tb;"]
      <> fmap indent signals
      <> [""]
      <> fmap indent dut
      <> [""]
      <> fmap indent initial
      <> ["endmodule"]
  where
    variable = case dialect of
      Verilog2005 -> "reg "
      SystemVerilog2017 -> "logic "
    net' = case dialect of
      Verilog2005 -> "wire "
      SystemVerilog2017 -> "logic "
    clk = unIdent (modClock m)
    rst = unIdent (modReset m)
    outs = fmap outNet (modOutputs m)
    signals =
      [variable <> clk <> ";", variable <> rst <> ";"]
        <> [variable <> typeRange (netType n) <> unIdent (netName n) <> ";" | n <- modInputs m]
        <> [net' <> typeRange (netType n) <> unIdent (netName n) <> ";" | n <- outs]
        <> ["integer gin_mismatches;"]
    dut =
      [unIdent (modName m) <> " gin_dut ("]
        <> fmap indent (commaSeparated [connect i | i <- modClock m : modReset m : portIdents])
        <> [");"]
    portIdents = fmap netName (modInputs m <> outs)
    connect i = "." <> unIdent i <> "(" <> unIdent i <> ")"
    initial =
      ["initial begin"]
        <> fmap
          indent
          ( ["gin_mismatches = 0;", clk <> " = 1'b0;", rst <> " = 1'b1;"]
              <> [drive n (Just 0) | n <- modInputs m]
              <> ["#5 " <> clk <> " = 1'b1;", "#5 " <> clk <> " = 1'b0;", rst <> " = 1'b0;"]
              <> concat (zipWith cycleLines [0 :: Int ..] (vecCycles vs))
              <> verdict
              <> ["$finish;"]
          )
        <> ["end"]
    cycleLines t c =
      ["// cycle " <> showInt t]
        <> zipWith drive (modInputs m) inputBits
        <> concat [report t (invalid n) | (n, Nothing) <- zip (modInputs m) inputBits]
        <> extra t "extra-inputs" (length (cycInputs c) - length (modInputs m))
        <> extra t "extra-outputs" (length (cycOutputs c) - length outs)
        <> ["#1;"]
        <> concat (zipWith (check t) outs (rowBits outs (cycOutputs c)))
        <> ["#4 " <> clk <> " = 1'b1;", "#5 " <> clk <> " = 1'b0;"]
      where
        inputBits = rowBits (modInputs m) (cycInputs c)
        invalid n = "port=" <> unIdent (netName n) <> " input=invalid"
    -- a mismatch the generator found in the row itself
    report t what =
      [ "$display(\"" <> mismatchMarker <> " cycle=" <> showInt t <> " " <> what <> "\");"
      , "gin_mismatches = gin_mismatches + 1;"
      ]
    extra t what k = if k > 0 then report t (what <> "=" <> showInt k) else []
    drive n bits =
      unIdent (netName n) <> " = " <> maybe (unknown ty) (valueLiteral ty) bits <> ";"
      where
        ty = netType n
    check t n = \case
      Just bits ->
        ["if (" <> name <> " !== " <> valueLiteral (netType n) bits <> ") begin"]
          <> fmap indent (mismatch (hexDigits (hwWidth (netType n)) bits))
          <> ["end"]
      Nothing -> mismatch "none"
      where
        name = unIdent (netName n)
        mismatch expected =
          [ "$display(\""
              <> mismatchMarker
              <> " cycle="
              <> showInt t
              <> " port="
              <> name
              <> " expected="
              <> expected
              <> " got=%h\", "
              <> name
              <> ");"
          , "gin_mismatches = gin_mismatches + 1;"
          ]
    cycles = length (vecCycles vs)
    verdict =
      [ "if (gin_mismatches == 0) begin"
      , indent ("$display(\"" <> passMarker <> " cycles=" <> showInt cycles <> "\");")
      , "end else begin"
      , indent ("$display(\"" <> failMarker <> " mismatches=%0d\", gin_mismatches);")
      , "end"
      ]

-- | The payload of each port's value in a row, by position; 'Nothing'
-- for a missing or ill-typed value.
rowBits :: [Net] -> [Value] -> [Maybe Integer]
rowBits ports row =
  zipWith (\n v -> v >>= valueBits (netType n)) ports (fmap Just row <> repeat Nothing)

-- | The payload of a value of the given port type, if it has that type.
valueBits :: HwType -> Value -> Maybe Integer
valueBits ty = \case
  VBool b | ty == HBit -> Just (if b then 1 else 0)
  VBV w v | ty == HVec w, v >= 0, v < 2 ^ w -> Just v
  _ -> Nothing

valueLiteral :: HwType -> Integer -> Text
valueLiteral = \case
  HBit -> literal . HLitBit . (/= 0)
  HVec w -> sizedHex w

-- | All bits X, at the port's width.
unknown :: HwType -> Text
unknown ty = showNat (hwWidth ty) <> "'bx"

-- | Each header line as a @//@ comment. Characters that could end the
-- comment or hide text (Unicode categories Cc, Cf, Zl, Zp, Cs, Co, Cn)
-- are replaced with U+FFFD. Header lines are expected to start with the
-- fixed tags the netlist builder adds, so none reads as a tool
-- directive such as @verilator lint_off@.
headerComments :: Module -> [Text]
headerComments = fmap (("// " <>) . Text.map scrub) . modHeader
  where
    scrub c
      | generalCategory c `elem` hidden = '\xFFFD'
      | otherwise = c
    hidden =
      [Control, Format, LineSeparator, ParagraphSeparator, Surrogate, PrivateUse, NotAssigned]

-- | A sized constant: @1'b0@ / @1'b1@ for bits, @<w>'h<hex>@ for vectors.
literal :: HLit -> Text
literal = \case
  HLitBit b -> if b then "1'b1" else "1'b0"
  HLitVec w v -> sizedHex w v

-- | @<w>'h<hexDigits w v>@.
sizedHex :: Natural -> Integer -> Text
sizedHex w v = showNat w <> "'h" <> hexDigits w v

-- | Lowercase hex of @v mod 2^w@, zero-padded to @ceil(w/4)@ digits (at
-- least one).
hexDigits :: Natural -> Integer -> Text
hexDigits w v = Text.justifyRight digits '0' (Text.pack (showHex (v `mod` (2 ^ w)) ""))
  where
    digits = max 1 (fromIntegral ((w + 3) `div` 4))

-- | The packed range of a declaration, with a trailing space: empty for
-- 'HBit', @[n-1:0] @ for @'HVec' n@.
typeRange :: HwType -> Text
typeRange = \case
  HBit -> ""
  HVec n -> "[" <> Text.pack (show (toInteger n - 1)) <> ":0] "

-- | Decimal rendering of a width or index.
showNat :: Natural -> Text
showNat = Text.pack . show

showInt :: Int -> Text
showInt = Text.pack . show

-- | Indent one level (two spaces).
indent :: Text -> Text
indent = ("  " <>)

-- | Append a comma to every line but the last.
commaSeparated :: [Text] -> [Text]
commaSeparated ls = zipWith (<>) ls (fmap (const ",") (drop 1 ls) <> [""])
