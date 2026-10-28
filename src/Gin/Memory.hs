-- |
-- Module       : Gin.Memory
-- Copyright    : (c) 2026 Emily Pillmore
-- License      : BSD-3-Clause
-- Maintainer   : Emily Pillmore <emilypi@cohomolo.gy>
-- Stability    : experimental
-- Portability  : non-portable (GHC extensions)
--
-- Protocol-neutral memory accelerator generation and bounded traffic models.
-- See @docs/memory-contract.md@ for the handshake and reset contracts.
module Gin.Memory
  ( MemoryConfig (..)
  , defaultMemoryConfig
  , MemoryDesign (..)
  , generateMemoryAccelerator
  , TrafficScenario (..)
  , defaultTrafficScenarios
  , decodeTrafficScenarios
  , decodeMemoryWords
  , MemoryRunStatus (..)
  , MemoryRun (..)
  , MemoryEvent (..)
  , MemoryOperation (..)
  , simulateMemory
  ) where

import Control.Monad (unless, when)
import Data.Char (isAsciiLower, isAsciiUpper, isDigit)
import Data.Aeson qualified as A
import Data.Aeson.Key qualified as Key
import Data.Aeson.KeyMap qualified as KeyMap
import Data.Aeson.Types (Parser, (.:))
import Data.ByteString.Lazy (LazyByteString)
import Data.IntMap.Strict qualified as IntMap
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as Text
import Gin.Backend.SystemVerilog (systemVerilog)
import Gin.Backend.Types (Backend (..))
import Gin.Core.Json (decodeWith)
import Gin.Core.Normal (NBind (..), NModule (..), NOutput (..), NRhs (..))
import Gin.Core.Type (Ty (..))
import Gin.Core.Value (Value (..))
import Gin.Error (GinError, Stage (StDriver, StSim), ginError)
import Gin.Netlist.Build (buildNetlist)
import Gin.Netlist.Types qualified as Net
import Gin.Normalize (checkNormal)
import Gin.Sim (simulateNormal)
import Numeric.Natural (Natural)

data MemoryConfig = MemoryConfig
  { memoryLanes :: !Int
  , memoryAddressWidth :: !Int
  }
  deriving stock (Eq, Show)

defaultMemoryConfig :: MemoryConfig
defaultMemoryConfig = MemoryConfig 1 32

data MemoryDesign = MemoryDesign
  { memoryTopName :: !Text
  , memorySystemVerilog :: !Text
  , memoryWordWidth :: !Natural
  , memoryConfig :: !MemoryConfig
  }
  deriving stock (Eq, Show)

-- | Latencies are minimum cycles after request acceptance. On cycle t,
-- request / response service is possible when t mod the relevant period is
-- zero. Each channel serves at most one request and one response per cycle.
-- Addresses select channels modulo 'trafficChannels'; each channel advances
-- its round-robin priority after a grant. This models an external adapter.
data TrafficScenario = TrafficScenario
  { trafficName :: !Text
  , trafficChannels :: !Int
  , trafficReadLatency :: !Int
  , trafficWriteLatency :: !Int
  , trafficAcceptEvery :: !Int
  , trafficResponseEvery :: !Int
  , trafficCycleLimit :: !Int
  }
  deriving stock (Eq, Show)

defaultTrafficScenarios :: [TrafficScenario]
defaultTrafficScenarios =
  [ TrafficScenario "single-channel" 1 8 4 1 1 100000
  , TrafficScenario "four-channel" 4 8 4 1 1 100000
  , TrafficScenario "contended" 1 24 12 3 2 100000
  ]

-- | Strict bounded JSON array of 1–16 named scenarios. Unknown and duplicate
-- keys are errors. Names are unique ASCII letters, digits, underscores or
-- hyphens, at most 64 characters.
decodeTrafficScenarios :: LazyByteString -> Either GinError [TrafficScenario]
decodeTrafficScenarios = decodeWith $ A.withArray "traffic scenarios" $ \values -> do
  unless (not (null values) && length values <= 16) (fail "expected 1 to 16 traffic scenarios")
  scenarios <- traverse scenarioParser (foldr (:) [] values)
  let names = map trafficName scenarios
  unless (Set.size (Set.fromList names) == length names) (fail "traffic scenario names must be unique")
  pure scenarios
  where
    scenarioParser = A.withObject "traffic scenario" $ \object -> do
      let allowed = ["name", "channels", "readLatency", "writeLatency", "acceptEvery", "responseEvery", "cycleLimit"]
      unless (all ((`elem` allowed) . Key.toText) (KeyMap.keys object)) (fail "unknown traffic scenario field")
      name <- object .: "name"
      unless (not (Text.null name) && Text.length name <= 64 && Text.all nameChar name) (fail "invalid traffic scenario name")
      channels <- object .: "channels" >>= bounded "channels" 1 16
      readLatency <- object .: "readLatency" >>= bounded "readLatency" 1 1000000
      writeLatency <- object .: "writeLatency" >>= bounded "writeLatency" 1 1000000
      acceptEvery <- object .: "acceptEvery" >>= bounded "acceptEvery" 1 1000000
      responseEvery <- object .: "responseEvery" >>= bounded "responseEvery" 1 1000000
      cycleLimit <- object .: "cycleLimit" >>= bounded "cycleLimit" 0 1000000
      pure (TrafficScenario name channels readLatency writeLatency acceptEvery responseEvery cycleLimit)
    nameChar c = isAsciiLower c || isAsciiUpper c || isDigit c || c == '_' || c == '-'

-- | Unsigned JSON numbers, limited by the existing strict decoder's global
-- number bound (currently 2^31-1), and at most 100000 words. Wider payloads
-- may be supplied through the Haskell API; width is checked by simulation.
decodeMemoryWords :: LazyByteString -> Either GinError [Integer]
decodeMemoryWords = decodeWith $ A.withArray "memory words" $ \values -> do
  when (length values > 100000) (fail "at most 100000 memory words are accepted")
  traverse A.parseJSON (foldr (:) [] values)

bounded :: String -> Int -> Int -> Int -> Parser Int
bounded label lo hi n
  | n >= lo && n <= hi = pure n
  | otherwise = fail (label <> " must be between " <> show lo <> " and " <> show hi)

data MemoryRunStatus = Completed | CycleLimit
  deriving stock (Eq, Show)

data MemoryOperation = ReadRequest | ReadResponse | WriteRequest | WriteResponse
  deriving stock (Eq, Ord, Show)

-- | Accepted handshake, with logical word index (not a byte address).
data MemoryEvent = MemoryEvent
  { memoryEventCycle :: !Int
  , memoryEventLane :: !Int
  , memoryEventWord :: !Int
  , memoryEventOperation :: !MemoryOperation
  , memoryEventValue :: !Integer
  }
  deriving stock (Eq, Show)

data MemoryRun = MemoryRun
  { memoryRunStatus :: !MemoryRunStatus
  , memoryCycles :: !Int
  , memoryReads :: !Int
  , memoryWrites :: !Int
  , memoryOutput :: ![Maybe Integer]
  , memoryEvents :: ![MemoryEvent]
  }
  deriving stock (Eq, Show)

validateConfig :: MemoryConfig -> Either GinError ()
validateConfig cfg = do
  unless (memoryLanes cfg >= 1 && memoryLanes cfg <= 16) $
    Left (ginError StDriver "memory lanes must be between 1 and 16")
  unless (memoryAddressWidth cfg >= 1 && memoryAddressWidth cfg <= 64) $
    Left (ginError StDriver "memory address width must be between 1 and 64")

validateKernel :: NModule -> Either GinError Natural
validateKernel nm = do
  checkNormal nm
  when (any isRegister (nmBinds nm)) $
    Left (ginError StDriver "memory kernel must be combinational")
  case (nmInputs nm, nmOutputs nm) of
    ([(_, TBitVec w)], [NOutput {noTy = TBitVec v}]) | w == v -> pure w
    _ -> Left (ginError StDriver "memory kernel requires one bit-vector input and one output of equal width")
  where
    isRegister NBind {nbRhs = NReg _ _} = True
    isRegister _ = False

-- | Generate checked kernel HDL and a fixed-size multi-lane wrapper. All
-- interpolated names come from the existing checked netlist builder; no
-- command text or unchecked HDL fragments are accepted.
generateMemoryAccelerator :: MemoryConfig -> NModule -> Either GinError MemoryDesign
generateMemoryAccelerator cfg nm = do
  validateConfig cfg
  width <- validateKernel nm
  net <- buildNetlist nm
  let top = "gin_memory_accelerator"
  pure MemoryDesign
    { memoryTopName = top
    , memorySystemVerilog = "// Memory protocol artifact: the source trace below covers the pure word kernel.\n"
        <> "// The wrapper uses the ready/valid, reset and completion contract in docs/memory-contract.md.\n"
        <> backendRender systemVerilog net <> "\n" <> renderWrapper top cfg width net
    , memoryWordWidth = width
    , memoryConfig = cfg
    }

renderWrapper :: Text -> MemoryConfig -> Natural -> Net.Module -> Text
renderWrapper top cfg width net = Text.unlines $
  [ "// Generic word-addressed accelerator. See docs/memory-contract.md."
  , "module " <> top <> " ("
  , "  input logic clk, rst, cmd_valid, output logic cmd_ready,"
  , "  input logic [" <> a1 <> ":0] cmd_src, cmd_dst,"
  , "  input logic [" <> a <> ":0] cmd_count,"
  , "  output logic done_valid, done_error, input logic done_ready,"
  , "  output logic [" <> l1 <> ":0] mem_req_valid, mem_req_write,"
  , "  input logic [" <> l1 <> ":0] mem_req_ready,"
  , "  output logic [" <> t (lanes * aw - 1) <> ":0] mem_req_addr,"
  , "  output logic [" <> t (toInteger lanes * toInteger width - 1) <> ":0] mem_req_wdata,"
  , "  input logic [" <> l1 <> ":0] mem_rsp_valid,"
  , "  output logic [" <> l1 <> ":0] mem_rsp_ready,"
  , "  input logic [" <> t (toInteger lanes * toInteger width - 1) <> ":0] mem_rsp_rdata"
  , ");"
  , "  localparam integer LANES = " <> t lanes <> ", AW = " <> a <> ", DW = " <> t width <> ";"
  , "  localparam logic [2:0] IDLE=0, READ_REQ=1, READ_WAIT=2, WRITE_REQ=3, WRITE_WAIT=4;"
  , "  logic active;"
  , "  logic [AW-1:0] source_base, destination_base;"
  , "  logic [AW:0] count;"
  , "  logic [AW+5:0] word_index [0:LANES-1];"
  , "  logic [2:0] state [0:LANES-1];"
  , "  logic [DW-1:0] write_data [0:LANES-1];"
  , "  wire [DW-1:0] kernel_result [0:LANES-1];"
  , "  wire [AW+1:0] source_end = {2'b0,cmd_src} + {1'b0,cmd_count};"
  , "  wire [AW+1:0] destination_end = {2'b0,cmd_dst} + {1'b0,cmd_count};"
  , "  wire invalid_command = (source_end > " <> t (aw + 2) <> "'d" <> t (2 ^ aw :: Integer) <> ") ||"
  , "    (destination_end > " <> t (aw + 2) <> "'d" <> t (2 ^ aw :: Integer) <> ") ||"
  , "    ((cmd_count != 0) && ({2'b0,cmd_src} < destination_end) && ({2'b0,cmd_dst} < source_end));"
  , "  logic all_idle;"
  , "  always_comb begin"
  , "    all_idle = 1'b1;"
  , "    for (integer j=0; j<LANES; j=j+1) if (state[j] != IDLE) all_idle = 1'b0;"
  , "  end"
  , "  assign cmd_ready = !rst && !active && !done_valid;"
  , "  for (genvar g=0; g<LANES; g=g+1) begin: lane"
  , "    assign mem_req_valid[g] = !rst && ((state[g] == READ_REQ) || (state[g] == WRITE_REQ));"
  , "    assign mem_req_write[g] = (state[g] == WRITE_REQ);"
  , "    assign mem_req_addr[g*AW +: AW] = ((state[g] == WRITE_REQ) ? destination_base : source_base) + word_index[g][AW-1:0];"
  , "    assign mem_req_wdata[g*DW +: DW] = write_data[g];"
  , "    assign mem_rsp_ready[g] = !rst && ((state[g] == READ_WAIT) || (state[g] == WRITE_WAIT));"
  , "    " <> ident (Net.modName net) <> " kernel ("
  , "      ." <> ident (Net.modClock net) <> "(clk), ." <> ident (Net.modReset net) <> "(rst),"
  ] <> inputOutput <>
  [ "    );"
  , "  end"
  , "  always_ff @(posedge clk) begin"
  , "    if (rst) begin"
  , "      active <= 1'b0; done_valid <= 1'b0; done_error <= 1'b0;"
  , "      source_base <= '0; destination_base <= '0; count <= '0;"
  , "      for (integer j=0; j<LANES; j=j+1) begin"
  , "        state[j] <= IDLE; word_index[j] <= '0; write_data[j] <= '0;"
  , "      end"
  , "    end else begin"
  , "      if (done_valid && done_ready) done_valid <= 1'b0;"
  , "      if (cmd_valid && cmd_ready) begin"
  , "        source_base <= cmd_src; destination_base <= cmd_dst; count <= cmd_count;"
  , "        done_error <= invalid_command;"
  , "        if (invalid_command || (cmd_count == 0)) done_valid <= 1'b1;"
  , "        else begin"
  , "          active <= 1'b1;"
  , "          for (integer j=0; j<LANES; j=j+1) begin"
  , "            word_index[j] <= j; state[j] <= (j < cmd_count) ? READ_REQ : IDLE;"
  , "          end"
  , "        end"
  , "      end"
  , "      if (active && all_idle) begin active <= 1'b0; done_valid <= 1'b1; end"
  , "      if (active) for (integer j=0; j<LANES; j=j+1) begin"
  , "        case (state[j])"
  , "          READ_REQ: if (mem_req_ready[j]) state[j] <= READ_WAIT;"
  , "          READ_WAIT: if (mem_rsp_valid[j]) begin"
  , "            write_data[j] <= kernel_result[j]; state[j] <= WRITE_REQ;"
  , "          end"
  , "          WRITE_REQ: if (mem_req_ready[j]) state[j] <= WRITE_WAIT;"
  , "          WRITE_WAIT: if (mem_rsp_valid[j]) begin"
  , "            word_index[j] <= word_index[j] + LANES;"
  , "            state[j] <= ((word_index[j] + LANES) < count) ? READ_REQ : IDLE;"
  , "          end"
  , "          default: state[j] <= IDLE;"
  , "        endcase"
  , "      end"
  , "    end"
  , "  end"
  , "endmodule"
  ]
  where
    lanes = memoryLanes cfg
    aw = memoryAddressWidth cfg
    a = t aw
    a1 = t (aw - 1)
    l1 = t (lanes - 1)
    ident = Net.unIdent
    inputOutput = case (Net.modInputs net, Net.modOutputs net) of
      ([input], [output]) ->
        [ "      ." <> ident (Net.netName input) <> "(mem_rsp_rdata[g*DW +: DW]),"
        , "      ." <> ident (Net.netName (Net.outNet output)) <> "(kernel_result[g])"
        ]
      _ -> [] -- validated one-input/one-output kernel and checked netlist

data Lane = Idle | Reading !Int | ReadPending !Int !Int | Writing !Int | WritePending !Int !Int

-- | Simulate the explicit channel model, not a physical memory device. The
-- logical source range starts at zero and destination range at input length.
-- Output is visible after its write request is accepted; completion also
-- requires the write acknowledgement. Cycles count memory service after the
-- command has been accepted, excluding command/completion handshake overhead.
simulateMemory :: MemoryConfig -> TrafficScenario -> NModule -> [Integer] -> Either GinError MemoryRun
simulateMemory cfg scenario nm wordsIn = do
  validateConfig cfg
  width <- validateKernel nm
  let inputWords = take 100001 wordsIn
      size = length inputWords
      lanes = memoryLanes cfg
      validPeriod n = n >= 1 && n <= 1000000
  unless (trafficChannels scenario >= 1 && trafficChannels scenario <= 16) $
    Left (ginError StSim "traffic channels must be between 1 and 16")
  unless (all validPeriod [trafficReadLatency scenario, trafficWriteLatency scenario, trafficAcceptEvery scenario, trafficResponseEvery scenario]) $
    Left (ginError StSim "traffic latency and service periods must be between 1 and 1000000 cycles")
  unless (trafficCycleLimit scenario >= 0 && trafficCycleLimit scenario <= 1000000) $
    Left (ginError StSim "traffic cycle limit must be between 0 and 1000000")
  when (size > 100000 || toInteger size * toInteger (max 1 (length (nmBinds nm))) > 20000000) $
    Left (ginError StSim "traffic input or kernel evaluation work limit exceeded")
  when (toInteger size * 2 > 2 ^ memoryAddressWidth cfg) $
    Left (ginError StSim "traffic input and output ranges exceed the address space")
  unless (all (\v -> v >= 0 && v < 2 ^ width) inputWords) $
    Left (ginError StSim "traffic input is outside the kernel word width")
  rows <- simulateNormal nm [[VBV width v] | v <- inputWords]
  expected <- traverse (\case [VBV _ v] -> Right v; _ -> Left (ginError StSim "unexpected memory kernel output")) rows
  let input = IntMap.fromList (zip [0 ..] inputWords)
      output = IntMap.fromList (zip [0 ..] expected)
      initial = IntMap.fromList [(lane, if lane < size then Reading lane else Idle) | lane <- [0 .. lanes - 1]]
      finish status cycleNo results readCount writes events = MemoryRun status cycleNo readCount writes
        [IntMap.lookup index results | index <- [0 .. size - 1]] (reverse events)
      loop !cycleNo !states !results !readCount !writes !events !requestTurns !responseTurns
        | all isIdle states = finish Completed cycleNo results readCount writes events
        | cycleNo >= trafficCycleLimit scenario = finish CycleLimit cycleNo results readCount writes events
        | otherwise =
            let order turns choose = concat
                  [ [lane | lane <- take lanes (drop (IntMap.findWithDefault 0 ch turns) (cycle [0 .. lanes - 1])),
                            choose (IntMap.findWithDefault Idle lane states) == Just ch]
                  | ch <- [0 .. trafficChannels scenario - 1]]
                requestChannel = \case
                  Reading index -> Just (index `mod` trafficChannels scenario)
                  Writing index -> Just ((size + index) `mod` trafficChannels scenario)
                  _ -> Nothing
                responseChannel = \case
                  ReadPending index _ -> Just (index `mod` trafficChannels scenario)
                  WritePending index _ -> Just ((size + index) `mod` trafficChannels scenario)
                  _ -> Nothing
                initialStep = (states, results, readCount, writes, events, Set.empty, Set.empty, requestTurns, responseTurns)
                (states', results', readCount', writes', events', _, _, requestTurns', responseTurns') =
                  foldl' (step cycleNo input output size states) initialStep
                    (order requestTurns requestChannel <> order responseTurns responseChannel)
             in loop (cycleNo + 1) states' results' readCount' writes' events' requestTurns' responseTurns'
  pure (loop 0 initial IntMap.empty 0 0 [] IntMap.empty IntMap.empty)
  where
    isIdle Idle = True
    isIdle _ = False
    step cycleNo input output size old (states, results, readCount, writes, events, requests, responses, requestTurns, responseTurns) lane =
      let original = IntMap.findWithDefault Idle lane old
          emit op index value = MemoryEvent cycleNo lane index op value : events
          reqReady channelId = cycleNo `mod` trafficAcceptEvery scenario == 0 && Set.notMember channelId requests
          rspReady channelId due = cycleNo >= due && cycleNo `mod` trafficResponseEvery scenario == 0 && Set.notMember channelId responses
          channel address = address `mod` trafficChannels scenario
          valueAt table index = IntMap.findWithDefault 0 index table
          nextTurn = (lane + 1) `mod` memoryLanes cfg
          unchanged = (states, results, readCount, writes, events, requests, responses, requestTurns, responseTurns)
       in case original of
            Reading index | reqReady (channel index) ->
              (IntMap.insert lane (ReadPending index (cycleNo + trafficReadLatency scenario)) states, results, readCount + 1, writes,
               emit ReadRequest index 0, Set.insert (channel index) requests, responses,
               IntMap.insert (channel index) nextTurn requestTurns, responseTurns)
            ReadPending index due | rspReady (channel index) due ->
              (IntMap.insert lane (Writing index) states, results, readCount, writes,
               emit ReadResponse index (valueAt input index), requests, Set.insert (channel index) responses,
               requestTurns, IntMap.insert (channel index) nextTurn responseTurns)
            Writing index | reqReady (channel (size + index)) ->
              let value = valueAt output index
               in (IntMap.insert lane (WritePending index (cycleNo + trafficWriteLatency scenario)) states,
                   IntMap.insert index value results, readCount, writes + 1,
                   emit WriteRequest index value, Set.insert (channel (size + index)) requests, responses,
                   IntMap.insert (channel (size + index)) nextTurn requestTurns, responseTurns)
            WritePending index due | rspReady (channel (size + index)) due ->
              let next = index + memoryLanes cfg
               in (IntMap.insert lane (if next < size then Reading next else Idle) states, results, readCount, writes,
                   emit WriteResponse index 0, requests, Set.insert (channel (size + index)) responses,
                   requestTurns, IntMap.insert (channel (size + index)) nextTurn responseTurns)
            _ -> unchanged

t :: Show a => a -> Text
t = Text.pack . show
