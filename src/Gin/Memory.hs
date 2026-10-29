{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}

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
  , LaneCount
  , AddressWidth
  , ServiceCycles
  , CycleBudget
  , mkMemoryConfig
  , mkTrafficScenario
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

    -- * Optics
  , memoryLanesL
  , memoryAddressWidthL
  , memoryTopNameL
  , memorySystemVerilogL
  , memoryWordWidthL
  , memoryConfigL
  , trafficNameL
  , trafficChannelsL
  , trafficReadLatencyL
  , trafficWriteLatencyL
  , trafficAcceptEveryL
  , trafficResponseEveryL
  , trafficCycleLimitL
  , memoryEventCycleL
  , memoryEventLaneL
  , memoryEventWordL
  , memoryEventOperationL
  , memoryEventValueL
  , memoryRunStatusL
  , memoryCyclesL
  , memoryReadsL
  , memoryWritesL
  , memoryOutputL
  , memoryEventsL
  , _Completed
  , _CycleLimit
  , _ReadRequest
  , _ReadResponse
  , _WriteRequest
  , _WriteResponse
  , _Idle
  , _Reading
  , _ReadPending
  , _Writing
  , _WritePending
  ) where

import Control.Lens (makePrisms, view)
import Control.Monad (unless, when)
import Data.Char (isAsciiLower, isAsciiUpper, isDigit)
import Data.Aeson qualified as A
import Data.Aeson.Key qualified as Key
import Data.Aeson.KeyMap qualified as KeyMap
import Data.Aeson.Types ((.:))
import Data.ByteString.Lazy (LazyByteString)
import Data.IntMap.Strict qualified as IntMap
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as Text
import Gin.Core.Bounded
import Gin.Core.Optics (makeFieldLenses)
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

-- | Checked settings shared by the generator and traffic model.
type LaneCount = BoundedInt 1 16
type AddressWidth = BoundedInt 1 64
type ServiceCycles = BoundedInt 1 1000000
type CycleBudget = BoundedInt 0 1000000

data MemoryConfig = MemoryConfig
  { memoryLanes :: !LaneCount
  , memoryAddressWidth :: !AddressWidth
  }
  deriving stock (Eq, Show)

defaultMemoryConfig :: MemoryConfig
defaultMemoryConfig = MemoryConfig (boundedIntLiteral @1) (boundedIntLiteral @32)

mkMemoryConfig :: Int -> Int -> Either GinError MemoryConfig
mkMemoryConfig lanes width = MemoryConfig
  <$> setting "memory lanes" (mkBoundedInt lanes)
  <*> setting "memory address width" (mkBoundedInt width)

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
  , trafficChannels :: !LaneCount
  , trafficReadLatency :: !ServiceCycles
  , trafficWriteLatency :: !ServiceCycles
  , trafficAcceptEvery :: !ServiceCycles
  , trafficResponseEvery :: !ServiceCycles
  , trafficCycleLimit :: !CycleBudget
  }
  deriving stock (Eq, Show)

defaultTrafficScenarios :: [TrafficScenario]
defaultTrafficScenarios =
  [ TrafficScenario "single-channel"
      (boundedIntLiteral @1) (boundedIntLiteral @8) (boundedIntLiteral @4)
      (boundedIntLiteral @1) (boundedIntLiteral @1) (boundedIntLiteral @100000)
  , TrafficScenario "four-channel"
      (boundedIntLiteral @4) (boundedIntLiteral @8) (boundedIntLiteral @4)
      (boundedIntLiteral @1) (boundedIntLiteral @1) (boundedIntLiteral @100000)
  , TrafficScenario "contended"
      (boundedIntLiteral @1) (boundedIntLiteral @24) (boundedIntLiteral @12)
      (boundedIntLiteral @3) (boundedIntLiteral @2) (boundedIntLiteral @100000)
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
      either (fail . show) pure (validateTrafficName name)
      channels <- object .: "channels"
      readLatency <- object .: "readLatency"
      writeLatency <- object .: "writeLatency"
      acceptEvery <- object .: "acceptEvery"
      responseEvery <- object .: "responseEvery"
      cycleLimit <- object .: "cycleLimit"
      pure (TrafficScenario name channels readLatency writeLatency acceptEvery responseEvery cycleLimit)

-- | Unsigned JSON numbers, limited by the existing strict decoder's global
-- number bound (currently 2^31-1), and at most 100000 words. Wider payloads
-- may be supplied through the Haskell API; width is checked by simulation.
decodeMemoryWords :: LazyByteString -> Either GinError [Integer]
decodeMemoryWords = decodeWith $ A.withArray "memory words" $ \values -> do
  when (length values > 100000) (fail "at most 100000 memory words are accepted")
  traverse A.parseJSON (foldr (:) [] values)

-- | Parse untrusted integers once, before any model or HDL work.
mkTrafficScenario :: Text -> Int -> Int -> Int -> Int -> Int -> Int -> Either GinError TrafficScenario
mkTrafficScenario name channels readLatency writeLatency acceptEvery responseEvery cycleLimit = do
  validateTrafficName name
  TrafficScenario name
    <$> setting "traffic channels" (mkBoundedInt channels)
    <*> setting "read latency" (mkBoundedInt readLatency)
    <*> setting "write latency" (mkBoundedInt writeLatency)
    <*> setting "request service period" (mkBoundedInt acceptEvery)
    <*> setting "response service period" (mkBoundedInt responseEvery)
    <*> setting "traffic cycle limit" (mkBoundedInt cycleLimit)

setting :: Text -> Either String a -> Either GinError a
setting label = either (Left . ginError StDriver . ((label <> ": ") <>) . Text.pack) Right

validateTrafficName :: Text -> Either GinError ()
validateTrafficName name = unless
  (not (Text.null name) && Text.length name <= 64 && Text.all nameChar name)
  (Left (ginError StDriver "invalid traffic scenario name"))
  where
    nameChar c = isAsciiLower c || isAsciiUpper c || isDigit c || c == '_' || c == '-'

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
  -- The simulator prepends events and reverses once at completion. A list
  -- supports that access pattern without copying a growing vector each step.
  , memoryEvents :: ![MemoryEvent]
  }
  deriving stock (Eq, Show)

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
    lanes = view boundedIntValue (memoryLanes cfg)
    aw = view boundedIntValue (memoryAddressWidth cfg)
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
  width <- validateKernel nm
  let inputWords = take 100001 wordsIn
      size = length inputWords
      lanes = view boundedIntValue (memoryLanes cfg)
  validateTrafficName (trafficName scenario)
  when (size > 100000 || toInteger size * toInteger (max 1 (length (nmBinds nm))) > 20000000) $
    Left (ginError StSim "traffic input or kernel evaluation work limit exceeded")
  when (toInteger size * 2 > 2 ^ view boundedIntValue (memoryAddressWidth cfg)) $
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
        | cycleNo >= cycleLimit = finish CycleLimit cycleNo results readCount writes events
        | otherwise =
            let order turns choose = concat
                  [ [lane | lane <- take lanes (drop (IntMap.findWithDefault 0 ch turns) (cycle [0 .. lanes - 1])),
                            choose (IntMap.findWithDefault Idle lane states) == Just ch]
                  | ch <- [0 .. channels - 1]]
                requestChannel = \case
                  Reading index -> Just (index `mod` channels)
                  Writing index -> Just ((size + index) `mod` channels)
                  _ -> Nothing
                responseChannel = \case
                  ReadPending index _ -> Just (index `mod` channels)
                  WritePending index _ -> Just ((size + index) `mod` channels)
                  _ -> Nothing
                initialStep = (states, results, readCount, writes, events, Set.empty, Set.empty, requestTurns, responseTurns)
                (states', results', readCount', writes', events', _, _, requestTurns', responseTurns') =
                  foldl' (step cycleNo input output size states) initialStep
                    (order requestTurns requestChannel <> order responseTurns responseChannel)
             in loop (cycleNo + 1) states' results' readCount' writes' events' requestTurns' responseTurns'
  pure (loop 0 initial IntMap.empty 0 0 [] IntMap.empty IntMap.empty)
  where
    channels = view boundedIntValue (trafficChannels scenario)
    cycleLimit = view boundedIntValue (trafficCycleLimit scenario)
    readLatency = view boundedIntValue (trafficReadLatency scenario)
    writeLatency = view boundedIntValue (trafficWriteLatency scenario)
    acceptEvery = view boundedIntValue (trafficAcceptEvery scenario)
    responseEvery = view boundedIntValue (trafficResponseEvery scenario)
    isIdle Idle = True
    isIdle _ = False
    step cycleNo input output size old (states, results, readCount, writes, events, requests, responses, requestTurns, responseTurns) lane =
      let original = IntMap.findWithDefault Idle lane old
          emit op index value = MemoryEvent cycleNo lane index op value : events
          reqReady channelId = cycleNo `mod` acceptEvery == 0 && Set.notMember channelId requests
          rspReady channelId due = cycleNo >= due && cycleNo `mod` responseEvery == 0 && Set.notMember channelId responses
          channel address = address `mod` channels
          valueAt table index = IntMap.findWithDefault 0 index table
          nextTurn = (lane + 1) `mod` view boundedIntValue (memoryLanes cfg)
          unchanged = (states, results, readCount, writes, events, requests, responses, requestTurns, responseTurns)
       in case original of
            Reading index | reqReady (channel index) ->
              (IntMap.insert lane (ReadPending index (cycleNo + readLatency)) states, results, readCount + 1, writes,
               emit ReadRequest index 0, Set.insert (channel index) requests, responses,
               IntMap.insert (channel index) nextTurn requestTurns, responseTurns)
            ReadPending index due | rspReady (channel index) due ->
              (IntMap.insert lane (Writing index) states, results, readCount, writes,
               emit ReadResponse index (valueAt input index), requests, Set.insert (channel index) responses,
               requestTurns, IntMap.insert (channel index) nextTurn responseTurns)
            Writing index | reqReady (channel (size + index)) ->
              let value = valueAt output index
               in (IntMap.insert lane (WritePending index (cycleNo + writeLatency)) states,
                   IntMap.insert index value results, readCount, writes + 1,
                   emit WriteRequest index value, Set.insert (channel (size + index)) requests, responses,
                   IntMap.insert (channel (size + index)) nextTurn requestTurns, responseTurns)
            WritePending index due | rspReady (channel (size + index)) due ->
              let next = index + view boundedIntValue (memoryLanes cfg)
               in (IntMap.insert lane (if next < size then Reading next else Idle) states, results, readCount, writes,
                   emit WriteResponse index 0, requests, Set.insert (channel (size + index)) responses,
                   requestTurns, IntMap.insert (channel (size + index)) nextTurn responseTurns)
            _ -> unchanged

t :: Show a => a -> Text
t = Text.pack . show

-- Optics use the same field-name + L convention as Gin.Core.
makeFieldLenses ''MemoryConfig
makeFieldLenses ''MemoryDesign
makeFieldLenses ''TrafficScenario
makeFieldLenses ''MemoryEvent
makeFieldLenses ''MemoryRun
makePrisms ''MemoryRunStatus
makePrisms ''MemoryOperation
makePrisms ''Lane
