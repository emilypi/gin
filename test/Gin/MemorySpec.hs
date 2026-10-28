module Gin.MemorySpec (spec) where

import Control.Monad (forM_)
import Data.Either (isLeft)
import Data.List (sort)
import Data.Map.Strict qualified as Map
import Data.Text qualified as Text
import Data.Text.IO qualified as Text
import Gin.Core.Normal
import Gin.Core.Syntax
import Gin.Examples (counterNormal, sysDomain, testCertificate)
import Gin.Memory
import Gin.TestUtil (itWithTools, runTool, withTempDir)
import System.Exit (ExitCode (..))
import System.FilePath ((</>))
import Test.Hspec

spec :: Spec
spec = describe "generic memory accelerator" $ do
  it "rejects stateful kernels, invalid lanes and address widths" $ do
    generateMemoryAccelerator defaultMemoryConfig counterNormal `shouldSatisfy` isLeft
    forM_ [MemoryConfig 0 8, MemoryConfig 17 8, MemoryConfig 1 0, MemoryConfig 1 65] $ \cfg ->
      generateMemoryAccelerator cfg kernel `shouldSatisfy` isLeft
  it "rejects malformed and ambiguous scenario and word inputs" $ do
    forM_ ["[]", "[{\"name\":\"x\",\"name\":\"y\"}]", "[{\"name\":\"x\",\"channels\":0}]",
           "[{\"name\":\"x\",\"unknown\":1}]"] $ \bytes ->
      decodeTrafficScenarios bytes `shouldSatisfy` isLeft
    decodeMemoryWords "[0,1,255]" `shouldBe` Right [0,1,255]
    forM_ ["[-1]", "[1.5]", "[2147483648]", "[\"1\"]"] $ \bytes ->
      decodeMemoryWords bytes `shouldSatisfy` isLeft
    decodeTrafficScenarios "[{\"name\":\"ok\",\"channels\":1,\"readLatency\":2,\"writeLatency\":1,\"acceptEvery\":3,\"responseEvery\":1,\"cycleLimit\":500}]"
      `shouldBe` Right [TrafficScenario "ok" 1 2 1 3 1 500]
  it "preserves word mapping with no loss or duplication across lanes and scenarios" $ do
    forM_ [1,2,3,8,16] $ \lanes ->
      forM_ defaultTrafficScenarios $ \scenario -> do
        result <- expectRight (simulateMemory (MemoryConfig lanes 8) scenario kernel [0 .. 36])
        memoryRunStatus result `shouldBe` Completed
        memoryOutput result `shouldBe` map (Just . (+ 1)) [0 .. 36]
        memoryReads result `shouldBe` 37
        memoryWrites result `shouldBe` 37
        forM_ [ReadRequest, ReadResponse, WriteRequest, WriteResponse] $ \op ->
          sort [memoryEventWord event | event <- memoryEvents result, memoryEventOperation event == op]
            `shouldBe` [0 .. 36]
        forM_ [0 .. lanes - 1] $ \lane -> do
          let observed = [(memoryEventWord event, memoryEventOperation event)
                         | event <- memoryEvents result, memoryEventLane event == lane]
          observed `shouldBe` [(index, op) | index <- [lane,lane+lanes .. 36],
                                          op <- [ReadRequest,ReadResponse,WriteRequest,WriteResponse]]
  it "bounds channel service even when lanes exceed channel count" $ do
    let scenario = TrafficScenario "service" 2 1 1 3 2 10000
    result <- expectRight (simulateMemory (MemoryConfig 16 8) scenario kernel [0 .. 63])
    let countOps ops = Map.fromListWith (+)
          [((memoryEventCycle event, address event `mod` 2), 1 :: Int)
          | event <- memoryEvents result, memoryEventOperation event `elem` ops]
        address event = memoryEventWord event + if memoryEventOperation event `elem` [WriteRequest,WriteResponse] then 64 else 0
    all (<= 1) (countOps [ReadRequest,WriteRequest]) `shouldBe` True
    all (<= 1) (countOps [ReadResponse,WriteResponse]) `shouldBe` True
    all (\event -> memoryEventCycle event `mod` 3 == 0)
      [event | event <- memoryEvents result, memoryEventOperation event `elem` [ReadRequest,WriteRequest]] `shouldBe` True
    memoryRunStatus result `shouldBe` Completed
  it "distinguishes budget exhaustion, empty completion and invalid words" $ do
    let scenario = TrafficScenario "zero" 1 1 1 1 1 0
    result <- expectRight (simulateMemory defaultMemoryConfig scenario kernel [1])
    memoryRunStatus result `shouldBe` CycleLimit
    memoryOutput result `shouldBe` [Nothing]
    memoryEvents result `shouldBe` []
    empty <- expectRight (simulateMemory defaultMemoryConfig scenario kernel [])
    memoryRunStatus empty `shouldBe` Completed
    simulateMemory defaultMemoryConfig scenario kernel [256] `shouldSatisfy` isLeft
    simulateMemory defaultMemoryConfig scenario kernel [-1] `shouldSatisfy` isLeft
    simulateMemory (MemoryConfig 1 1) scenario kernel [0,1] `shouldSatisfy` isLeft
  itWithTools ["iverilog", "vvp"] "replays backpressure, invalid commands and reset against emitted HDL" $ withTempDir $ \dir -> do
    design <- expectRight (generateMemoryAccelerator (MemoryConfig 3 8) kernel)
    Text.writeFile (dir </> "design.sv") (memorySystemVerilog design)
    bench <- Text.readFile "test/hdl/memory_tb.sv"
    Text.writeFile (dir </> "bench.sv") bench
    (compiled, _, compileError) <- runTool dir "iverilog" ["-g2012", "-s", "memory_tb", "-o", "sim", "design.sv", "bench.sv"]
    if compiled /= ExitSuccess then expectationFailure (Text.unpack compileError) else pure ()
    (ran, output, runError) <- runTool dir "vvp" ["sim"]
    if ran /= ExitSuccess then expectationFailure (Text.unpack (output <> runError)) else pure ()
    output `shouldSatisfy` Text.isInfixOf "MEMORY-PASS"

expectRight :: Show e => Either e a -> IO a
expectRight (Right value) = pure value
expectRight (Left err) = expectationFailure (show err) >> fail "unexpected error"

kernel :: NModule
kernel = NModule
  { nmName = "memorykernel"
  , nmDomain = sysDomain
  , nmInputs = [("word", TBitVec 8)]
  , nmOutputs = [NOutput "result" (TBitVec 8) (AVar "inc")]
  , nmBinds = [NBind "inc" (TBitVec 8) (NPrim BvAdd [AVar "word", ALit (VBV 8 1)])]
  , nmCertificate = testCertificate "memory_kernel"
  }
