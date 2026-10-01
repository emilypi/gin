-- | Tests for the SystemVerilog-2017 backend: the Verilog-family suite
-- from "Gin.Backend.VerilogSpec", run with the SystemVerilog tools and
-- golden files, plus dialect checks.
module Gin.Backend.SystemVerilogSpec (spec) where

import Gin.Backend.SystemVerilog (systemVerilog)
import Gin.Backend.Types (Backend (..), Target (..))
import Gin.Backend.VerilogSpec (Flavour (..), allNetlists, designWords, familySpec)
import Test.Hspec

systemVerilogFlavour :: Flavour
systemVerilogFlavour =
  Flavour
    { flBackend = systemVerilog
    , flTag = "sv"
    , flGoldenDir = "systemverilog"
    , flIcarusStd = "-g2012"
    , flVerilatorLanguage = "1800-2017"
    }

spec :: Spec
spec = do
  describe "backend" $
    it "targets SystemVerilog with the sv extension" $ do
      backendTarget systemVerilog `shouldBe` SystemVerilog
      backendFileExt systemVerilog `shouldBe` "sv"
  familySpec systemVerilogFlavour
  describe "dialect" $
    it "declares signals as logic and registers in always_ff, never wire or reg" $ do
      let ws = concatMap (designWords . backendRender systemVerilog) allNetlists
      filter (`elem` ["wire", "reg", "always"]) ws `shouldBe` []
      filter (== "logic") ws `shouldSatisfy` (not . null)
      filter (== "always_ff") ws `shouldSatisfy` (not . null)
