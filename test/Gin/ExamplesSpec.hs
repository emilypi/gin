-- | Sanity checks on the shared fixtures themselves, so a broken fixture
-- fails here rather than in every suite that uses it.
module Gin.ExamplesSpec (spec) where

import Data.List (nub)
import Data.Maybe (isNothing)
import Data.Text qualified as Text
import Gin.Core.Normal
import Gin.Core.Syntax
import Gin.Examples
import Gin.Netlist.Types
import Gin.Vectors (Cycle (..), Vectors (..))
import Test.Hspec

netlists :: [(String, Module)]
netlists = [("counter", counterNetlist), ("mac", macNetlist), ("detector", detectorNetlist)]

normals :: [(String, NModule)]
normals = [("counter", counterNormal), ("mac", macNormal), ("detector", detectorNormal)]

vectors :: [(String, Vectors)]
vectors = [("counter", counterVectors), ("mac", macVectors), ("detector", detectorVectors)]

moduleIdents :: Module -> [Ident]
moduleIdents m =
  modName m
    : modClock m
    : modReset m
    : fmap netName (modInputs m <> fmap outNet (modOutputs m) <> fmap declNet (modDecls m))

operands :: Module -> [Operand]
operands m = fmap outDriver (modOutputs m) <> concatMap declOperands (modDecls m)
  where
    declOperands = \case
      DReg _ _ o -> [o]
      DAssign _ e -> exprOperands e
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

spec :: Spec
spec = do
  describe "netlist fixtures" $ for_ netlists $ \(name, m) -> do
    it (name <> ": every identifier is legal") $
      filter (not . isLegalIdent . unIdent) (moduleIdents m) `shouldBe` []
    it (name <> ": identifiers are case-insensitively distinct") $ do
      let names = fmap (Text.toLower . unIdent) (moduleIdents m)
      length (nub names) `shouldBe` length names
    it (name <> ": every reference names an input or a declared net") $
      [i | ORef i <- operands m, isNothing (operandType m (ORef i))] `shouldBe` []
  describe "normal-form fixtures" $ for_ normals $ \(name, nm) ->
    it (name <> ": bound names are unique and distinct from inputs") $ do
      let names = fmap fst (nmInputs nm) <> fmap nbName (nmBinds nm)
      length (nub names) `shouldBe` length names
  describe "vector fixtures" $ for_ vectors $ \(name, vs) ->
    it (name <> ": every row matches the port types") $
      [ c
      | c <- vecCycles vs
      , fmap valueTy (cycInputs c) /= fmap portTy (vecInputs vs)
          || fmap valueTy (cycOutputs c) /= fmap portTy (vecOutputs vs)
      ]
        `shouldBe` []
  where
    for_ xs f = mapM_ f xs
