-- | Shared test helpers.
module Gin.TestUtil
  ( goldenText
  , toolAvailable
  , itWithTools
  , runTool
  , withTempDir
  , tshow
  , ifE
  , moduleOperands
  , declOperands
  ) where

import Control.Monad (unless, when)
import Data.Maybe (isJust)
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Text.IO qualified as Text
import Gin.Core.Syntax (Expr (..))
import Gin.Netlist.Types (Decl (..), Module (..), Operand, Output (..), exprOperands)
import System.Directory (createDirectoryIfMissing, doesFileExist, findExecutable)
import System.Environment (lookupEnv)
import System.Exit (ExitCode (..))
import System.FilePath (takeDirectory, (</>))
import System.IO.Temp (withSystemTempDirectory)
import System.Process (CreateProcess (..), proc, readCreateProcessWithExitCode)
import System.Timeout (timeout)
import Test.Hspec (Expectation, SpecWith, expectationFailure, it, pendingWith, shouldBe)

-- | Compare against @test/golden/<rel>@. With @GIN_ACCEPT=1@ in the
-- environment, (re)write the golden file instead. A missing golden file
-- is a failure unless accepting.
goldenText :: FilePath -> Text -> Expectation
goldenText rel actual = do
  let file = "test" </> "golden" </> rel
  accept <- (== Just "1") <$> lookupEnv "GIN_ACCEPT"
  exists <- doesFileExist file
  if accept
    then do
      createDirectoryIfMissing True (takeDirectory file)
      Text.writeFile file actual
    else do
      unless exists $
        expectationFailure ("missing golden file " <> file <> " (rerun with GIN_ACCEPT=1)")
      expected <- Text.readFile file
      actual `shouldBe` expected

toolAvailable :: String -> IO Bool
toolAvailable t = isJust <$> findExecutable t

-- | A test that needs external tools. Missing tools make it pending, or a
-- failure when @GIN_REQUIRE_TOOLS=1@ (set this in CI).
itWithTools :: [String] -> String -> Expectation -> SpecWith ()
itWithTools tools name body = it name $ do
  missing <- filterMissing tools
  required <- (== Just "1") <$> lookupEnv "GIN_REQUIRE_TOOLS"
  case missing of
    [] -> body
    ms -> do
      let msg = "missing tools: " <> unwords ms
      when required (expectationFailure msg)
      pendingWith msg
  where
    filterMissing = fmap concat . traverse (\t -> (\ok -> [t | not ok]) <$> toolAvailable t)

-- | Run a tool (no shell) in a working directory with a 300 s limit;
-- returns exit code, stdout and stderr. A timeout yields @ExitFailure
-- 124@ and a message on stderr.
runTool :: FilePath -> String -> [String] -> IO (ExitCode, Text, Text)
runTool cwd' exe args =
  timeout (300 * 1000000) (readCreateProcessWithExitCode (proc exe args) {cwd = Just cwd'} "")
    >>= \case
      Just (code, out, err) -> pure (code, Text.pack out, Text.pack err)
      Nothing -> pure (ExitFailure 124, "", Text.pack ("timeout: " <> exe))

withTempDir :: (FilePath -> IO a) -> IO a
withTempDir = withSystemTempDirectory "gin-test"

tshow :: (Show a) => a -> Text
tshow = Text.pack . show

-- | The two-way @if c then t else e@.
ifE :: Expr ty name -> Expr ty name -> Expr ty name -> Expr ty name
ifE c t e = EIf [(c, t)] e

-- | Every operand a module reads: output drivers, then each declaration's.
moduleOperands :: Module -> [Operand]
moduleOperands m = fmap outDriver (modOutputs m) <> concatMap declOperands (modDecls m)

declOperands :: Decl -> [Operand]
declOperands = \case
  DReg _ _ o -> [o]
  DAssign _ e -> exprOperands e
