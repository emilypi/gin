-- | Shared test helpers. Owner: p1 (frozen; extend only via replan).
module Gin.TestUtil
  ( goldenText
  , toolAvailable
  , itWithTools
  , runTool
  , withTempDir
  ) where

import Control.Monad (unless, when)
import Data.Maybe (isJust)
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Text.IO qualified as Text
import System.Directory (createDirectoryIfMissing, doesFileExist, findExecutable)
import System.Environment (lookupEnv)
import System.Exit (ExitCode)
import System.FilePath (takeDirectory, (</>))
import System.IO.Temp (withSystemTempDirectory)
import System.Process (CreateProcess (..), proc, readCreateProcessWithExitCode)
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
-- failure when @GIN_REQUIRE_TOOLS=1@ (set by every verify gate, C-6).
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

-- | Run a tool (no shell) in a working directory; returns exit code,
-- stdout and stderr.
runTool :: FilePath -> String -> [String] -> IO (ExitCode, Text, Text)
runTool cwd' exe args = do
  (code, out, err) <- readCreateProcessWithExitCode (proc exe args) {cwd = Just cwd'} ""
  pure (code, Text.pack out, Text.pack err)

withTempDir :: (FilePath -> IO a) -> IO a
withTempDir = withSystemTempDirectory "gin-test"
