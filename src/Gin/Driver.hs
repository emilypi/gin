-- | Runs the compiler pipeline and implements the CLI commands.
module Gin.Driver
  ( runCli
  , runCliWith
  ) where

import System.Environment (getEnvironment)
import System.Exit (ExitCode)

-- | Parse the arguments and run one command. Never calls 'exitWith';
-- returns 'ExitSuccess', @ExitFailure 1@ for a failed check or compile,
-- or @ExitFailure 2@ for a usage error.
runCli :: [String] -> IO ExitCode
runCli args = getEnvironment >>= \env -> runCliWith env args

-- | 'runCli' with an explicit environment. External tools are looked up
-- in the directories of the environment's @PATH@ and spawned by absolute
-- path with that environment, so tests can substitute or hide tools
-- without touching the process environment.
runCliWith :: [(String, String)] -> [String] -> IO ExitCode
runCliWith = error "not yet implemented: runCliWith"
