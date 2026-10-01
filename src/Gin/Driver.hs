-- | Runs the compiler pipeline and implements the CLI commands.
module Gin.Driver
  ( runCli
  ) where

import System.Exit (ExitCode)

-- | Parse the arguments and run one command. Never calls 'exitWith';
-- returns 'ExitSuccess', @ExitFailure 1@ for a failed check or compile,
-- or @ExitFailure 2@ for a usage error.
runCli :: [String] -> IO ExitCode
runCli = error "not yet implemented: runCli"
