-- |
-- Module       : Main
-- Copyright    : (c) 2026 Emily Pillmore
-- License      : BSD-3-Clause
--
-- Maintainer   : Emily Pillmore <emilypi@cohomolo.gy>
-- Stability    : experimental
-- Portability  : non-portable (GHC extensions)
module Main (main) where

import Gin.Driver (runCli)
import System.Environment (getArgs)
import System.Exit (exitWith)

main :: IO ()
main = getArgs >>= runCli >>= exitWith
