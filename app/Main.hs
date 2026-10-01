module Main (main) where

import Gin.Driver (runCli)
import System.Environment (getArgs)
import System.Exit (exitWith)

main :: IO ()
main = getArgs >>= runCli >>= exitWith
