module Main (main) where

import System.Environment (getArgs)
import Data.Either (either)
import Control.Monad (liftM)

import qualified Data.ByteString as B

import Feynman.Frontend.DotQC (parseDotQC)
import Feynman.Frontend.OpenQASM.Syntax (fromDotQC, emit)

printHelp :: IO ()
printHelp = mapM_ putStrLn [
  "qc2qasm -- .qc to openQASM circuit converter",
  "Written by Matthew Amy",
  "",
  "USAGE: qc2qasm <circuit>.qc"
  ]

parseArgs :: [String] -> IO ()
parseArgs []     = printHelp
parseArgs (x:_)
  | (drop (length x - 3) x) == ".qc" = B.readFile x >>= go
  | otherwise = putStrLn ("Invalid argument \"" ++ x ++ "\"") >> printHelp
  where go str = either print emit (liftM fromDotQC $ parseDotQC str)

main :: IO ()
main = getArgs >>= parseArgs
