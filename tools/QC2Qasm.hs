module Main (main) where

import System.Environment (getArgs)
import System.FilePath (takeExtension, takeBaseName)
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
  "USAGE: qc2qasm <circuit>.qc",
  "",
  "qc2qasm <circuit>.qc produces a QASM gate declaration for the given .qc circuit."
  ]

parseArgs :: [String] -> IO ()
parseArgs []                   = printHelp
parseArgs (x:_)
  | takeExtension x == ".qc"   = B.readFile x >>= go (takeBaseName x)
  | x == "-h" || x == "--help" = printHelp
  | otherwise                  = do 
      putStrLn ("Invalid argument \"" ++ x ++ "\"") 
      printHelp
  where go fname str = either print emit (liftM (fromDotQC fname) $ parseDotQC str)

main :: IO ()
main = getArgs >>= parseArgs
