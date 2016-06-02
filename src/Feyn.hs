module Main (main) where

import System.Environment

import DotQC
--import TPar
import PhaseFold

main :: IO ()
main = do
  putStrLn "Feyn -- copywrite 2016 Matthew Amy"
  (f:xs) <- getArgs
  s      <- readFile f
  case parseDotQC s of
    Left err -> putStrLn $ "Error parsing input: " ++ show err
    Right circuit -> print circuit
