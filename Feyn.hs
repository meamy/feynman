module Main (main) where

import System.Environment

import Syntax

main :: IO ()
main = do
  putStrLn "Feyn -- copywrite 2016 Matthew Amy"
  (f:xs) <- getArgs
  s      <- readFile f
  case parseQC s of
    Left err -> putStrLn $ "Error parsing input: " ++ show err
    Right circuit -> printCircIR circuit
