module Main (main) where

import System.Environment

import Data.List

import Data.Set (Set)
import qualified Data.Set as Set

import DotQC
--import TPar
import PhaseFold

testPhaseFold (DotQC q i o decls) = do
  (Decl _ _ body) <- find (\(Decl n _ _) -> n == "main") decls
  let gates = toCliffordT body
  return $ runAnalysis q (Set.toList i) gates

main :: IO ()
main = do
  putStrLn "Feyn -- copywrite 2016 Matthew Amy"
  (f:xs) <- getArgs
  s      <- readFile f
  case parseDotQC s of
    Left err -> putStrLn $ "Error parsing input: " ++ show err
    Right circuit -> do
      print circuit
      print $ testPhaseFold circuit
