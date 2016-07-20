module Main (main) where

import System.Environment

import Data.List

import Data.Set (Set)
import qualified Data.Set as Set

import DotQC
import PhaseFold
import TPar

testPhaseFold qc@(DotQC q i o decs) = do
  (Decl n p body) <- find (\(Decl n _ _) -> n == "main") decs
  let gates  = toCliffordT body
  let gates' = phasePhold q (Set.toList i) gates
  let main   = Decl n p $ fromCliffordT gates'
  Just $ qc { decls = map (\dec@(Decl n _ _) -> if n == "main" then main else dec) decs }
      
testCnotMin qc@(DotQC q i o decs) = do
  (Decl n p body) <- find (\(Decl n _ _) -> n == "main") decs
  let gates  = toCliffordT body
  let gates' = gtpar cnotMinMore q (Set.toList i) gates
  let main   = Decl n p $ fromCliffordT gates'
  Just $ qc { decls = map (\dec@(Decl n _ _) -> if n == "main" then main else dec) decs }

main :: IO ()
main = do
  putStrLn "# Feyn -- copywrite 2016 Matthew Amy"
  (f:xs) <- getArgs
  s      <- readFile f
  case parseDotQC s of
    Left err -> putStrLn $ "Error parsing input: " ++ show err
    Right circuit -> do
      --print circuit
      print $ testCnotMin circuit
