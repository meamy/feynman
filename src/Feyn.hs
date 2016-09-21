module Main (main) where

import System.Environment

import Data.List

import Data.Set (Set)
import qualified Data.Set as Set

import DotQC
import PhaseFold
import TPar
import Syntax (Primitive(CNOT, T, Tinv))

printJust Nothing  = print ""
printJust (Just x) = print x

printStats xs =
  let cnots = length $ filter (\x -> case x of CNOT _ _ -> True; _ -> False) xs
      ts    = length $ filter (\x -> case x of T _ -> True; Tinv _ -> True; _ -> False) xs
  in do
    putStrLn $ "# CNOT-count: " ++ show cnots
    putStrLn $ "# T-count:    " ++ show ts


testPhaseFold qc@(DotQC q i o decs) = case find (\(Decl n _ _) -> n == "main") decs of
  Nothing -> return Nothing
  Just (Decl n p body) ->
    let gates  = toCliffordT body
        gates' = phaseFold q (Set.toList i) gates
        main   = Decl n p $ fromCliffordT gates'
        ret    = qc { decls = map (\dec@(Decl n _ _) -> if n == "main" then main else dec) decs }
    in do
      putStrLn "# Original circuit statistics:"
      printStats gates
      putStrLn "# Optimized circuit statistics:"
      printStats gates'
      print ret
      return $ Just ret
      
{-testCnotMin qc@(DotQC q i o decs) = do
  (Decl n p body) <- find (\(Decl n _ _) -> n == "main") decs
  let gates  = toCliffordT body
  let gates' = gtpar cnotMinMore q (Set.toList i) gates
  let main   = Decl n p $ fromCliffordT gates'
  Just $ qc { decls = map (\dec@(Decl n _ _) -> if n == "main" then main else dec) decs }-}

testCnotMin qc@(DotQC q i o decs) = case find (\(Decl n _ _) -> n == "main") decs of
  Nothing -> return Nothing
  Just (Decl n p body) ->
    let gates  = toCliffordT body
        gates' = gtpar cnotMinMost q (Set.toList i) gates
        main   = Decl n p $ fromCliffordT gates'
        ret    = qc { decls = map (\dec@(Decl n _ _) -> if n == "main" then main else dec) decs }
    in do
      putStrLn "# Original circuit statistics:"
      printStats gates
      putStrLn "# Optimized circuit statistics:"
      printStats gates'
      print ret
      return $ Just ret

testTpar qc@(DotQC q i o decs) = case find (\(Decl n _ _) -> n == "main") decs of
  Nothing -> return Nothing
  Just (Decl n p body) ->
    let gates  = toCliffordT body
        gates' = gtpar tparMore q (Set.toList i) gates
        main   = Decl n p $ fromCliffordT gates'
        ret    = qc { decls = map (\dec@(Decl n _ _) -> if n == "main" then main else dec) decs }
    in do
      putStrLn "# Original circuit statistics:"
      printStats gates
      putStrLn "# Optimized circuit statistics:"
      printStats gates'
      print ret
      return $ Just ret

main :: IO ()
main = do
  putStrLn "# Feyn -- copywrite 2016 Matthew Amy"
  (f:xs) <- getArgs
  s      <- readFile f
  case parseDotQC s of
    Left err -> putStrLn $ "Error parsing input: " ++ show err
    Right circuit -> testPhaseFold circuit >> return ()
