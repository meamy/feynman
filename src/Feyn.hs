module Main (main) where

import System.Environment

import Data.List

import Data.Set (Set)
import qualified Data.Set as Set

import Control.Monad

import DotQC
import PhaseFold
import TPar
import Syntax (Primitive(CNOT, T, Tinv))

import Tests

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
        gates' = gtpar cnotMinGray q (Set.toList i) gates
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

parseArgs :: ((DotQC, DotQC) -> Either String (DotQC, DotQC)) -> [String] -> IO ()
parseArgs pass []     = return ()
parseArgs pass (x:xs) = case x of
  "-phasefold" -> parseArgs (pass >=> runPhaseFold) xs
  "-cnotmin"   -> parseArgs (pass >=> runCnotMin) xs
  "-tpar"      -> parseArgs (pass >=> runTpar) xs
  "Small"      -> runBenchmarks pass benchmarksSmall
  "Med"        -> runBenchmarks pass benchmarksMedium
  "All"        -> runBenchmarks pass benchmarksAll
  f            -> do
    s <- readFile f
    case printErr (parseDotQC s) >>= (\c -> pass (c, c)) of
      Left err      -> putStrLn err
      Right (c, c') -> do
        putStrLn $ "# Original circuit statistics:"
        putStrLn $ "#   " ++ show (countGates c)
        putStrLn $ "# Optimized circuit statistics:"
        putStrLn $ "#   " ++ show (countGates c')
        print c'
  where printErr res = case res of
          Left err -> Left $ show err
          Right x  -> Right x

main :: IO ()
main = do
  putStrLn "# Feyn -- copyright 2016 Matthew Amy"
  getArgs >>= parseArgs return
