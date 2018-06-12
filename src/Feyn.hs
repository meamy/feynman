module Main (main) where

import System.Environment

import Data.List

import Data.Set (Set)
import qualified Data.Set as Set

import Control.Monad

import Frontend.DotQC
import Optimization.PhaseFold
import Optimization.TPar
import Verification.SOP
import Core (Primitive(CNOT, T, Tinv), ID)

import Benchmarks

{- Toolkit passes -}

type DotQCPass = DotQC -> Either String DotQC

trivPass :: DotQCPass
trivPass = Right

inlinePass :: DotQCPass
inlinePass = Right . inlineDotQC

optimizationPass :: ([ID] -> [ID] -> [Primitive] -> [Primitive]) -> DotQCPass
optimizationPass f qc = Right $ qc { decls = map applyOpt $ decls qc }
  where applyOpt decl = decl { body = wrap (f (qubits qc ++ params decl) (inp ++ params decl)) $ body decl }
        wrap g        = fromCliffordT . g . toCliffordT
        inp           = Set.toList $ inputs qc

phasefoldPass :: DotQCPass
phasefoldPass = optimizationPass phaseFold

tparPass :: DotQCPass
tparPass = optimizationPass tpar

cnotminPass :: DotQCPass
cnotminPass = optimizationPass minCNOT

equivalenceCheck :: DotQC -> DotQC -> Either String DotQC
equivalenceCheck qc qc' =
  let gatelist      = toCliffordT . toGatelist $ qc
      gatelist'     = toCliffordT . toGatelist $ qc'
      primaryInputs = Set.toList $ inputs qc
      result        = validate (union (qubits qc) (qubits qc')) primaryInputs gatelist gatelist'
  in
    case (inputs qc == inputs qc', result) of
      (False, _)    -> Left $ "Failed to verify: different inputs"
      (_, Just sop) -> Left $ "Failed to verify: " ++ show sop
      _             -> Right qc'

{- Main program -}

run :: DotQCPass -> Bool -> String -> Either String [String]
run pass verify src = do
  qc  <- printErr $ parseDotQC src
  qc' <- pass qc
  if verify
    then equivalenceCheck qc qc'
    else Right qc'
  return $ ["# Original:"] ++
           map ("#   " ++) (showCliffordTStats qc) ++
           ["# Result:"] ++
           map ("#   " ++) (showCliffordTStats qc') ++
           [show qc']
  where printErr (Left l)  = Left $ show l
        printErr (Right r) = Right r

parseArgs :: DotQCPass -> Bool -> [String] -> IO ()
parseArgs pass verify []     = return ()
parseArgs pass verify (x:xs) = case x of
  "-inline"    -> parseArgs (pass >=> inlinePass) verify xs
  "-phasefold" -> parseArgs (pass >=> phasefoldPass) verify xs
  "-cnotmin"   -> parseArgs (pass >=> cnotminPass) verify xs
  "-tpar"      -> parseArgs (pass >=> tparPass) verify xs
  "-verify"    -> parseArgs pass True xs
  "VerBench"   -> runVertest cnotminPass equivalenceCheck benchmarksMedium
  "VerAlg"     -> runVerSuite
  "Small"      -> runBenchmarks pass benchmarksSmall
  "Med"        -> runBenchmarks pass benchmarksMedium
  "All"        -> runBenchmarks pass benchmarksAll
  f            -> do
    src <- readFile f
    case run pass verify src of
      Left err  -> putStrLn $ "ERROR: " ++ err
      Right res -> mapM_ putStrLn res

main :: IO ()
main = do
  putStrLn "# Feynman -- quantum circuit toolkit"
  putStrLn "# Written by Matthew Amy"
  getArgs >>= parseArgs trivPass False
