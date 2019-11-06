{-# LANGUAGE TupleSections #-}
module Main (main) where

import Feynman.Core (Primitive(CNOT, T, Tinv), ID)
import Feynman.Frontend.DotQC hiding (showStats)
import Feynman.Frontend.OpenQASM.Lexer (lexer)
import Feynman.Frontend.OpenQASM.Syntax (QASM,
                                         prettyPrint,
                                         check,
                                         desugar,
                                         emit,
                                         fromDotQC,
                                         inline,
                                         applyOpt,
                                         showStats)
import Feynman.Frontend.OpenQASM.Parser (parse)
import Feynman.Optimization.PhaseFold
import Feynman.Optimization.TPar
import Feynman.Verification.SOP

import System.Environment

import Data.List

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Map (Map)
import qualified Data.Map as Map

import Control.Monad
import System.Time
import Control.DeepSeq

import Data.ByteString (ByteString)
import qualified Data.ByteString as B

import Benchmarks

{- Toolkit passes -}

data Pass = Triv
          | Inline
          | MCT
          | CT
          | Simplify
          | Phasefold
          | CNOTMin
          | TPar

{- DotQC -}

optimizeDotQC :: ([ID] -> [ID] -> [Primitive] -> [Primitive]) -> DotQC -> DotQC
optimizeDotQC f qc = qc { decls = map applyOpt $ decls qc }
  where applyOpt decl = decl { body = wrap (f (qubits qc ++ params decl) (inp ++ params decl)) $ body decl }
        wrap g        = fromCliffordT . g . toCliffordT
        inp           = Set.toList $ inputs qc

dotQCPass :: Pass -> (DotQC -> DotQC)
dotQCPass pass = case pass of
  Triv      -> id
  Inline    -> inlineDotQC
  MCT       -> expandToffolis
  CT        -> expandAll
  Simplify  -> simplifyDotQC
  Phasefold -> optimizeDotQC phaseFold
  CNOTMin   -> optimizeDotQC minCNOT
  TPar      -> optimizeDotQC tpar

equivalenceCheckDotQC :: DotQC -> DotQC -> Either String DotQC
equivalenceCheckDotQC qc qc' =
  let gatelist      = toCliffordT . toGatelist $ qc
      gatelist'     = toCliffordT . toGatelist $ qc'
      primaryInputs = Set.toList $ inputs qc
      result        = validateIsometry False (union (qubits qc) (qubits qc')) primaryInputs gatelist gatelist'
  in
    case (inputs qc == inputs qc', result) of
      (False, _)    -> Left $ "Failed to verify: different inputs"
      (_, Just sop) -> Left $ "Failed to verify: " ++ show sop
      _             -> Right qc'

runDotQC :: [Pass] -> Bool -> String -> ByteString -> IO ()
runDotQC passes verify fname src = do
  TOD starts startp <- getClockTime
  TOD ends endp     <- parseAndPass `seq` getClockTime
  case parseAndPass of
    Left err        -> putStrLn $ "ERROR: " ++ err
    Right (qc, qc') -> do
      let time = (fromIntegral $ ends - starts) * 1000 + (fromIntegral $ endp - startp) / 10^9
      putStrLn $ "# Feynman -- quantum circuit toolkit"
      putStrLn $ "# Original (" ++ fname ++ "):"
      mapM_ putStrLn . map ("#   " ++) $ showCliffordTStats qc
      putStrLn $ "# Result (" ++ formatFloatN time 3 ++ "ms):"
      mapM_ putStrLn . map ("#   " ++) $ showCliffordTStats qc'
      putStrLn $ show qc'
  where printErr (Left l)  = Left $ show l
        printErr (Right r) = Right r
        parseAndPass = do
          qc  <- printErr $ parseDotQC src
          qc' <- return $ foldr dotQCPass qc passes
          seq (depth $ toGatelist qc') (return ()) -- Nasty solution to strictifying
          when verify . void $ equivalenceCheckDotQC qc qc'
          return (qc, qc')

{- Deprecated transformations for benchmark suites -}
benchPass :: [Pass] -> (DotQC -> Either String DotQC)
benchPass passes = \qc -> Right $ foldr dotQCPass qc passes

benchVerif :: Bool -> Maybe (DotQC -> DotQC -> Either String DotQC)
benchVerif True  = Just equivalenceCheckDotQC
benchVerif False = Nothing

{- QASM -}

qasmPass :: Pass -> (QASM -> QASM)
qasmPass pass = case pass of
  Triv      -> id
  Inline    -> inline
  MCT       -> inline
  CT        -> inline
  Simplify  -> id
  Phasefold -> applyOpt phaseFold
  CNOTMin   -> applyOpt minCNOT
  TPar      -> applyOpt tpar

runQASM :: [Pass] -> Bool -> String -> String -> IO ()
runQASM passes verify fname src = do
  TOD starts startp <- getClockTime
  TOD ends endp     <- parseAndPass `seq` getClockTime
  case parseAndPass of
    Left err        -> putStrLn $ "ERROR: " ++ err
    Right (qasm, qasm') -> do
      let time = (fromIntegral $ ends - starts) * 1000 + (fromIntegral $ endp - startp) / 10^9
      putStrLn $ "// Feynman -- quantum circuit toolkit"
      putStrLn $ "// Original (" ++ fname ++ "):"
      mapM_ putStrLn . map ("//   " ++) $ showStats qasm
      putStrLn $ "// Result (" ++ formatFloatN time 3 ++ "ms):"
      mapM_ putStrLn . map ("//   " ++) $ showStats qasm'
      emit qasm'
  where printErr (Left l)  = Left $ show l
        printErr (Right r) = Right r
        parseAndPass = do
          let qasm   = parse . lexer $ src
          symtab <- check qasm
          let qasm'  = desugar symtab qasm -- For correct gate counts
          qasm'' <- return $ foldr qasmPass qasm' passes
          return (qasm', qasm'')

{- Main program -}

printHelp :: IO ()
printHelp = mapM_ putStrLn lines
  where lines = [
          "Feynman -- quantum circuit toolkit",
          "Written by Matthew Amy",
          "",
          "Run with feyn [passes] (<circuit>.(qc | qasm) | Small | Med | All)",
          "",
          "Transformation passes:",
          "  -inline\tInline all sub-circuits",
          "  -mctExpand\tExpand all MCT gates using |0>-initialized ancillas",
          "  -toCliffordT\tExpand all gates to Clifford+T gates",
          "",
          "Optimization passes:",
          "  -simplify\tBasic gate-cancellation pass",
          "  -phasefold\tMerges phase gates according to the circuit's phase polynomial",
          "  -tpar\t\tPhase folding + T-parallelization algorithm from [AMM14]",
          "  -cnotmin\tPhase folding + CNOT-minimization algorithm from [AAM17]",
          "  -O2\t\t**Standard strategy** Phase folding + simplify",
          "",
          "Verification passes:",
          "  -verify\tPerform verification algorithm of [A18] after all passes",
          "",
          "E.g. \"feyn -verify -inline -cnotmin -simplify circuit.qc\" will first inline the circuit,",
          "       then optimize CNOTs, followed by a gate cancellation pass and finally verify the result",
          "",
          "WARNING: Using \"-verify\" with \"All\" may crash your computer without first setting",
          "         user-level memory limits. Use with caution"
          ]
          

parseArgs :: [Pass] -> Bool -> [String] -> IO ()
parseArgs passes verify []     = printHelp
parseArgs passes verify (x:xs) = case x of
  "-h"           -> printHelp
  "-inline"      -> parseArgs (Inline:passes) verify xs
  "-mctExpand"   -> parseArgs (MCT:passes) verify xs
  "-toCliffordT" -> parseArgs (CT:passes) verify xs
  "-simplify"    -> parseArgs (Simplify:passes) verify xs
  "-phasefold"   -> parseArgs (Phasefold:Simplify:passes) verify xs
  "-cnotmin"     -> parseArgs (CNOTMin:Simplify:passes) verify xs
  "-tpar"        -> parseArgs (TPar:Simplify:passes) verify xs
  "-O2"          -> parseArgs (Simplify:Phasefold:Simplify:passes) verify xs
  "-verify"      -> parseArgs passes True xs
  "VerBench"     -> runBenchmarks (benchPass [CNOTMin,Simplify]) (benchVerif True) benchmarksMedium
  "VerAlg"       -> runVerSuite
  "Small"        -> runBenchmarks (benchPass passes) (benchVerif verify) benchmarksSmall
  "Med"          -> runBenchmarks (benchPass passes) (benchVerif verify) benchmarksMedium
  "All"          -> runBenchmarks (benchPass passes) (benchVerif verify) benchmarksAll
  f | (drop (length f - 3) f) == ".qc" -> B.readFile f >>= runDotQC passes verify f
  f | (drop (length f - 5) f) == ".qasm" -> readFile f >>= runQASM passes verify f
  f | otherwise -> putStrLn ("Unrecognized option \"" ++ f ++ "\"") >> printHelp

main :: IO ()
main = getArgs >>= parseArgs [] False
