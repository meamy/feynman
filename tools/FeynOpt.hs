{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant bracket" #-}
module Main (main) where

import Feynman.Core (Primitive, ID, expandCNOT)
import Feynman.Frontend.DotQC hiding (showStats)
import Feynman.Frontend.OpenQASM.Lexer (lexer)
import Feynman.Frontend.OpenQASM.Syntax (QASM,
                                         check,
                                         desugar,
                                         emit,
                                         inline,
                                         applyOpt,
                                         showStats)
import Feynman.Frontend.OpenQASM.Parser (parse)
import Feynman.Optimization.PhaseFold
import Feynman.Optimization.StateFold
import Feynman.Optimization.TPar
import Feynman.Optimization.Clifford
import Feynman.Synthesis.Pathsum.Unitary hiding (MCT)
import Feynman.Verification.Symbolic

import System.Environment (getArgs)
import System.CPUTime     (getCPUTime)

import Data.List
import qualified Data.Set as Set

import Control.Monad

import Data.ByteString (ByteString)
import qualified Data.ByteString as B

import Benchmarks (runBenchmarks,
                   benchmarksSmall,
                   benchmarksMedium,
                   benchmarksAll,
                   benchmarkFolder,
                   formatFloatN)


{- Toolkit passes -}

data Pass = Triv
          | Inline
          | MCT
          | CT
          | Simplify
          | Phasefold
          | Statefold Int
          | CNOTMin
          | TPar
          | Cliff
          | CZ
          | Decompile

{- DotQC -}

optimizeDotQC :: ([ID] -> [ID] -> [Primitive] -> [Primitive]) -> DotQC -> DotQC
optimizeDotQC f qc = qc { decls = map go $ decls qc }
  where go decl =
          let circuitQubits = qubits qc ++ params decl
              circuitInputs = (Set.toList $ inputs qc) ++ params decl
              wrap g        = fromCliffordT . g . toCliffordT
          in
            decl { body = wrap (f circuitQubits circuitQubits) $ body decl }

decompileDotQC :: DotQC -> DotQC
decompileDotQC qc = qc { decls = map go $ decls qc }
  where go decl =
          let circuitQubits  = qubits qc ++ params decl
              circuitInputs  = (Set.toList $ inputs qc) ++ params decl
              resynthesize c = case resynthesizeCircuit $ toCliffordT c of
                Nothing -> c
                Just c' -> fromExtractionBasis c'
          in
            decl { body = resynthesize $ body decl }

dotQCPass :: Pass -> (DotQC -> DotQC)
dotQCPass pass = case pass of
  Triv        -> id
  Inline      -> inlineDotQC
  MCT         -> expandToffolis
  CT          -> expandAll
  Simplify    -> simplifyDotQC
  Phasefold   -> optimizeDotQC phaseFold
  Statefold d -> optimizeDotQC (stateFold d)
  CNOTMin     -> optimizeDotQC minCNOT
  TPar        -> optimizeDotQC tpar
  Cliff       -> optimizeDotQC (\_ _ -> simplifyCliffords)
  CZ          -> optimizeDotQC (\_ _ -> expandCNOT)
  Decompile   -> decompileDotQC

equivalenceCheckDotQC :: DotQC -> DotQC -> Either String DotQC
equivalenceCheckDotQC qc qc' =
  let circ    = toCliffordT . toGatelist $ qc
      circ'   = toCliffordT . toGatelist $ qc'
      vars    = union (qubits qc) (qubits qc')
      ins     = Set.toList $ inputs qc
      result  = validate False vars ins circ circ'
  in
    case (inputs qc == inputs qc', result) of
      (False, _)            -> Left $ "Circuits not equivalent (different inputs)"
      (_, NotIdentity ce)   -> Left $ "Circuits not equivalent (" ++ ce ++ ")"
      (_, Inconclusive sop) -> Left $ "Failed to verify: \n  " ++ show sop
      _                     -> Right qc'

runDotQC :: [Pass] -> Bool -> String -> ByteString -> IO ()
runDotQC passes verify fname src = do
  start <- getCPUTime
  end   <- parseAndPass `seq` getCPUTime
  case parseAndPass of
    Left err        -> putStrLn $ "ERROR: " ++ err
    Right (qc, qc') -> do
      let time = (fromIntegral $ end - start) / 10^9
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

qasmPass :: Bool -> Pass -> (QASM -> QASM)
qasmPass pureCircuit pass = case pass of
  Triv        -> id
  Inline      -> inline
  MCT         -> inline
  CT          -> inline
  Simplify    -> id
  Phasefold   -> applyOpt phaseFold pureCircuit
  Statefold d -> applyOpt (stateFold d) pureCircuit
  CNOTMin     -> applyOpt minCNOT pureCircuit
  TPar        -> applyOpt tpar pureCircuit
  Cliff       -> applyOpt (\_ _ -> simplifyCliffords) pureCircuit
  CZ          -> applyOpt (\_ _ -> expandCNOT) pureCircuit

runQASM :: [Pass] -> Bool -> Bool -> String -> String -> IO ()
runQASM passes verify pureCircuit fname src = do
  start <- getCPUTime
  end   <- parseAndPass `seq` getCPUTime
  case parseAndPass of
    Left err        -> putStrLn $ "ERROR: " ++ err
    Right (qasm, qasm') -> do
      let time = (fromIntegral $ end - start) / 10^9
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
          qasm'' <- return $ foldr (qasmPass pureCircuit) qasm' passes
          return (qasm', qasm'')

{- QASM3 -}

qasm3Pass :: Bool -> Pass -> (QASM -> QASM)
qasm3Pass pureCircuit pass = case pass of
  Triv        -> id
  Inline      -> inline
  MCT         -> inline
  CT          -> inline
  Simplify    -> id
  Phasefold   -> applyOpt phaseFold pureCircuit
  Statefold d -> applyOpt (stateFold d) pureCircuit
  CNOTMin     -> applyOpt minCNOT pureCircuit
  TPar        -> applyOpt tpar pureCircuit
  Cliff       -> applyOpt (\_ _ -> simplifyCliffords) pureCircuit
  CZ          -> applyOpt (\_ _ -> expandCNOT) pureCircuit

runQASM3 :: [Pass] -> Bool -> Bool -> String -> String -> IO ()
runQASM3 passes verify pureCircuit fname src = do
  start <- getCPUTime
  end   <- parseAndPass `seq` getCPUTime
  case parseAndPass of
    Left err        -> putStrLn $ "ERROR: " ++ err
    Right (qasm, qasm') -> do
      let time = (fromIntegral $ end - start) / 10^9
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
          qasm'' <- return $ foldr (qasmPass pureCircuit) qasm' passes
          return (qasm', qasm'')

{- Main program -}

printHelp :: IO ()
printHelp = mapM_ putStrLn lines
  where lines = [
          "Feynman -- quantum circuit toolkit",
          "Written by Matthew Amy",
          "",
          "Run with feynopt [passes] (<circuit>.(qc | qasm) | Small | Med | All | -benchmarks <path to folder>)",
          "",
          "Options:",
          "  -purecircuit\tPerform qasm passes assuming the initial state (of qubits) is unknown",
          "",
          "Transformation passes:",
          "  -inline\tInline all sub-circuits",
          "  -mctExpand\tExpand all MCT gates using |0>-initialized ancillas",
          "  -toCliffordT\tExpand all gates to Clifford+T gates",
          "",
          "Optimization passes:",
          "  -simplify\tBasic gate-cancellation pass",
          "  -phasefold\tMerges phase gates according to the circuit's phase polynomial",
          "  -statefold d \tSlightly more powerful phase folding",
          "  -tpar\t\tPhase folding + T-parallelization algorithm from [AMM14]",
          "  -cnotmin\tPhase folding + CNOT-minimization algorithm from [AAM17]",
          "  -clifford\t\t Re-synthesize Clifford segments",
          "  -O2\t\t**Standard strategy** Phase folding + simplify",
          "  -O3\t\tPhase folding + state folding + simplify + CNOT minimization",
          "  -O4\t\tPhase folding + state folding + simplify + clifford resynthesis + CNOT min",
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


data Options = Options {passes :: [Pass], verify :: Bool, pureCircuit :: Bool, useQASM3 :: Bool}

defaultOptions = Options {passes = [], verify = False, pureCircuit = False, useQASM3 = False}


parseArgs :: Bool -> Options -> [String] -> IO ()
parseArgs doneSwitches options []     = printHelp
parseArgs doneSwitches options (x:xs) = case x of
  f | doneSwitches -> runFile f
  "-h"           -> printHelp
  "-purecircuit" -> parseArgs doneSwitches options {pureCircuit = True} xs
  "-inline"      -> parseArgs doneSwitches options {passes = Inline:passes options} xs
  "-mctExpand"   -> parseArgs doneSwitches options {passes = MCT:passes options} xs
  "-toCliffordT" -> parseArgs doneSwitches options {passes = CT:passes options} xs
  "-simplify"    -> parseArgs doneSwitches options {passes = Simplify:passes options} xs
  "-phasefold"   -> parseArgs doneSwitches options {passes = Phasefold:passes options} xs
  "-statefold"   -> parseArgs doneSwitches options {passes = (Statefold $ read (head xs)):passes options} (tail xs)
  "-cnotmin"     -> parseArgs doneSwitches options {passes = CNOTMin:passes options} xs
  "-tpar"        -> parseArgs doneSwitches options {passes = TPar:passes options} xs
  "-clifford"    -> parseArgs doneSwitches options {passes = Cliff:passes options} xs
  "-cxcz"        -> parseArgs doneSwitches options {passes = CZ:passes options} xs
  "-decompile"   -> parseArgs doneSwitches options {passes = Decompile:passes options} xs
  "-O2"          -> parseArgs doneSwitches options {passes = o2 ++ passes options} xs
  "-O3"          -> parseArgs doneSwitches options {passes = o3 ++ passes options} xs
  "-O4"          -> parseArgs doneSwitches options {passes = o4 ++ passes options} xs
  "-verify"      -> parseArgs doneSwitches options {verify = True} xs
  "-benchmarks"  -> benchmarkFolder (head xs) >>= runBenchmarks (benchPass $ passes options) (benchVerif $ verify options)
  "-qasm3"       -> parseArgs doneSwitches options {useQASM3 = True} xs
  "--"           -> parseArgs True options xs
  "VerBench"     -> runBenchmarks (benchPass [CNOTMin,Simplify]) (benchVerif True) benchmarksMedium
--  "VerAlg"       -> runVerSuite
  "Small"        -> runBenchmarks (benchPass $ passes options) (benchVerif $ verify options) benchmarksSmall
  "Med"          -> runBenchmarks (benchPass $ passes options) (benchVerif $ verify options) benchmarksMedium
  "All"          -> runBenchmarks (benchPass $ passes options) (benchVerif $ verify options) benchmarksAll
  f | ((drop (length f - 3) f) == ".qc") || ((drop (length f - 5) f) == ".qasm") -> runFile f
  f | otherwise -> putStrLn ("Unrecognized option \"" ++ f ++ "\"") >> printHelp
  where o2 = [Simplify,Phasefold,Simplify,CT,Simplify,MCT]
        o3 = [CNOTMin,Simplify,Statefold 0,Phasefold,Simplify,CT,Simplify,MCT]
        o4 = [CNOTMin,Statefold 1,Cliff,Simplify,CZ,Simplify,Statefold 1,Phasefold,Simplify,CT,Simplify,MCT]
        runFile f | (drop (length f - 3) f) == ".qc"   = B.readFile f >>= runDotQC (passes options) (verify options) f
        runFile f | (drop (length f - 5) f) == ".qasm" =
          if useQASM3 options then readFile f >>= runQASM3 (passes options) (verify options) (pureCircuit options) f
                              else readFile f >>= runQASM (passes options) (verify options) (pureCircuit options) f
        runFile f = putStrLn ("Unrecognized file type \"" ++ f ++ "\"") >> printHelp


main :: IO ()
main = getArgs >>= parseArgs False defaultOptions
