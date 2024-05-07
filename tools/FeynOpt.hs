{-# LANGUAGE TupleSections #-}
module Main (main) where

import Feynman.Core (Primitive, ID, expandCNOT, expandCZ)
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
          | CX
          | Decompile

{- DotQC -}

optimizeDotQC :: ([ID] -> [ID] -> [Primitive] -> [Primitive]) -> DotQC -> DotQC
optimizeDotQC f qc = qc { decls = map go $ decls qc }
  where go decl =
          let circuitQubits = qubits qc ++ params decl
              circuitInputs = (Set.toList $ inputs qc) ++ params decl
              wrap g        = fromCliffordT . g . toCliffordT
          in
            decl { body = wrap (f circuitQubits circuitInputs) $ body decl }

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
  CX          -> optimizeDotQC (\_ _ -> expandCZ)
  Decompile   -> decompileDotQC

equivalenceCheckDotQC :: DotQC -> DotQC -> Either String DotQC
equivalenceCheckDotQC qc qc' =
  let circ    = toCliffordT . toGatelist $ qc
      circ'   = toCliffordT . toGatelist $ qc'
      vars    = union (qubits qc) (qubits qc')
      ins     = Set.toList $ inputs qc
      result  = validate True vars ins circ circ'
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
  CX          -> applyOpt (\_ _ -> expandCZ) pureCircuit

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
          "  -apf\t\tAffine phase folding algorithm (equiv. to pyzx)",
          "  -qpf\t\tQuadratic phase folding algorithm",
          "  -ppf\t\tPolynomial phase folding algorithm",
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


parseArgs :: [Pass] -> Bool -> Bool -> [String] -> IO ()
parseArgs passes verify pureCircuit []     = printHelp
parseArgs passes verify pureCircuit (x:xs) = case x of
  "-h"           -> printHelp
  "-purecircuit" -> parseArgs (passes) verify True xs
  "-inline"      -> parseArgs (Inline:passes) verify pureCircuit xs
  "-mctExpand"   -> parseArgs (MCT:passes) verify pureCircuit xs
  "-toCliffordT" -> parseArgs (CT:passes) verify pureCircuit xs
  "-simplify"    -> parseArgs (Simplify:passes) verify pureCircuit xs
  "-phasefold"   -> parseArgs (Phasefold:passes) verify pureCircuit xs
  "-statefold"   -> parseArgs ((Statefold $ read (head xs)):passes) verify pureCircuit (tail xs)
  "-cnotmin"     -> parseArgs (CNOTMin:passes) verify pureCircuit xs
  "-tpar"        -> parseArgs (TPar:passes) verify pureCircuit xs
  "-clifford"    -> parseArgs (Cliff:passes) verify pureCircuit xs
  "-cxcz"        -> parseArgs (CZ:passes) verify pureCircuit xs
  "-czcx"        -> parseArgs (CX:passes) verify pureCircuit xs
  "-decompile"   -> parseArgs (Decompile:passes) verify pureCircuit xs
  "-O2"          -> parseArgs (o2 ++ passes) verify pureCircuit xs
  "-O3"          -> parseArgs (o3 ++ passes) verify pureCircuit xs
  "-apf"         -> parseArgs (apf ++ passes) verify pureCircuit xs
  "-qpf"         -> parseArgs (qpf ++ passes) verify pureCircuit xs
  "-ppf"         -> parseArgs (ppf ++ passes) verify pureCircuit xs
  "-verify"      -> parseArgs passes True pureCircuit xs
  "-benchmarks"  -> benchmarkFolder (head xs) >>= runBenchmarks (benchPass passes) (benchVerif verify)
  "VerBench"     -> runBenchmarks (benchPass [CNOTMin,Simplify]) (benchVerif True) benchmarksMedium
--  "VerAlg"       -> runVerSuite
  "Small"        -> runBenchmarks (benchPass passes) (benchVerif verify) benchmarksSmall
  "Med"          -> runBenchmarks (benchPass passes) (benchVerif verify) benchmarksMedium
  "All"          -> runBenchmarks (benchPass passes) (benchVerif verify) benchmarksAll
  f | (drop (length f - 3) f) == ".qc" -> B.readFile f >>= runDotQC passes verify f
  f | (drop (length f - 5) f) == ".qasm" -> readFile f >>= runQASM passes verify pureCircuit f
  f | otherwise -> putStrLn ("Unrecognized option \"" ++ f ++ "\"") >> printHelp
  where o2  = [Simplify,Phasefold,Simplify,CT,Simplify,MCT]
        o3  = [CNOTMin,Simplify,Statefold 0,Phasefold,Simplify,CT,Simplify,MCT]
        apf = [Simplify,Statefold 1,Cliff,Simplify,CZ,Simplify,Statefold 1,Phasefold,Simplify,CT,Simplify,MCT]
        qpf = [Simplify,Statefold 1,Cliff,Simplify,CZ,Simplify,Statefold 2,Phasefold,Simplify,CT,Simplify,MCT]
        ppf = [Simplify,Statefold 1,Cliff,Simplify,CZ,Simplify,Statefold 0,Phasefold,Simplify,CT,Simplify,MCT]

main :: IO ()
main = getArgs >>= parseArgs [] False False
