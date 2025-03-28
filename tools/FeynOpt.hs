{-# LANGUAGE TupleSections, BangPatterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant bracket" #-}
module Main (main) where

import Feynman.Core (Primitive,
                     ID,
                     simplifyPrimitive',
                     expandCNOT,
                     expandCNOT',
                     annotate,
                     unannotate,
                     expandCZ,
                     idsW)

import qualified Feynman.Frontend.DotQC as DotQC

import qualified Feynman.Frontend.OpenQASM.Syntax as QASM2
import qualified Feynman.Frontend.OpenQASM.Lexer  as QASM2Lexer
import qualified Feynman.Frontend.OpenQASM.Parser as QASM2Parser

import qualified Feynman.Frontend.OpenQASM3.Chatty as QASM3Chatty
import qualified Feynman.Frontend.OpenQASM3.Parser as QASM3Parser
import qualified Feynman.Frontend.OpenQASM3.Syntax as QASM3Syntax
import qualified Feynman.Frontend.OpenQASM3.Utils  as QASM3Utils

import Feynman.Optimization.PhaseFold
import Feynman.Optimization.StateFold
import Feynman.Optimization.TPar
import Feynman.Optimization.Clifford
import Feynman.Synthesis.Pathsum.Unitary hiding (MCT)
import Feynman.Verification.Symbolic

import System.Environment (getArgs)
import System.CPUTime     (getCPUTime)
import System.IO (hPutStrLn, stderr)

import Data.List
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map

import Control.Monad

import Data.ByteString (ByteString)
import qualified Data.ByteString as B

import Benchmarks (runBenchmarks,
                   benchmarksSmall,
                   benchmarksMedium,
                   benchmarksAll,
                   benchmarksPOPL25,
                   benchmarksPOPL25QASM,
                   benchmarkFolder,
                   formatFloatN)


{- Toolkit passes -}

data Pass = Triv
          | Inline
          | Unroll
          | MCT
          | CT
          | Simplify
          | Phasefold
          | Paulifold Int
          | Statefold Int
          | CNOTMin
          | TPar
          | Cliff
          | ZXopt
          | CZ
          | CX
          | Decompile

data Options = Options { 
  passes :: [Pass],
  verify :: Bool,
  pureCircuit :: Bool,
  useQASM3 :: Bool }

{- DotQC -}

optimizeDotQC :: ([ID] -> [ID] -> [Primitive] -> [Primitive]) -> DotQC.DotQC -> DotQC.DotQC
optimizeDotQC f qc = qc { DotQC.decls = map go $ DotQC.decls qc }
  where go decl =
          let circuitQubits = DotQC.qubits qc ++ DotQC.params decl
              circuitInputs = (Set.toList $ DotQC.inputs qc) ++ DotQC.params decl
              wrap g        = DotQC.fromCliffordT . g . DotQC.toCliffordT
          in
            decl { DotQC.body = wrap (f circuitQubits circuitInputs) $ DotQC.body decl }

decompileDotQC :: DotQC.DotQC -> DotQC.DotQC
decompileDotQC qc = qc { DotQC.decls = map go $ DotQC.decls qc }
  where go decl =
          let circuitQubits  = DotQC.qubits qc ++ DotQC.params decl
              circuitInputs  = (Set.toList $ DotQC.inputs qc) ++ DotQC.params decl
              resynthesize c = case resynthesizeCircuit $ DotQC.toCliffordT c of
                Nothing -> c
                Just c' -> DotQC.fromExtractionBasis c'
          in
            decl { DotQC.body = resynthesize $ DotQC.body decl }

dotQCPass :: Pass -> (DotQC.DotQC -> DotQC.DotQC)
dotQCPass pass = case pass of
  Triv        -> id
  Inline      -> DotQC.inlineDotQC
  Unroll      -> id
  MCT         -> DotQC.expandToffolis
  CT          -> DotQC.expandAll
  Simplify    -> DotQC.simplifyDotQC
  Phasefold   -> optimizeDotQC phaseFold
  Paulifold d -> optimizeDotQC (pauliFold d)
  Statefold d -> optimizeDotQC (stateFold d)
  CNOTMin     -> optimizeDotQC minCNOT
  TPar        -> optimizeDotQC tpar
  Cliff       -> optimizeDotQC (\_ _ -> simplifyCliffords)
  ZXopt       -> optimizeDotQC optimizeModuloCliffords
  CZ          -> optimizeDotQC (\_ _ -> expandCNOT)
  CX          -> optimizeDotQC (\_ _ -> expandCZ)
  Decompile   -> decompileDotQC

equivalenceCheckDotQC :: DotQC.DotQC -> DotQC.DotQC -> Either String DotQC.DotQC
equivalenceCheckDotQC qc qc' =
  let circ    = DotQC.toCliffordT . DotQC.toGatelist $ qc
      circ'   = DotQC.toCliffordT . DotQC.toGatelist $ qc'
      vars    = union (DotQC.qubits qc) (DotQC.qubits qc')
      ins     = Set.toList $ DotQC.inputs qc
      result  = validate True vars ins circ circ'
  in
    case (DotQC.inputs qc == DotQC.inputs qc', result) of
      (False, _)            -> Left $ "Circuits not equivalent (different inputs)"
      (_, NotIdentity ce)   -> Left $ "Circuits not equivalent (" ++ ce ++ ")"
      (_, Inconclusive sop) -> Left $ "Failed to verify: \n  " ++ show sop
      _                     -> Right qc'

runDotQC :: [Pass] -> Bool -> String -> ByteString -> IO ()
runDotQC passes verify fname src = do
  start <- getCPUTime
  end   <- parseAndPass `seq` getCPUTime
  case parseAndPass of
    Left err        -> hPutStrLn stderr $ "ERROR: " ++ err
    Right (qc, qc') -> do
      let time = (fromIntegral $ end - start) / 10^9
      let verStr = if verify then ", Verified" else ""
      putStrLn $ "# Feynman -- quantum circuit toolkit"
      putStrLn $ "# Original (" ++ fname ++ "):"
      mapM_ putStrLn . map ("#   " ++) $ DotQC.showCliffordTStats qc
      putStrLn $ "# Result (" ++ formatFloatN time 3 ++ "ms" ++ verStr ++ "):"
      mapM_ putStrLn . map ("#   " ++) $ DotQC.showCliffordTStats qc'
      if verify then putStrLn $ "# Verified" else return ()
      putStrLn $ show qc'
  where printErr (Left l)  = Left $ show l
        printErr (Right r) = Right r
        parseAndPass = do
          qc  <- printErr $ DotQC.parseDotQC src
          qc' <- return $ foldr dotQCPass qc passes
          seq (DotQC.depth $ DotQC.toGatelist qc') (return ()) -- Nasty solution to strictifying
          if verify then void $ equivalenceCheckDotQC qc qc' else return ()
          return (qc, qc')

{- Deprecated transformations for benchmark suites -}
benchPass :: [Pass] -> (DotQC.DotQC -> Either String DotQC.DotQC)
benchPass passes = \qc -> Right $ foldr dotQCPass qc passes

benchVerif :: Bool -> Maybe (DotQC.DotQC -> DotQC.DotQC -> Either String DotQC.DotQC)
benchVerif True  = Just equivalenceCheckDotQC
benchVerif False = Nothing

{- QASM -}

qasmPass :: Bool -> Pass -> (QASM2.QASM -> QASM2.QASM)
qasmPass pureCircuit pass = case pass of
  Triv        -> id
  Inline      -> QASM2.inline
  Unroll      -> id
  MCT         -> QASM2.inline
  CT          -> QASM2.inline
  Simplify    -> id
  Phasefold   -> QASM2.applyOpt phaseFold pureCircuit
  Statefold d -> QASM2.applyOpt (stateFold d) pureCircuit
  Paulifold d -> QASM2.applyOpt (pauliFold d) pureCircuit
  CNOTMin     -> QASM2.applyOpt minCNOT pureCircuit
  TPar        -> QASM2.applyOpt tpar pureCircuit
  Cliff       -> QASM2.applyOpt (\_ _ -> simplifyCliffords) pureCircuit
  CZ          -> QASM2.applyOpt (\_ _ -> expandCNOT) pureCircuit
  CX          -> QASM2.applyOpt (\_ _ -> expandCZ) pureCircuit
  Decompile   -> id

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
      mapM_ putStrLn . map ("//   " ++) $ QASM2.showStats qasm
      putStrLn $ "// Result (" ++ formatFloatN time 3 ++ "ms):"
      mapM_ putStrLn . map ("//   " ++) $ QASM2.showStats qasm'
      QASM2.emit qasm'
  where parseAndPass = do
          let qasm   = QASM2Parser.parse . QASM2Lexer.lexer $ src
          symtab <- QASM2.check qasm
          let qasm'  = QASM2.desugar symtab qasm -- For correct gate counts
          qasm'' <- return $ foldr (qasmPass pureCircuit) qasm' passes
          return (qasm', qasm'')

{- QASM3 -}

showCounts :: Map String Int -> [String]
showCounts = map f . Map.toList where
  f (gate, count) = gate ++ ": " ++ show count

qasm3Pass pureCircuit pass = case pass of
  Triv        -> id
  Inline      -> QASM3Utils.inlineGateCalls
  Unroll      -> QASM3Utils.unrollLoops
  MCT         -> id
  CT          -> id
  Simplify    -> id
  Phasefold   -> QASM3Utils.applyWStmtOpt phaseAnalysispp
  Statefold 1 -> QASM3Utils.applyWStmtOpt phaseAnalysispp
  Statefold d -> QASM3Utils.applyWStmtOpt (stateAnalysispp d)
  Paulifold 1 -> QASM3Utils.applyWStmtOpt phaseAnalysispp
  Paulifold d -> QASM3Utils.applyWStmtOpt (stateAnalysispp d)
  CNOTMin     -> id
  TPar        -> id
  Cliff       -> id
  CZ          -> id
  CX          -> id
  Decompile   -> id

runQASM3 :: [Pass] -> Bool -> Bool -> String -> String -> IO ()
runQASM3 passes verify pureCircuit fname src = do
  start <- getCPUTime
  end   <- parseAndPass `seq` getCPUTime
  case parseAndPass of
    QASM3Chatty.Failure _ err -> putStrLn $ "ERROR: " ++ err
    QASM3Chatty.Value _ (qasm, qasm') -> do
      let time = (fromIntegral $ end - start) / 10^9
      putStrLn $ "// Feynman -- quantum circuit toolkit"
      putStrLn $ "// Original (" ++ fname ++ ", using QASM3 frontend):"
      mapM_ putStrLn . map ("//   " ++) $ QASM3Utils.showStats qasm
      putStrLn $ "// Result (" ++ formatFloatN time 3 ++ "ms):"
      mapM_ putStrLn . map ("//   " ++) $ QASM3Utils.showStats qasm'
      putStrLn $ QASM3Syntax.pretty qasm'
      return ()
  where parseAndPass = do
          qasm <- QASM3Parser.parseString  src
          let qasm' = QASM3Utils.unrollLoops . QASM3Utils.inlineGateCalls . QASM3Utils.decorateIDs $ qasm
          qasm'' <- return $ foldr (qasm3Pass pureCircuit) qasm' passes
          return (qasm', qasm'')

generateInvariants :: String -> IO ()
generateInvariants fname = case drop (length fname - 5) fname == ".qasm" of
  False -> putStrLn ("Must be a qasm file (" ++ fname ++ ")") >> printHelp
  True  -> do
    src <- readFile fname
    case go src of
      QASM3Chatty.Failure _ err -> putStrLn $ "ERROR: " ++ err
      QASM3Chatty.Value _ invs -> do
        putStrLn $ "Loop invariants:"
        mapM_ putStrLn . map ("\t" ++) $ invs
        return ()
  where go src = do
          qasm <- QASM3Parser.parseString src
          let qasm' = QASM3Utils.decorateIDs . QASM3Utils.unrollLoops . QASM3Utils.inlineGateCalls $ qasm
          let wstmt = QASM3Utils.buildModel qasm'
          let ids   = idsW wstmt
          return $ summarizeLoops 0 ids ids wstmt

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
          "  -purecircuit\t\tPerform qasm passes assuming the initial state (of qubits) is unknown",
          "  -verify\t\tVerify equivalence of the output to the original circuit (only dotQC)",
          "  -qasm3\t\tRun using the openQASM 3 frontend",
          "",
          "Transformation passes:",
          "  -inline\t\tInline all sub-circuits",
          "  -unroll\t\tUnroll loops (QASM3 specific)",
          "  -mctExpand\t\tExpand all MCT gates using |0>-initialized ancillas",
          "  -toCliffordT\t\tExpand all gates to Clifford+T gates",
          "  -decompile\t\tDecompiles a Clifford+T circuit into multiply-controlled gates",
          "  -cxcz\t\t\tReplaces CNOT gates with H and CZ",
          "  -czcx\t\t\tReplaces CZ gates with H and CNOT",
          "",
          "Optimization passes:",
          "  -simplify\t\tBasic gate-cancellation pass",
          "  -phasefold\t\tMerges phase gates according to the circuit's phase polynomial",
          "  -statefold <d>\tPhase folding with state invariants up to degree <d> (or unbounded if d < 1)",
          "  -paulifold <d>\tMonotone optimization equivalent to -cxcz -statefold",
          "  -tpar\t\t\tPhase folding + T-parallelization algorithm from (Amy, Maslov, Mosca, TCAD 2014)",
          "  -cnotmin\t\tPhase folding + CNOT-minimization algorithm from (Amy, Azimzadeh, Mosca, Q. Sci. Tech. 2017)",
          "  -clifford\t\tRe-synthesize Clifford segments",
          "",
          "  -O2\t\t\t**Standard strategy** Phase folding + simplify",
          "  -O3\t\t\tPhase folding + state folding + simplify + CNOT minimization",
          "  -O4\t\t\tPhase folding + state folding + simplify + Clifford resynthesis + CNOT minimization",
          "",
          "  -apf\t\t\tAffine phase folding (Amy & Lunderville, POPL 2025)",
          "  -qpf\t\t\tQuadratic phase folding (Amy & Lunderville, POPL 2025)",
          "  -ppf\t\t\tPolynomial phase folding (Amy & Lunderville, POPL 2025)",
          "",
          "Benchmarking:",
          "  -benchmark <path>\tRun on all files in <folder> and output statistics",
          "",
          "Misc:",
          "  -invgen <file>\tGenerates and prints loop invariants",
          "",
          "E.g. \"feyn -verify -inline -cnotmin -simplify circuit.qc\" will first inline the circuit,",
          "       then optimize CNOTs, followed by a gate cancellation pass and finally verify the result",
          "",
          "Caution: Attempting to verify very large circuits can overload your system memory.",
          "         Set user-level memory limits when doing so."
          ]


defaultOptions :: Options
defaultOptions = Options {
  passes = [],
  verify = False,
  pureCircuit = False,
  useQASM3 = False }


parseArgs :: Bool -> Options -> [String] -> IO ()
parseArgs doneSwitches options []     = printHelp
parseArgs doneSwitches options (x:xs) = case x of
  f | doneSwitches -> runFile f
  "-h"           -> printHelp
  "-purecircuit" -> parseArgs doneSwitches options {pureCircuit = True} xs
  "-inline"      -> parseArgs doneSwitches options {passes = Inline:passes options} xs
  "-unroll"      -> parseArgs doneSwitches options {passes = Unroll:passes options} xs
  "-mctExpand"   -> parseArgs doneSwitches options {passes = MCT:passes options} xs
  "-toCliffordT" -> parseArgs doneSwitches options {passes = CT:passes options} xs
  "-simplify"    -> parseArgs doneSwitches options {passes = Simplify:passes options} xs
  "-phasefold"   -> parseArgs doneSwitches options {passes = Phasefold:passes options} xs
  "-statefold"   -> parseArgs doneSwitches options {passes = (Statefold $ read (head xs)):passes options} (tail xs)
  "-paulifold"   -> parseArgs doneSwitches options {passes = (Paulifold $ read (head xs)):passes options} (tail xs)
  "-cnotmin"     -> parseArgs doneSwitches options {passes = CNOTMin:passes options} xs
  "-tpar"        -> parseArgs doneSwitches options {passes = TPar:passes options} xs
  "-clifford"    -> parseArgs doneSwitches options {passes = Cliff:passes options} xs
  "-zxopt"       -> parseArgs doneSwitches options {passes = ZXopt:passes options} xs
  "-cxcz"        -> parseArgs doneSwitches options {passes = CZ:passes options} xs
  "-czcx"        -> parseArgs doneSwitches options {passes = CX:passes options} xs
  "-decompile"   -> parseArgs doneSwitches options {passes = Decompile:passes options} xs
  "-O2"          -> parseArgs doneSwitches options {passes = o2 ++ passes options} xs
  "-O3"          -> parseArgs doneSwitches options {passes = o3 ++ passes options} xs
  "-O4"          -> parseArgs doneSwitches options {passes = o4 ++ passes options} xs
  "-apf"         -> parseArgs doneSwitches options {passes = apf ++ passes options} xs
  "-qpf"         -> parseArgs doneSwitches options {passes = qpf ++ passes options} xs
  "-ppf"         -> parseArgs doneSwitches options {passes = ppf ++ passes options} xs
  "-verify"      -> parseArgs doneSwitches options {verify = True} xs
  "-benchmark"   -> benchmarkFolder (head xs) >>= runBenchmarks (benchPass $ passes options) (benchVerif $ verify options)
  "-qasm3"       -> parseArgs doneSwitches options {useQASM3 = True} xs
  "-invgen"      -> generateInvariants (head xs)
  "--"           -> parseArgs True options xs
  "Small"        -> runBenchmarks (benchPass $ passes options) (benchVerif $ verify options) benchmarksSmall
  "Med"          -> runBenchmarks (benchPass $ passes options) (benchVerif $ verify options) benchmarksMedium
  "All"          -> runBenchmarks (benchPass $ passes options) (benchVerif $ verify options) benchmarksAll
  "POPL25"       -> runBenchmarks (benchPass $ passes options) (benchVerif $ verify options) benchmarksPOPL25
  "POPL25QASM"   -> runBenchmarks (benchPass $ passes options) (benchVerif $ verify options) benchmarksPOPL25QASM
  f | ((drop (length f - 3) f) == ".qc") || ((drop (length f - 5) f) == ".qasm") -> runFile f
  f | otherwise -> putStrLn ("Unrecognized option \"" ++ f ++ "\"") >> printHelp
  where o2  = [Simplify,Phasefold,Simplify,CT,Simplify,MCT]
        o3  = [CNOTMin,Simplify,Statefold 0,Phasefold,Simplify,CT,Simplify,MCT]
        o4  = [CNOTMin,Cliff,Paulifold 1,Simplify,Statefold 0,Phasefold,Simplify,CT,Simplify,MCT]
        apf = [Simplify,Paulifold 1,Simplify,Statefold 1,Statefold 1,Phasefold,Simplify,CT,Simplify,MCT]
        qpf = [Simplify,Paulifold 1,Simplify,Statefold 2,Statefold 2,Phasefold,Simplify,CT,Simplify,MCT]
        ppf = [Simplify,Paulifold 1,Simplify,Statefold 0,Statefold 0,Phasefold,Simplify,CT,Simplify,MCT]
        runFile f | (drop (length f - 3) f) == ".qc"   = B.readFile f >>= runDotQC (passes options) (verify options) f
        runFile f | (drop (length f - 5) f) == ".qasm" =
          if useQASM3 options then readFile f >>= runQASM3 (passes options) (verify options) (pureCircuit options) f
                              else readFile f >>= runQASM (passes options) (verify options) (pureCircuit options) f
        runFile f = putStrLn ("Unrecognized file type \"" ++ f ++ "\"") >> printHelp

main :: IO ()
main = getArgs >>= parseArgs False defaultOptions
