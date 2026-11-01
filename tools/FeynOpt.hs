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


-- Optimization presets
presetO2, presetO3, presetO4, presetAPF, presetQPF, presetPPF :: [Pass]
presetO2  = [Simplify, Phasefold, Simplify, CT, Simplify, MCT]
presetO3  = [CNOTMin, Simplify, Statefold 0, Phasefold, Simplify, CT, Simplify, MCT]
presetO4  = [CNOTMin, Cliff, Paulifold 1, Simplify, Statefold 0, Phasefold, Simplify, CT, Simplify, MCT]
presetAPF = [Simplify, Paulifold 1, Simplify, Statefold 1, Statefold 1, Phasefold, Simplify, CT, Simplify, MCT]
presetQPF = [Simplify, Paulifold 1, Simplify, Statefold 2, Statefold 2, Phasefold, Simplify, CT, Simplify, MCT]
presetPPF = [Simplify, Paulifold 1, Simplify, Statefold 0, Statefold 0, Phasefold, Simplify, CT, Simplify, MCT]

-- Option record helpers
addPass :: Pass -> Options -> Options
addPass p options = options { passes = p : passes options }

addPasses :: [Pass] -> Options -> Options
addPasses ps options = options { passes = ps ++ passes options }

isQC, isQASM, isCircuitFile :: FilePath -> Bool
isQC f   = ".qc"   `isSuffixOf` f
isQASM f = ".qasm" `isSuffixOf` f
isCircuitFile f = isQC f || isQASM f

parseArgs :: Bool -> Options -> [String] -> IO ()
parseArgs doneSwitches options args = case args of
  [] -> printHelp

  -- If switches were terminated by '--', treat the next argument as the circuit file:
  arg : _ | doneSwitches -> runFile arg

  -- Flags
  "-h"           : _  -> printHelp
  "-purecircuit" : xs -> parseArgs False (options { pureCircuit = True }) xs
  "-verify"      : xs -> parseArgs False (options { verify = True }) xs
  "-qasm3"       : xs -> parseArgs False (options { useQASM3 = True }) xs
  "--"           : xs -> parseArgs True  options xs

  -- Single passes
  "-inline"      : xs -> parseArgs False (addPass Inline options) xs
  "-unroll"      : xs -> parseArgs False (addPass Unroll options) xs
  "-mctExpand"   : xs -> parseArgs False (addPass MCT options) xs
  "-toCliffordT" : xs -> parseArgs False (addPass CT options) xs
  "-simplify"    : xs -> parseArgs False (addPass Simplify options) xs
  "-phasefold"   : xs -> parseArgs False (addPass Phasefold options) xs
  "-cnotmin"     : xs -> parseArgs False (addPass CNOTMin options) xs
  "-tpar"        : xs -> parseArgs False (addPass TPar options) xs
  "-clifford"    : xs -> parseArgs False (addPass Cliff options) xs
  "-cxcz"        : xs -> parseArgs False (addPass CZ options) xs
  "-czcx"        : xs -> parseArgs False (addPass CX options) xs
  "-decompile"   : xs -> parseArgs False (addPass Decompile options) xs

  -- Parameterized passes
  "-statefold"   : d : xs   -> parseArgs False (addPass (Statefold $ read d) options) xs
  "-paulifold"   : d : xs   -> parseArgs False (addPass (Paulifold $ read d) options) xs
  "-benchmark"   : path : _ -> benchmarkFolder path >>= runBenchmarks (benchPass $ passes options) (benchVerif $ verify options)
  "-invgen"      : file : _ -> generateInvariants file

  -- Preset pipelines
  "-O2"          : xs -> parseArgs False (addPasses presetO2 options) xs
  "-O3"          : xs -> parseArgs False (addPasses presetO3 options) xs
  "-O4"          : xs -> parseArgs False (addPasses presetO4 options) xs
  "-apf"         : xs -> parseArgs False (addPasses presetAPF options) xs
  "-qpf"         : xs -> parseArgs False (addPasses presetQPF options) xs
  "-ppf"         : xs -> parseArgs False (addPasses presetPPF options) xs

  -- Benchmark suites
  "Small"        : _  -> runBenchmarks (benchPass $ passes options) (benchVerif $ verify options) benchmarksSmall
  "Med"          : _  -> runBenchmarks (benchPass $ passes options) (benchVerif $ verify options) benchmarksMedium
  "All"          : _  -> runBenchmarks (benchPass $ passes options) (benchVerif $ verify options) benchmarksAll
  "POPL25"       : _  -> runBenchmarks (benchPass $ passes options) (benchVerif $ verify options) benchmarksPOPL25
  "POPL25QASM"   : _  -> runBenchmarks (benchPass $ passes options) (benchVerif $ verify options) benchmarksPOPL25QASM

  -- Input circuit files
  f : _ | isCircuitFile f -> runFile f
  f : _                   -> putStrLn ("Unrecognized option \"" ++ f ++ "\"") >> printHelp
  where
    runFile f
      | isQC f   = B.readFile f >>= runDotQC (passes options) (verify options) f
      | isQASM f = do
          let runner = if useQASM3 options then runQASM3 else runQASM
          readFile f >>= runner (passes options) (verify options) (pureCircuit options) f
      | otherwise = putStrLn ("Unrecognized file type \"" ++ f ++ "\"") >> printHelp

main :: IO ()
main = getArgs >>= parseArgs False defaultOptions
