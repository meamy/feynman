module Feynman.Frontend.OpenQASM.Driver where

import Feynman.Core (expandCNOT, expandCZ)
import qualified Feynman.Frontend.Frontend as FE
import qualified Feynman.Frontend.OpenQASM.Lexer as QASMLexer
import qualified Feynman.Frontend.OpenQASM.Parser as QASMParser
import qualified Feynman.Frontend.OpenQASM.Syntax as QASM
import Feynman.Optimization.Clifford
import Feynman.Optimization.PhaseFold
import qualified Feynman.Optimization.RelationalFold as L
import qualified Feynman.Optimization.RelationalFoldNL as NL
import Feynman.Optimization.StateFold
import Feynman.Optimization.TPar
import Feynman.Synthesis.Pathsum.Unitary
import Feynman.Verification.Symbolic
import Numeric (showFFloat)
import System.CPUTime (getCPUTime)

formatFloatN floatNum numOfDecimals = showFFloat (Just numOfDecimals) floatNum ""

printErr (Left l) = Left $ show l
printErr (Right r) = Right r

instance FE.ProgramRepresentation QASM.QASM where
  readAndParse path = do
    src <- readFile path
    let parseResult = do
          let qasm = QASMParser.parse . QASMLexer.lexer $ src
          symtab <- QASM.check qasm
          return $ QASM.desugar symtab qasm -- For correct gate counts
    return parseResult

  expectValid _ = Right ()

  applyPass pureCircuit pass = case pass of
    FE.Triv -> id
    FE.Inline -> QASM.inline
    FE.Unroll -> id
    FE.MCT -> QASM.inline
    FE.CT -> QASM.inline
    FE.Simplify -> id
    FE.Phasefold -> QASM.applyOpt phaseFold pureCircuit
    FE.Statefold d -> QASM.applyOpt (stateFold d) pureCircuit
    FE.PauliFold d -> QASM.applyOpt (pauliFold d) pureCircuit
    FE.CNOTMin -> QASM.applyOpt minCNOT pureCircuit
    FE.TPar -> QASM.applyOpt tpar pureCircuit
    FE.Cliff -> QASM.applyOpt (\_ _ -> simplifyCliffords) pureCircuit
    FE.CZ -> QASM.applyOpt (\_ _ -> expandCNOT) pureCircuit
    FE.CX -> QASM.applyOpt (\_ _ -> expandCZ) pureCircuit
    FE.Decompile -> id

  prettyPrint = unlines . QASM.prettyPrint

  computeStats qasm =
    let qasm' = QASM.inline qasm
        (cbits, qbits) = QASM.bitCounts qasm'
        counts = QASM.gateCounts qasm'
        totaldepth = Nothing
        tdepth = Nothing
     in FE.ProgramStats counts (Just cbits) qbits totaldepth tdepth

  prettyPrintWithBenchmarkInfo name time stats stats' verified qc =
    unlines
      ( [ "// Feynman -- quantum circuit toolkit",
          "// Original (" ++ name ++ "):"
        ]
          ++ map ("//   " ++) (FE.statsLines stats)
          ++ ["// Result (" ++ formatFloatN time 3 ++ "ms):"]
          ++ map ("//   " ++) (FE.statsLines stats')
          ++ QASM.prettyPrint qc
      )

  equivalenceCheck _ _ = Left "Can't verify QASM programs"
