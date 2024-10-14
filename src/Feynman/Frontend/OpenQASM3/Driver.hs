module Feynman.Frontend.OpenQASM3.Driver where

import Control.Monad.State.Lazy
import Data.Int (Int64)
-- import qualified Data.Map.Strict as Map
import Data.Map (Map, (!))
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Word (Word64)
import Feynman.Algebra.Base
import Feynman.Core hiding (Decl, subst)
import qualified Feynman.Frontend.Frontend as FE
import Feynman.Frontend.OpenQASM3.Ast
import qualified Feynman.Frontend.OpenQASM3.Chatty as Chatty
import Feynman.Frontend.OpenQASM3.Parser (parseString)
import Feynman.Frontend.OpenQASM3.Semantics
import qualified Feynman.Frontend.OpenQASM3.Semantics as QASM3
import Feynman.Frontend.OpenQASM3.Syntax
import qualified Feynman.Frontend.OpenQASM3.Syntax as QASM3
import Feynman.Frontend.OpenQASM3.Syntax.Transformations
import Feynman.Optimization.Clifford
import Feynman.Optimization.PhaseFold
import Feynman.Optimization.RelationalFold as L
import Feynman.Optimization.RelationalFoldNL as NL
import Feynman.Optimization.StateFold
import Feynman.Optimization.TPar
import Feynman.Synthesis.Pathsum.Unitary
import Feynman.Synthesis.Phase
import Feynman.Verification.Symbolic
import Numeric (showFFloat)
import System.CPUTime (getCPUTime)

-- type Ctx = Map.Map String SyntaxNode

type Result c = Chatty.Chatty String String c

generateInvariants :: String -> IO ()
generateInvariants fname = do
  src <- readFile fname
  case go src of
    Chatty.Failure _ err -> putStrLn $ "ERROR: " ++ err
    Chatty.Value _ invs -> do
      putStrLn $ "Loop invariants:"
      mapM_ (putStrLn . ("\t" ++)) $ invs
  where
    go src = do
      qasm <- parseString src
      let qasm' = decorateIDs . unrollLoops . inlineGateCalls $ qasm
      let wstmt = buildModel qasm'
      let ids = idsW wstmt
      return $ NL.summarizeLoops 0 ids ids wstmt

{-
-- transcribed from the OpenQASM 3.0 standard gate library and qelib1.inc

-- stdgates definitions not in qelib1
gate p(λ) a { ctrl @ gphase(λ) a; }
gate sx a { pow(0.5) @ x a; }
gate crx(θ) a, b { ctrl @ rx(θ) a, b; }
gate cry(θ) a, b { ctrl @ ry(θ) a, b; }
gate swap a, b { cx a, b; cx b, a; cx a, b; }
gate cswap a, b, c { ctrl @ swap a, b, c; }
gate cp(λ) a, b { ctrl @ p(λ) a, b; }
gate phase(λ) q { U(0, 0, λ) q; } -- same as u1
gate cphase(λ) a, b { ctrl @ phase(λ) a, b; } -- controlled u1

-- and because it's a QASM2 builtin,
gate CX a, b { ctrl @ U(π, 0, π) a, b; }

-- qelib1 has cu1 not in stdgates
gate cu1(lambda) a,b
{
  u1(lambda/2) a;
  cx a,b;
  u1(-lambda/2) b;
  cx a,b;
  u1(lambda/2) b;
}

-- stdgates definition
gate x a { U(π, 0, π) a; gphase(-π/2);}
-- qelib1 definition
gate x a { u3(pi,0,pi) a; }

-- stdgates definition
gate y a { U(π, π/2, π/2) a; gphase(-π/2);}
-- qelib1 definition
gate y a { u3(pi,pi/2,pi/2) a; }

-- stdgates definition
gate z a { p(π) a; }
-- qelib1 definition
gate z a { u1(pi) a; }

-- stdgates definition
gate h a { U(π/2, 0, π) a; gphase(-π/4);}
-- qelib1 definition
gate h a { u2(0,pi) a; }

-- stdgates definition
gate s a { pow(0.5) @ z a; }
-- qelib1 definition
gate s a { u1(pi/2) a; }

-- stdgates definition
gate sdg a { inv @ pow(0.5) @ z a; }
-- qelib1 definition
gate sdg a { u1(-pi/2) a; }

-- stdgates definition
gate t a { pow(0.5) @ s a; }
-- qelib1 definition
gate t a { u1(pi/4) a; }

-- stdgates definition
gate tdg a { inv @ pow(0.5) @ s a; }
-- qelib1 definition
gate tdg a { u1(-pi/4) a; }

-- stdgates definition
gate rx(θ) a { U(θ, -π/2, π/2) a; gphase(-θ/2);}
-- qelib1 definition
gate rx(theta) a { u3(theta,-pi/2,pi/2) a; }

-- stdgates definition
gate ry(θ) a { U(θ, 0, 0) a; gphase(-θ/2);}
-- qelib1 definition
gate ry(theta) a { u3(theta,0,0) a; }

-- stdgates definition
gate rz(λ) a { gphase(-λ/2); U(0, 0, λ) a; }
-- qelib1 definition
gate rz(phi) a { u1(phi) a; }

-- stdgates definition
gate cx a, b { ctrl @ x a, b; }
-- qelib1 definition
gate cx c,t { CX c,t; }

-- stdgates definition
gate cy a, b { ctrl @ y a, b; }
-- qelib1 definition
gate cy a,b { sdg b; cx a,b; s b; }

-- stdgates definition
gate cz a, b { ctrl @ z a, b; }
-- qelib1 definition
gate cz a,b { h b; cx a,b; h b; }

-- stdgates definition
gate crz(θ) a, b { ctrl @ rz(θ) a, b; }
-- qelib1 definition
gate crz(lambda) a,b
{
  u1(lambda/2) b;
  cx a,b;
  u1(-lambda/2) b;
  cx a,b;
}

-- stdgates definition
gate ch a, b { ctrl @ h a, b; }
-- qelib1 definition
gate ch a,b {
h b; sdg b;
cx a,b;
h b; t b;
cx a,b;
t b; h b; s b; x b; s a;
}

-- stdgates definition
gate ccx a, b, c { ctrl @ ctrl @ x a, b, c; }
-- qelib1 definition
gate ccx a,b,c
{
  h c;
  cx b,c; tdg c;
  cx a,c; t c;
  cx b,c; tdg c;
  cx a,c; t b; t c; h c;
  cx a,b; t a; tdg b;
  cx a,b;
}

-- stdgates definition
gate cu(θ, φ, λ, γ) a, b { p(γ-θ/2) a; ctrl @ U(θ, φ, λ) a, b; }
-- qelib1 definition
gate cu3(theta,phi,lambda) c, t
{
  // implements controlled-U(theta,phi,lambda) with  target t and control c
  u1((lambda-phi)/2) t;
  cx c,t;
  u3(-theta/2,0,-(phi+lambda)/2) t;
  cx c,t;
  u3(theta/2,phi,0) t;
}

-- stdgates definition
gate id a { U(0, 0, 0) a; }
-- qelib1 definition
gate id a { U(0,0,0) a; }

-- stdgates definition
gate u1(λ) q { U(0, 0, λ) q; }
-- qelib1 definition
gate u1(lambda) q { U(0,0,lambda) q; }

-- stdgates definition
gate u2(φ, λ) q { gphase(-(φ+λ+π/2)/2); U(π/2, φ, λ) q; }
-- qelib1 definition
gate u2(phi,lambda) q { U(pi/2,phi,lambda) q; }

-- stdgates definition
gate u3(θ, φ, λ) q { gphase(-(φ+λ+θ)/2); U(θ, φ, λ) q; }
-- qelib1 definition
gate u3(theta,phi,lambda) q { U(theta,phi,lambda) q; }

-- in both QASM2 and QASM3, U(...) a la u3(...) is a builtin

-}

formatFloatN floatNum numOfDecimals = showFFloat (Just numOfDecimals) floatNum ""

printErr (Left l) = Left $ show l
printErr (Right r) = Right r

instance FE.ProgramRepresentation (QASM3.SyntaxNode Loc) where
  readAndParse path = do
    src <- readFile path
    let parsed = parseString src
    case parsed of
      Chatty.Failure {Chatty.messages = msgs, Chatty.error = err} ->
        return $ Left $ unlines (msgs ++ [err])
      Chatty.Value {Chatty.value = qasm} ->
        return $ Right $ unrollLoops . inlineGateCalls . decorateIDs $ qasm

  expectValid _ = Right ()

  applyPass pureCircuit pass = case pass of
    FE.Triv -> id
    FE.Inline -> inlineGateCalls
    FE.Unroll -> unrollLoops
    FE.MCT -> id
    FE.CT -> id
    FE.Simplify -> id
    FE.Phasefold -> applyWStmtOpt (L.genSubstList)
    FE.Statefold 1 -> applyWStmtOpt (L.genSubstList)
    FE.Statefold d -> applyWStmtOpt (NL.genSubstList d)
    FE.PauliFold 1 -> applyWStmtOpt (L.genSubstList)
    FE.PauliFold d -> applyWStmtOpt (NL.genSubstList d)
    FE.CNOTMin -> id
    FE.TPar -> id
    FE.Cliff -> id
    FE.CZ -> id
    FE.CX -> id
    FE.Decompile -> id

  prettyPrint = QASM3.pretty

  computeStats qasm =
    let qbits = countQubits qasm
        counts = countGateCalls qasm
        totaldepth = Nothing
        tdepth = Nothing
     in FE.ProgramStats counts Nothing qbits totaldepth tdepth

  prettyPrintWithBenchmarkInfo name time stats stats' verified qc =
    unlines
      ( [ "// Feynman -- quantum circuit toolkit",
          "// Original (" ++ name ++ ", using QASM3 frontend):"
        ]
          ++ map ("//   " ++) (FE.statsLines stats)
          ++ ["// Result (" ++ formatFloatN time 3 ++ "ms):"]
          ++ map ("//   " ++) (FE.statsLines stats')
      )
      ++ QASM3.pretty qc

  equivalenceCheck _ _ = Left "Can't verify QASM3 programs"
