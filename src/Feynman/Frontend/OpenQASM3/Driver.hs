module Feynman.Frontend.OpenQASM3.Driver where

import qualified Control.Monad.State as State
import Data.Int (Int64)
-- import qualified Data.Map.Strict as Map
import Data.Map ((!))
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Word (Word64)
import Feynman.Core
import qualified Feynman.Frontend.OpenQASM3.Ast as Ast
import qualified Feynman.Frontend.OpenQASM3.Chatty as Chatty
import qualified Feynman.Frontend.OpenQASM3.Semantics as Semantics
import qualified Feynman.Frontend.OpenQASM3.Syntax as Syntax

-- type Ctx = Map.Map String SyntaxNode

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
gate phase(λ) q { U(0, 0, λ) q; }
gate cphase(λ) a, b { ctrl @ phase(λ) a, b; }

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

-- qelib1 :: Ctx
-- qelib1 = Map.fromList
--   [ ("u3", Circ 3 1),
--     ("u2", Circ 2 1),
--     ("u1", Circ 1 1),
--     ("cx", Circ 0 2),
--     ("id", Circ 0 1),
--     ("x", Circ 0 1),
--     ("y", Circ 0 1),
--     ("z", Circ 0 1),
--     ("h", Circ 0 1),
--     ("s", Circ 0 1),
--     ("sdg", Circ 0 1),
--     ("t", Circ 0 1),
--     ("tdg", Circ 0 1),
--     ("rx", Circ 1 1),
--     ("ry", Circ 1 1),
--     ("rz", Circ 1 1),
--     ("cz", Circ 0 2),
--     ("cy", Circ 0 2),
--     ("ch", Circ 0 2),
--     ("ccx", Circ 0 3),
--     ("crz", Circ 1 2),
--     ("cu1", Circ 1 2),
--     ("cu3", Circ 3 2) ]

type Result c = Chatty.Chatty String String c

analyze :: Ast.Node Syntax.Tag c -> Result Semantics.Program
analyze = Semantics.analyze

normalize :: Semantics.Program -> Result Semantics.Program
normalize = return

-- Inlines all local definitions & non-primitive operations
-- Note: non-strictness can hopefully allow for some efficient
--       fusion with operations on inlined code
inline :: Semantics.Program -> Result Semantics.Program
inline = return

-- Provides an optimization interface for the main IR
applyOpt :: ([ID] -> [ID] -> [Primitive] -> [Primitive]) -> Bool -> Semantics.Program -> Result Semantics.Program
applyOpt opt pureCircuit = return

{- Statistics -}

-- Assumes inlined code
gateCounts :: Semantics.Program -> Map.Map ID Int
gateCounts _ = Map.empty

-- gateCounts (QASM ver stmts) =

bitCounts :: Semantics.Program -> (Int, Int)
bitCounts _ = (0, 0)

-- bitCounts (QASM ver stmts) = foldl bcStmt (0, 0) stmts

-- depth :: QASM -> Int
-- gateDepth :: [ID] -> QASM -> Int

showStats :: Semantics.Program -> [String]
showStats _ = ["Stats not available for QASM3"]

-- showStats qasm =
--          ["cbits: " ++ show cbits, "qubits: " ++ show qbits] ++
--          map (\ (gate, count) -> gate ++ ": " ++ show count) . Map.toList $ gateCounts qasm'

emit :: Semantics.Program -> String
emit _ = "Not implemented\n"
