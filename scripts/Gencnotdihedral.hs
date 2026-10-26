module Main where

import Control.Monad (forM_)
import qualified Data.Map as Map
import qualified Data.Set as Set
import System.Directory (createDirectoryIfMissing)
import Text.Printf (printf)

import Feynman.Core (Primitive, ID)
import Feynman.Synthesis.Pathsum.Unitary (generateCNOTDihedral)
import qualified Feynman.Frontend.DotQC as QC
import qualified Feynman.Frontend.OpenQASM.Syntax as Q

-- | Where the circuits are written (relative to where you run the program)
qcDir, qasmDir :: FilePath
qcDir   = "benchmarks/qc_cnotdihedral"
qasmDir = "benchmarks/qasm_cnotdihedral"

-- | (index, n qubits, k gates)
--   n grows by 1 every 3 circuits (3 .. 12), k grows steadily up to maxGates
--   (23, 46, 70, ... 700). Edit these to change the sizes or the number of circuits.
numCircuits, maxGates :: Int
numCircuits = 40
maxGates    = 900

schedule :: [(Int, Int, Int)]
schedule = [ (i, 3 + (i - 1) `div` 3, maxGates * i `div` numCircuits) | i <- [1 .. numCircuits] ]

-- | The n qubits of a circuit: q0 .. q(n-1).
--   Matches the names genT / genX / genCX use (they pick q0 .. q(m) for argument m).
qubitList :: Int -> [ID]
qubitList n = [ "q" ++ show i | i <- [0 .. n - 1] ]

-- | .qc text, printed by Feynman's Show DotQC instance
toQC :: Int -> [Primitive] -> String
toQC n gates = show dotqc ++ "\n"
  where
    qs    = qubitList n
    dotqc = QC.DotQC qs (Set.fromList qs) (Set.fromList qs)
                     [QC.Decl "main" [] (QC.fromCliffordT gates)]

-- | OpenQASM 2.0 text: one register qubits[0..n-1], gates converted and
--   printed by Feynman's OpenQASM module. Qubit order matches the .qc file.
toQASM :: Int -> [Primitive] -> String
toQASM n gates = unlines (Q.prettyPrint qasm)
  where
    qs    = qubitList n
    index = Map.fromList (zip qs [0 ..])
    uexps = Q.qcGatesToQASM index (QC.fromCliffordT gates)   -- register is named "qubits"
    qasm  = Q.QASM 2.0 $
              [ Q.IncStmt "qelib1.inc"
              , Q.DecStmt (Q.VarDec "qubits" (Q.Qreg n)) ]
              ++ map (Q.QStmt . Q.GateExp) uexps

main :: IO ()
main = do
  createDirectoryIfMissing True qcDir
  createDirectoryIfMissing True qasmDir
  forM_ schedule $ \(i, n, k) -> do
    -- the generators' argument is the highest qubit index, so n-1 gives n qubits
    gates <- generateCNOTDihedral (n - 1) k
    let base     = printf "cnotdihedral_%02d_n%d_k%d" i n k :: String
        qcFile   = qcDir   ++ "/" ++ base ++ ".qc"
        qasmFile = qasmDir ++ "/" ++ base ++ ".qasm"
    -- same random circuit goes into both files
    writeFile qcFile   (toQC n gates)
    writeFile qasmFile (toQASM n gates)
    printf "wrote %s (%d gates)\n" base (length gates)