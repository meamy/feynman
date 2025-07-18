module Feynman.Synthesis.HypergraphPartition.HGraphBuilder where
import qualified Data.Map as Map
import           Data.Map   (Map)

import           Data.List (sort)

import Data.Set (Set)
import qualified Data.Set as Set

import System.Directory (createDirectoryIfMissing, doesFileExist)
import System.FilePath  ((</>), (<.>))
import System.Process (callProcess)
import qualified Feynman.Synthesis.HypergraphPartition.PartitionConfigs as Cfg
import Control.Monad (unless)



import Feynman.Core
    ( Circuit(..),
      Primitive(..),
      getArgs,
      foldCirc,
      Decl(..),
      foldStmt,
      Stmt(..),
      ID,
      Hypergraph(..),
      Hyperedge, Vertex(..), isCZ, ids,getArgs)
import Test.QuickCheck.Test (test)


-- | Build the hypergraph for a given Circuit
--   Qubits are numbered 1..n in declaration order, CZ gates are globally numbered starting at n+1.
buildHypergraph :: Circuit -> Hypergraph
buildHypergraph circuit =
  let qs           = qubits circuit
      nQubits      = length qs
      startCZ      = nQubits + 1
      qIndexMap    = Map.fromList (zip qs [1..])

      -- flatten all primitives in declaration order with their positions
      allPrimsWithIdx :: [(Primitive, Int)]
      allPrimsWithIdx =
        [ (p, idx)
        | Decl _ _ (Seq stmts) <- decls circuit
        , (Gate p, idx)       <- zip stmts [0..]
        ]

      -- assign global CZ indices by original position
      czPositions = [ pos | (p,pos) <- allPrimsWithIdx, isCZ p ]
      czMap       = Map.fromList $ zip czPositions [startCZ..]

      -- extract primitives acting on q, keeping their positions
      qubitGatesWithIdx q =
        [ (p,pos)
        | (p,pos) <- allPrimsWithIdx
        , q `elem` getArgs p
        ]

      -- process each wire into its hyperedges (emitting only after seeing a CZ)
      buildForWire q =
        let wireIdx = qIndexMap Map.! q
            prims   = qubitGatesWithIdx q
            -- Stateful walk: czSeen tracks if we've started a hedge
            go :: Bool -> Hyperedge -> [(Primitive,Int)] -> [Hyperedge]
            -- End of list: emit only if we saw a CZ
            go czSeen hedge []
              | czSeen    = [hedge]
              | otherwise = []
            go czSeen hedge ((g,pos):ps)
              -- extend hedge on CZ
              | isCZ g && wireIdx `elem` map (qIndexMap Map.!) (getArgs g) =
                  let idx    = czMap Map.! pos
                      hedge' = if czSeen
                               then Set.insert (GateIdx idx) hedge
                               else Set.fromList [Wire wireIdx, GateIdx idx]
                  in go True hedge' ps
              -- on non-CZ, flush previous hedge if any, reset
              | otherwise =
                  let out = if czSeen then [hedge] else []
                  in out ++ go False Set.empty ps
        in go False Set.empty prims

      -- collect all hyperedges and vertices
      hs = concatMap buildForWire qs
      vs = Set.unions hs
  in Hypergraph vs hs

-- | Extract the numeric ID from a Vertex
vertexNum :: Vertex -> Int
vertexNum (Wire i) = i
vertexNum (GateIdx i) = i

hypToString :: Hypergraph -> String
hypToString (Hypergraph vs hs) =
  let numH      = length hs
      numV      = Set.size vs
      header    = unwords [show numH, show numV, "10"]
      edgeLines =
        [ unwords . map show . sort . map vertexNum . Set.toList $ hedge
        | hedge <- hs
        ]
  in unlines (header : edgeLines)

-- | Write a hypergraph to a .hgr file under the "Temp" directory (created if missing).
--   The file will be named <name>.hgr.
writeHypToFile :: String -> Hypergraph -> IO FilePath
writeHypToFile name hyp = do
  let dir      = "Temp"
      filePath = dir </> name <.> "hgr"
      contents = hypToString hyp
  createDirectoryIfMissing True dir
  writeFile filePath contents
  return filePath

-- runHypExample :: IO ()
-- runHypExample = do
--   let hyp = buildHypergraph testCircuit2
--   path <- writeHypToFile "testCircuit" hyp
--   putStrLn $ "Hypergraph written to: " ++ path


-- | Run the example: write the hypergraph, then invoke KaHyPar.
runHypExample :: IO ()
runHypExample = do
  let name    = "testCircuit"
      tempDir = "Temp"
      k       = Cfg.numParts  -- number of partitions
  -- build and write hypergraph
  let hyp = buildHypergraph testCircuit2
  filePath <- writeHypToFile name hyp
  putStrLn $ "Hypergraph written to: " ++ filePath

  -- ensure the file exists before calling KaHyPar
  exists <- doesFileExist filePath
  unless exists $
    error $ "Hypergraph file not found: " ++ filePath

  -- run KaHyPar CLI
  let outputPrefix  = tempDir </> "km1"
      partitionFile = outputPrefix <.> "hgr"
  callProcess "KaHyPar"
    [ "-h", filePath
    , "-k", show k
    , "-e", Cfg.epsilon
    , "-m", "direct"
    , "-o", outputPrefix
    , "-p", Cfg.subalgorithm
    , "-w", "true"
    , "-q", "true"
    ]
  putStrLn $ "Partition written to: " ++ partitionFile



-- Unit circuit tests
testCircuit :: Circuit
testCircuit = Circuit { qubits = ["a", "b", "c", "d"],
                    inputs = Set.fromList ["a", "b", "c", "d"],
                    decls  = [test] }
    where test = Decl { name = "main",
                       params = [],
                       body = Seq [
                                      Gate $ CZ "a" "c", Gate $ CZ "b" "c", Gate $ H "c",
                                      Gate $ H "b", Gate $ CZ "c" "d", Gate $ H "c", Gate $ CZ "b" "c", Gate $ H "d", Gate $ CZ "b" "d"
                                  ] }

testCircuit1 :: Circuit
testCircuit1 = Circuit { qubits = ["a", "b", "c", "d"],
                    inputs = Set.fromList ["a", "b", "c", "d"],
                    decls  = [test] }
    where test = Decl { name = "main",
                       params = [],
                       body = Seq [
                                      Gate $ H "d", Gate $ CZ "b" "d", Gate $ H "c", Gate $ CZ "b" "c",
                                      Gate $ H "a", Gate $ CZ "a" "b", Gate $ H "a", Gate $ H "b",
                                      Gate $ CZ "a" "b", Gate $ CZ "a" "c", Gate $ CZ "a" "d",
                                      Gate $ H "b", Gate $ H "c", Gate $ H "d"
                                  ] 
                      }


testCircuit2 :: Circuit
testCircuit2 = Circuit { qubits = ["a", "b", "c", "d"],
                    inputs = Set.fromList ["a", "b", "c", "d"],
                    decls  = [test] }
    where test = Decl { name = "main",
                       params = [],
                       body = Seq [
                                      Gate $ H "a", Gate $ CZ "a" "b", Gate $ H "a", Gate $ H "b",
                                      Gate $ CZ "a" "b", Gate $ H "a", Gate $ H "b", Gate $ CZ "a" "b",
                                      Gate $ CZ "b" "c", Gate $ H "c", Gate $ CZ "c" "d",
                                      Gate $ H "c", Gate $ H "d", Gate $ CZ "c" "d", Gate $ H "b", Gate $ H "d"  
                                  ] 
                      }
