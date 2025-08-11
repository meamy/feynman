module Feynman.Synthesis.HypergraphPartition.HGraphBuilder where
import qualified Data.Map as Map
import           Data.Map   (Map)

import           Data.List (isPrefixOf, isInfixOf, maximumBy, sort)

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Ord (comparing)

import System.Directory (doesFileExist, renameFile, removeFile, listDirectory, createDirectoryIfMissing ,getModificationTime)
import System.FilePath  ((</>), (<.>))
import System.Process (callProcess)
import qualified Feynman.Synthesis.HypergraphPartition.PartitionConfigs as Cfg
import Control.Monad (unless,  when)


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

packCircuit :: [Primitive] -> Circuit
packCircuit circ = Circuit { qubits = ids circ,
                             inputs = Set.fromList (ids circ),
                             decls  = [main] }
    where main = Decl { name = "main",
                        params = [],
                        body = Seq $ map Gate circ
                      }

-- | Build the hypergraph for a given Circuit
--   Qubits are numbered 1..n in declaration order, CZ gates are globally numbered starting at n+1.
buildHypergraph :: Circuit -> (Int, Hypergraph)
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
  in (nQubits, Hypergraph vs hs)

-- | Extract the numeric ID from a Vertex
vertexNum :: Vertex -> Int
vertexNum (Wire i) = i
vertexNum (GateIdx i) = i

hypToString :: Int -> Hypergraph -> String
hypToString nQubits (Hypergraph vs hs) =
  let numH      = length hs
      numV      = Set.size vs
      header    = unwords [show numH, show numV, "10"]
      edgeLines =
        [ unwords . map show . sort . map vertexNum . Set.toList $ hedge
        | hedge <- hs
        ]
      weights     = [1 | _ <- [1..nQubits]]
                 ++ [0 | _ <- [nQubits+1..numV]]
      weightLines = map show weights
  in unlines $ header : edgeLines ++ weightLines

-- | Write a hypergraph to a .hgr file under the "Temp" directory (created if missing).
--   The file will be named <name>.hgr.
writeHypToFile :: String -> Int -> Hypergraph -> IO FilePath
writeHypToFile name nQubits hyp = do
  let dir      = "Temp"
      filePath = dir </> name <.> "hgr"
      contents = hypToString nQubits hyp
  createDirectoryIfMissing True dir
  writeFile filePath contents
  return filePath

-- | Build and partition, invoking KaHyPar with correct flags
runHypExample :: IO ()
runHypExample = do
  let name    = "testCircuit"
      tempDir = "Temp"
      k       = Cfg.numParts
      objective = "km1"
      kahypar = Cfg.kahyparPath

  -- Build and write hypergraph
  let (nQuibits, hyp) = buildHypergraph testGraysynth
  filePath <- writeHypToFile name nQuibits hyp
  putStrLn $ "Hypergraph written to: " ++ filePath

  -- Ensure .hgr exists
  exists <- doesFileExist filePath
  unless exists $
    error $ "Hypergraph file not found: " ++ filePath

  -- Ensure KahyPar binary exists
  execExists <- doesFileExist kahypar
  unless execExists $
    error $ "Cannot find KahyPar executable at: " ++ kahypar

  -- Invoke KaHyPar: specify objective, config, and output folder
  callProcess kahypar
    [ 
      "-h", filePath, 
      "-k", show k, 
      "-e", Cfg.epsilon, 
      "-o", objective,                      -- objective name (km1)
      "-m", "direct",
      "-p", Cfg.subalgorithm,                -- config .ini path
      "-w", "true"
    ]

  putStrLn $ "Partition file written to: " ++ tempDir </> (objective <.> "hgr")

-- | Build and partition, invoking KaHyPar with correct flags
getNumCuts :: [Primitive] -> IO [Primitive]
getNumCuts circ = do
  let tempDir      = "Temp"
      hypergraphFN = "hypergraph.hgr"
      partitionFN  = "partion.hgr"     -- (spelled as requested)
      hypergraphFP = tempDir </> hypergraphFN
      partitionFP  = tempDir </> partitionFN
      k            = Cfg.numParts
      kahypar      = Cfg.kahyparPath

  -- Build and write hypergraph (initial path may differ; we rename to hypergraph.hgr)
  let (nQuibits, hyp) = buildHypergraph $ packCircuit circ
  filePath <- writeHypToFile "hypergraph" nQuibits hyp       -- write with base "hypergraph"
  -- Ensure it ends up exactly at Temp/hypergraph.hgr
  when (filePath /= hypergraphFP) $ do
    existsInitial <- doesFileExist filePath
    unless existsInitial $
      error $ "Expected hypergraph file not found at: " ++ filePath
    renameFile filePath hypergraphFP
  putStrLn $ "Hypergraph written to: " ++ hypergraphFP

  -- Ensure .hgr exists
  exists <- doesFileExist hypergraphFP
  unless exists $
    error $ "Hypergraph file not found: " ++ hypergraphFP

  -- Ensure KaHyPar binary exists
  execExists <- doesFileExist kahypar
  unless execExists $
    error $ "Cannot find KaHyPar executable at: " ++ kahypar

  -- Invoke KaHyPar (writes a partition file like hypergraph.hgr.partK...KaHyPar)
  callProcess kahypar
    [ "-h", hypergraphFP
    , "-k", show k
    , "-e", Cfg.epsilon
    , "-o", "km1"
    , "-m", "direct"
    , "-p", Cfg.subalgorithm
    , "-w", "true"
    ]

  -- Find the latest KaHyPar-produced partition file and rename to partion.hgr
  candFiles <- listDirectory tempDir
  let isPart f = ("hypergraph.hgr.part" `isPrefixOf` f) || (".KaHyPar" `isInfixOf` f)
      parts    = [ f | f <- candFiles, isPart f ]
  when (null parts) $
    error "KaHyPar did not produce a partition file."
  times <- mapM (\f -> getModificationTime (tempDir </> f) >>= \t -> pure (f,t)) parts
  let latest = fst $ maximumBy (comparing snd) times
  -- rename latest to the exact requested filename
  existing <- doesFileExist partitionFP
  when existing $ removeFile partitionFP
  renameFile (tempDir </> latest) partitionFP
  putStrLn $ "Partition file written to: " ++ partitionFP

  return circ

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

testGraysynth :: Circuit
testGraysynth = Circuit { qubits = ["a", "b", "c", "d"],
                    inputs = Set.fromList ["a", "b", "c", "d"],
                    decls  = [test] }
    where test = Decl { name = "main",
                       params = [],
                       body = Seq [
                                      Gate $ H "b", Gate $ CZ "c" "d", Gate $ H "b",
                                      Gate $ Rz 1 "a", Gate $ Rz 1 "b", Gate $ H "a",
                                      Gate $ CZ "a" "d", Gate $ H "a", Gate $ Rz 1 "a",
                                      Gate $ H "a", Gate $ CZ "a" "b", Gate $ CZ "a" "d",
                                      Gate $ H "a", Gate $ Rz 1 "a", Gate $ H "a",
                                      Gate $ CZ "a" "c", Gate $ H "a", Gate $ Rz 1 "a", Gate $ H "a", Gate $ CZ "a" "d", Gate $ H "a", Gate $ Rz 1 "a", Gate $ H "a", Gate $ CZ "a" "b", Gate $ H "b", Gate $ CZ "b" "c", Gate $ H "b", Gate $ CZ "a" "d", Gate $ H "a"
                                  ] 
                      }
