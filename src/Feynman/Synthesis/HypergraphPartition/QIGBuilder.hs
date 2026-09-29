{-|
Quantum Interaction Graph (QIG), following Azenha, Polian & Brandhofer,
"Scalable Transpilation for Overcoming Restricted Connectivity in
Distributed Superconducting Quantum Architectures", Sec. V-C.

  * vertices     : virtual qubits, numbered 1..n (same convention as
                   'Wire i' in HGraphBuilder, so partitions line up)
  * edge {i, j}  : qubits i and j act together in at least one gate
  * edge weight  : total number of such gates over the WHOLE circuit
                   (one global graph, not time-sliced)

Gates on 3+ qubits (Ctrl, Uninterp) are clique-expanded: every pair of
their qubits gets +1. Single-qubit gates, Measure and Reset add nothing.
-}
module Feynman.Synthesis.HypergraphPartition.QIGBuilder
  ( QIG(..)
  , buildQIG
  , buildQIGFromPrims
  , buildQIGOver
  , qigWeight
  , qigCut
  , qigToHypergraph
  , qigToHMetis
  , partitionQIG
  ) where

import qualified Data.Map as Map
import           Data.Map   (Map)
import qualified Data.Set as Set
import           Data.List  (foldl', tails, isPrefixOf)
import           Data.Maybe (mapMaybe)
import           Control.Monad (forM_, when)
import           System.Directory (createDirectoryIfMissing, listDirectory, removeFile)
import           System.Exit (ExitCode(..))
import           System.FilePath ((</>))
import           System.IO (hPutStrLn, stderr)
import           System.Process (readProcessWithExitCode)

import qualified Feynman.Synthesis.HypergraphPartition.PartitionConfigs as Cfg

import Feynman.Core
    ( Circuit(..), Decl(..), Stmt(..), Primitive, ID
    , getArgs, ids, Hypergraph(..), Vertex(..) )

data QIG = QIG
  { qigNumQubits :: Int
  , qigIndex     :: Map ID Int          -- qubit name -> vertex (1-based)
  , qigEdges     :: Map (Int, Int) Int  -- (i, j) with i < j -> gate count
  } deriving (Show)

-- | Build the QIG from a Circuit. Nested 'Seq' blocks are flattened and
--   'Repeat k' multiplies the weights of its body by k. 'Call' statements
--   are not inlined, so inline subroutines first if your circuits use them.
buildQIG :: Circuit -> QIG
buildQIG circuit = accumulate (qubits circuit) weighted
  where
    weighted = concatMap (flatten 1 . body) (decls circuit)

    flatten :: Int -> Stmt -> [(Primitive, Int)]
    flatten k (Gate g)     = [(g, k)]
    flatten k (Seq st)     = concatMap (flatten k) st
    flatten k (Repeat i s) = flatten (k * i) s
    flatten _ (Call _ _)   = []

-- | Build the QIG from a flat gate list, as 'getNumCuts' receives it.
--   Uses 'ids circ' for numbering, matching the qIndexMap in 'getNumCuts'.
buildQIGFromPrims :: [Primitive] -> QIG
buildQIGFromPrims circ = accumulate (ids circ) [ (g, 1) | g <- circ ]

-- | Build the QIG over an explicit qubit list, so declared-but-idle qubits
--   still get a vertex. Qubits used by the circuit but missing from the list
--   are appended, so every qubit the circuit touches is always a vertex.
buildQIGOver :: [ID] -> [Primitive] -> QIG
buildQIGOver qs circ = accumulate allQs [ (g, 1) | g <- circ ]
  where
    declared = Set.fromList qs
    allQs    = qs ++ [ q | q <- ids circ, not (Set.member q declared) ]

accumulate :: [ID] -> [(Primitive, Int)] -> QIG
accumulate qs gates = QIG (length qs) qIndexMap (foldl' addGate Map.empty gates)
  where
    qIndexMap = Map.fromList (zip qs [1..])

    addGate acc (g, k) =
      let vs    = Set.toAscList . Set.fromList
                $ mapMaybe (`Map.lookup` qIndexMap) (getArgs g)
          pairs = [ (a, b) | (a:rest) <- tails vs, b <- rest ]   -- a < b
      in foldl' (\m p -> Map.insertWith (+) p k m) acc pairs

-- | Interaction weight between two vertices (0 if they never interact).
--   Handy for the capacity-enforcement and boundary-reallocation passes.
qigWeight :: QIG -> Int -> Int -> Int
qigWeight qig i j
  | i == j    = 0
  | otherwise = Map.findWithDefault 0 (min i j, max i j) (qigEdges qig)

-- | Total weight of QIG edges whose endpoints sit in different blocks,
--   i.e. the number of two-qubit gates that cross QPUs under this assignment.
qigCut :: QIG -> Map ID Int -> Int
qigCut qig assignment =
  sum [ w | ((a, b), w) <- Map.toList (qigEdges qig), blockOf a /= blockOf b ]
  where
    byIdx     = Map.fromList [ (i, Map.findWithDefault 0 q assignment)
                             | (q, i) <- Map.toList (qigIndex qig) ]
    blockOf i = Map.findWithDefault 0 i byIdx

-- | View the QIG as your existing Hypergraph type (every hyperedge has
--   exactly two pins). Isolated qubits are kept in the vertex set.
qigToHypergraph :: QIG -> Hypergraph
qigToHypergraph (QIG n _ es) = Hypergraph vs hes
  where
    vs  = Set.fromList [ Wire i | i <- [1..n] ]
    hes = [ (Set.fromList [Wire a, Wire b], w) | ((a, b), w) <- Map.toList es ]

-- | Serialize for KaHyPar in hMetis format with EDGE weights (fmt = 1).
--   Do not use 'hypToString' here: it writes fmt 10 (vertex weights only),
--   so KaHyPar would ignore the gate counts.
qigToHMetis :: QIG -> String
qigToHMetis (QIG n _ es) = unlines (header : edgeLines)
  where
    header    = unwords [show (Map.size es), show n, "1"]
    edgeLines = [ unwords [show w, show a, show b] | ((a, b), w) <- Map.toList es ]

-- | Build the QIG over the given qubits, partition it into @numParts@ blocks
--   with KaHyPar, and return the graph together with the assignment
--   qubit -> block (0 .. k-1). Every qubit in @qs@ and every qubit the
--   circuit touches gets a block, idle ones included.
--
--   Uses the same KaHyPar settings as 'getNumCuts' (Cfg.kahyparPath,
--   Cfg.epsilon, Cfg.subalgorithm, km1 objective, direct mode), but its own
--   file names (qig.hgr / qig.partition), so the parity-hypergraph files are
--   left alone.
partitionQIG :: Int -> [ID] -> [Primitive] -> IO (QIG, Map ID Int)
partitionQIG numParts qs circ = do
  let qig       = buildQIGOver qs circ
      n         = qigNumQubits qig
      k         = min numParts (max 1 n)
      byIdx     = Map.fromList [ (i, q) | (q, i) <- Map.toList (qigIndex qig) ]
      toAssign blocks = Map.fromList [ (byIdx Map.! i, b) | (i, b) <- zip [1 ..] blocks ]

  if k <= 1 || Map.null (qigEdges qig)
    then do
      -- Nothing to cut (one block, or no multi-qubit gates): KaHyPar has no
      -- work to do and may reject an edgeless graph, so split evenly instead.
      let blocks = [ ((i - 1) * k) `div` max 1 n | i <- [1 .. n] ]
      return (qig, toAssign blocks)
    else do
      blocks <- runKaHyPar k n (qigToHMetis qig)
      return (qig, toAssign blocks)

-- | Write an hMetis file, run KaHyPar on it and read back one block per vertex.
runKaHyPar :: Int -> Int -> String -> IO [Int]
runKaHyPar k n hmetis = do
  let dir        = Cfg.hypergraphPartitionDataPath
      graphFN    = "qig.hgr"
      graphFP    = dir </> graphFN
      partFP     = dir </> "qig.partition"
      isQigPart f = (graphFN ++ ".part") `isPrefixOf` f

  createDirectoryIfMissing True dir

  -- Remove partition files from earlier runs, so the one we read is fresh.
  old <- filter isQigPart <$> listDirectory dir
  forM_ old (removeFile . (dir </>))

  writeFile graphFP hmetis

  let args = [ "-h", graphFP
             , "-k", show k
             , "-e", show Cfg.epsilon
             , "-o", "km1"
             , "-m", "direct"
             , "-p", Cfg.subalgorithm
             , "-w", "true" ]
  (ec, out, err) <- readProcessWithExitCode Cfg.kahyparPath args ""
  case ec of
    ExitSuccess -> pure ()
    _ -> do
      hPutStrLn stderr $ "KaHyPar failed on the QIG.\n--- stdout ---\n" ++ out
                      ++ "\n--- stderr ---\n" ++ err
      ioError (userError "partitionQIG: KaHyPar exited with an error.")

  -- KaHyPar names its output <graph>.part<k>.epsilon<e>.seed<s>.KaHyPar
  produced <- filter isQigPart <$> listDirectory dir
  partFile <- case produced of
    [f] -> pure (dir </> f)
    []  -> ioError (userError "partitionQIG: KaHyPar did not produce a partition file.")
    fs  -> ioError (userError ("partitionQIG: several partition files found: " ++ unwords fs))

  contents <- readFile partFile
  let blocks = map read (lines contents) :: [Int]
  when (length blocks /= n) $
    ioError (userError ("partitionQIG: expected " ++ show n ++ " blocks, got "
                        ++ show (length blocks)))

  -- Keep a stable copy next to the other partition files, for inspection.
  writeFile partFP contents
  removeFile partFile
  return blocks