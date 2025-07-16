module Feynman.Synthesis.HypergraphPartition.HGraphBuilder where
import qualified Data.Map as Map
import           Data.Map   (Map)

import           Data.List (sort)

import Data.Set (Set)
import qualified Data.Set as Set

import System.Directory (createDirectoryIfMissing)
import System.FilePath  ((</>), (<.>))

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
  let qs        = qubits circuit
      nQubits   = length qs
      startCZ   = nQubits + 1
      -- map each qubit ID to its Int index
      qIndexMap = Map.fromList (zip qs [1..])

      -- flatten all primitives in declaration order with their positions
      allPrimsWithIdx :: [(Primitive, Int)]
      allPrimsWithIdx =
        [ (p, idx)
        | Decl _ _ (Seq stmts) <- decls circuit
        , (Gate p, idx)       <- zip stmts [0..]
        ]

      -- assign global CZ indices by original position
      czPositions = [ pos | (p,pos) <- allPrimsWithIdx, isCZ p ]
      czMap :: Map.Map Int Int
      czMap = Map.fromList $ zip czPositions [startCZ..]

      -- extract primitives acting on q, keeping their positions
      qubitGatesWithIdx q =
        [ (p,pos)
        | (p,pos) <- allPrimsWithIdx
        , q `elem` getArgs p
        ]

      -- process each wire into its vertices and hyperedges
      buildForWire q =
        let wireIdx = qIndexMap Map.! q
            prims   = qubitGatesWithIdx q
            go hedge [] = (Set.toList hedge, [hedge])
            go hedge ((g,pos):xs)
              -- global CZ check: lookup its index by position
              | isCZ g && wireIdx `elem` map (qIndexMap Map.!) (getArgs g)
                = let idx    = czMap Map.! pos
                      hedge' = Set.insert (GateIdx idx) hedge
                  in go hedge' xs
              | otherwise
                = let (vsRest, hsRest) = go (Set.singleton (Wire wireIdx)) xs
                  in (Wire wireIdx : vsRest, hedge : hsRest)
        in go (Set.singleton (Wire wireIdx)) prims

      allResults = map buildForWire qs
      vs         = Set.unions (map (Set.fromList . fst) allResults)
      hs         = concatMap snd allResults
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

runHypExample :: IO ()
runHypExample = do
  let hyp = buildHypergraph testCircuit
  path <- writeHypToFile "testCircuit" hyp
  putStrLn $ "Hypergraph written to: " ++ path


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

