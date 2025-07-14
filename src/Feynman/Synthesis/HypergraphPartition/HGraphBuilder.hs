module Feynman.Synthesis.HGraphBuilder where
import qualified Data.Map as Map
import           Data.Map   (Map)
import           Data.List  (nub)

import Data.Set (Set)
import qualified Data.Set as Set

import           System.Directory       (createDirectoryIfMissing)
import           System.FilePath        ((</>), (<.>))

import Feynman.Core
    ( Circuit(..),
      Primitive(..),
      PartAlg(..),
      getArgs,
      foldCirc,
      ID,
      Hypergraph,
      Segment,
      Hedge, isCZ, ids,getArgs)
      
-- | Top-level: given a flat list of Primitives (circuit), produce
--   * H: hypergraph mapping each wire ID to its list of hedges
-- buildHypergraph :: [Primitive] -> Hypergraph
-- buildHypergraph circuit =
--   let wires  = ids circuit                  -- all wire IDs in the circuit
--       events = zip [0..] circuit           -- annotate each gate with its position
--   in buildHypergraphHelper wires events    -- delegate to helper

flattenCircuit :: Circuit -> [Primitive]
flattenCircuit circ = reverse $ foldCirc collect [] circ
  where
    collect :: Stmt -> [Primitive] -> [Primitive]
    collect (Gate g) acc = g : acc
    collect _        acc = acc

-- Build a hypergraph from a full 'Circuit'
buildHypergraph :: Circuit -> Hypergraph
buildHypergraph circ =
  let prims  = flattenCircuit circ
      wires  = qubits circ
      events = zip [0..] prims
  in buildHypergraphHelper wires events

-- | Helper: constructs H from wire list and indexed events
buildHypergraphHelper :: [ID] -> [(Int, Primitive)] -> Hypergraph
buildHypergraphHelper wires events =
  Map.fromList [ (w, buildWireHedges w events) | w <- wires ]

-- | Build all hyperedges for a single wire
--   Scans through events touching this wire, grouping contiguous CZ segments
--   Each segment [n,m) becomes a Hedge (n, ws, m)
--   Non-CZ gates produce singleton hedges [(pos,[],pos+1)]
buildWireHedges :: ID -> [(Int, Primitive)] -> [Hedge]
buildWireHedges wire evsAll =
  let -- restrict to events on this wire
      evs :: [(Int, Primitive)]
      evs = [ (pos, g) | (pos, g) <- evsAll, wire `elem` getArgs g ]

      -- fold to accumulate hedges
      (hs, mStart, ws) = foldl (processEvent wire) ([], Nothing, []) evs

      -- determine lastPosition to flush remaining segment
      lastPos = case evs of [] -> 0; _ -> fst (last evs)

      -- flush final CZ segment if present, then trailing empty hedge
      finalHedges = case mStart of
        Just n  -> hs ++ [(n, ws, lastPos+1), (lastPos+1, [], lastPos+2)]
        Nothing -> hs ++ [(lastPos+1, [], lastPos+2)]
  in finalHedges

-- | Fold step: update accumulator for each event on a wire
--   * On CZ: start (or continue) a segment, collect other qubit IDs
--   * On non-CZ: flush any CZ segment, then create a singleton hedge
processEvent :: ID -> ([Hedge], Maybe Int, [(ID, Int)]) -> (Int, Primitive) -> ([Hedge], Maybe Int, [(ID, Int)])
processEvent wire (acc, mStart, ws) (pos, gate)
  | isCZ gate =
      let n       = case mStart of
                      Just start -> start
                      Nothing    -> pos
          others  = [ w | w <- getArgs gate, w /= wire ]
          ws'     = ws ++ map (\w -> (w,pos)) others      -- record other vertices with CZ position
      in (acc, Just n, ws')

  | otherwise =
      let -- flush current CZ segment if open
          acc' = case mStart of
                   Just n  -> acc ++ [(n, ws, pos)]
                   Nothing -> acc
          -- singleton hedge for this non-CZ gate
          singleton = (pos, [], pos+1)
      in (acc' ++ [singleton], Nothing, [])


-- | Count the number of “cuts” in a segment:
--   each hedge that spans B distinct blocks contributes (B–1) to the sum.
countCuts :: Segment -> Int
countCuts (_, hyp, part, _, _) =
  sum [ b - 1 | b <- blocksPerHedge ]
  where
    -- for each hedge, collect its vertex IDs,
    -- look up their blocks, de-duplicate, and count
    blocksPerHedge :: [Int]
    blocksPerHedge =
      [ length . nub . map (part Map.!) $ verts
      | verts <- flatData
      ]

    -- flatten the hypergraph to a list of hedges, each as [ID]
    flatData :: [[ID]]
    flatData =
      Map.foldrWithKey
        (\qid hedges acc ->
           let sets = [ qid : map fst wires | (_, wires, _) <- hedges ]
           in  sets ++ acc)
        []
        hyp

-- | Emit the .hgr file contents for your Hypergraph.
--   Returns (fileText, numHedges, numVertices).
hypToString :: PartAlg -> Hypergraph -> Int -> (String, Int, Int)
hypToString alg hyp nQubits = (fileData, nHedges, nVertices)
  where
    -- 1) turn each hedge into a list of vertex-IDs
    flatDataID :: [[ID]]
    flatDataID =
      Map.foldrWithKey
        (\qid hedges acc ->
           let sets = [ qid : map fst wires | (_, wires, _) <- hedges ]
           in  sets ++ acc)
        []
        hyp

    -- 2) assign each qubit-name an integer 1..#
    idList :: [ID]
    idList = nub $ concat flatDataID

    idMap :: Map ID Int
    idMap = Map.fromList (zip idList [1..])

    -- 3) convert each hedge to numbers
    flatDataNum :: [[Int]]
    flatDataNum = map (map (idMap Map.!)) flatDataID

    -- 4) counts
    nVertices :: Int
    nVertices = foldr (max . foldr max 0) 0 flatDataNum

    nHedges :: Int
    nHedges = length flatDataNum

    nPins :: Int
    nPins =
      nHedges +
      sum [ length wires | hedges <- Map.elems hyp, (_, wires, _) <- hedges ]

    -- 5) first line differs by partitioner
    fstLine :: [String]
    fstLine = case alg of
      Kahypar -> [ show nHedges, show nVertices, "10" ]
      Patoh   -> [ "1", show nVertices, show nHedges, show nPins, "1" ]

    -- 6) vertex weights: 1 for first nQubits, then 0
    verticesWeights :: [[String]]
    verticesWeights =
      replicate nQubits ["1"] ++ replicate (nVertices - nQubits) ["0"]

    -- 7) assemble all lines
    fileData :: String
    fileData = unlines . map unwords $
      fstLine
      : map (map show . nub) flatDataNum
      ++ verticesWeights

writeHypergraphFile
  :: PartAlg
  -> Hypergraph
  -> Int        -- ^ nQubits
  -> FilePath   -- ^ base name (e.g. "circuit1")
  -> IO ()
writeHypergraphFile alg hyp nQubits base = do
  let (fileData, _nH, _nV) = hypToString alg hyp nQubits
      dir  = "HypergraphPartition" </> "temp"
      path = dir </> base <.> "hgr"
  -- ensure the directory exists
  createDirectoryIfMissing True dir
  writeFile path fileData
