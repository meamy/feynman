module Feynman.Synthesis.HGraphBuilder where
import qualified Data.Map as Map
import           Data.Map   (Map)
import           Data.List  (nub)

import Feynman.Core
    ( Primitive,
      MaxHedgeDist,
      PartAlg(..),
      ID,
      Hypergraph,
      Segment,
      isClassical,
      targetOf )

-- | Build the hypergraph from a list of primitives
buildHyp :: MaxHedgeDist -> Int -> [Primitive] -> Hypergraph
buildHyp maxHedgeDist nQubits gs =
  Map.map (filter (\(_, ws, _) -> not (null ws)))
    $ Map.map splitLongHedges hyp
  where
    -- initial hypergraph, converting negative aux wires to positive
    hyp = Map.map
            (map (\(i, ws, o) -> (i, map (\(w,p) -> (nQubits - w - 1, p)) ws, o)))
          $ buildHypRec gs 0 0

    splitLongHedges [] = []
    splitLongHedges ((i, ws, o) : hs)
      | maxHedgeDist == 1 =
          map (\(w,p) -> (p, [(w,p)], p+1)) ws ++ splitLongHedges hs
      | maxHedgeDist < (o - i) =
          let x = i + ((o - i) `div` 2) in
          splitLongHedges ((i, takeWhile (before x) ws, x)
                          : (x, dropWhile (before x) ws, o) : hs)
      | otherwise = (i, ws, o) : splitLongHedges hs

    before x (_, p) = p < x

-- | Recursively build hypergraph from primitive list
buildHypRec :: [Primitive] -> Int -> Int -> Hypergraph
buildHypRec [] _ _ = Map.empty
buildHypRec (g:gs) pos czVertex
  | isClassical g = buildHypRec gs (pos + 1) czVertex
  | otherwise    = case g of
      -- CZ gates create hyperedges on both control and target wires
      CZ x y -> newCZAt [x, y]
        where
          newCZAt []     = buildHypRec gs (pos + 1) (czVertex - 1)
          newCZAt (w:ws) =
            Map.alter (addCZ czVertex) w (newCZAt ws)

          addCZ v Nothing                = Just [(0, [(v-1, pos)], pos + 1)]
          addCZ v (Just ((_, ws, o) : es)) =
            Just ((0, (v-1, pos):ws, o) : es)

      -- All other gates produce a hyperedge on the primary target wire
      _ -> case targetOf g of
        Just wire -> Map.alter addHedge wire next
        Nothing   -> error $ "Gate " ++ show g ++ " was not properly preprocessed."
        where
          next = buildHypRec gs (pos + 1) czVertex

          addHedge Nothing                     = Just [(0, [], pos)]
          addHedge (Just ((_, ws, o) : es)) =
            Just ((0, [], pos) : (pos+1, ws, o) : es)

-- buildHyp :: Int -> [Primitive] -> Hypergraph
-- buildHyp maxHedgeDist gs = 
--   let n = length gs
--       (hyp, _) = buildHypRec (reverse gs) (n-1) 0 Map.empty
--       splitLong (i, ws, o) 
--         | maxHedgeDist <= 0 || o - i <= maxHedgeDist = [(i, ws, o)]
--         | otherwise = 
--             let mid = i + (o - i) `div` 2
--                 (ws1, ws2) = span (\(_, pos) -> pos < mid) ws
--             in [(i, ws1, mid)] ++ splitLong (mid, ws2, o)
--       processHedges = Map.map (concatMap splitLong . filter (\(_, ws, _) -> not $ null ws))
--   in processHedges hyp

-- buildHypRec :: [Primitive] -> Int -> Int -> Hypergraph -> (Hypergraph, Int)
-- buildHypRec [] _ nextVertex hyp = (hyp, nextVertex)
-- buildHypRec (g:gs) pos nextVertex hyp
--   | isClassical g = buildHypRec gs (pos-1) nextVertex hyp
--   | otherwise = case g of
--       CZ c t -> 
--         let wires = [c, t]
--             updateWire w h = 
--               case Map.lookup w h of
--                 Nothing -> Map.insert w [(pos, [(nextVertex, pos)], pos+1)] h
--                 Just (hedge@(i, ws, o):hedges) -> 
--                   Map.insert w ((i, (nextVertex, pos):ws, o) : hedges) h
--             newHyp = foldr updateWire hyp wires
--         in buildHypRec gs (pos-1) (nextVertex+1) newHyp
--       _ -> 
--         case targetOf g of
--           Just target -> 
--             let update = Map.alter (\case
--                   Nothing -> Just [(pos, [], pos+1)]
--                   Just hedges -> Just $ (pos, [], pos+1) : hedges
--                 ) target
--                 newHyp = update hyp
--             in buildHypRec gs (pos-1) nextVertex newHyp
--           Nothing -> buildHypRec gs (pos-1) nextVertex hyp


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
