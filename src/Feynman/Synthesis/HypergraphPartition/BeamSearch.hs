module Feynman.Synthesis.HypergraphPartition.BeamSearch
  ( wireVertices
  , blockWireWeight
  , isBalanced
  , allBalancedWirePartitions
  , flipVertex
  , flipNeighbours
  , swapNeighbours
  , neighbours
  , dedupPartitions
  , beamSearchWith
  , exhaustiveSearchWith
  ) where

import Feynman.Core (Block, Vertex(..))

import Data.List (minimumBy, sortBy)
import Data.Ord (comparing)

import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set

{- Partition helpers -}

-- The Wire vertices of a partition (parity/GateIdx vertices are ignored).
wireVertices :: Map Vertex Block -> [Vertex]
wireVertices pm = [ v | v@(Wire _) <- Map.keys pm ]

-- Weight of a block = count of Wire vertices assigned to it (parities weigh 0).
blockWireWeight :: Block -> Map Vertex Block -> Int
blockWireWeight b pm =
  length [ () | (Wire _, p) <- Map.toList pm, p == b ]

-- Balance / validity gate for a 2-block assignment.
isBalanced :: Double -> Map Vertex Block -> Bool
isBalanced eps pm =
  let totalWireWeight = length (wireVertices pm)
      k = 2
      perfect = ceiling (fromIntegral totalWireWeight / fromIntegral k :: Double)
      maxW    = floor  ((1 + eps) * fromIntegral perfect :: Double)
      w0 = blockWireWeight 0 pm
      w1 = blockWireWeight 1 pm
  in w0 <= maxW && w1 <= maxW && w0 > 0 && w1 > 0
     -- both blocks non-empty (in wires) keeps the 2-QPU split meaningful

-- Every balanced 0/1 assignment of the template's Wire vertices.
-- Exponential in the number of wires: only use on small circuits.
allBalancedWirePartitions :: Double -> Map Vertex Block -> [Map Vertex Block]
allBalancedWirePartitions eps template =
  filter (isBalanced eps) (assign wires base)
  where
    wires = wireVertices template
    base  = foldr Map.delete template wires

    assign [] pm     = [pm]
    assign (w:ws) pm =
      assign ws (Map.insert w 0 pm) ++ assign ws (Map.insert w 1 pm)

{- Neighbourhood -}

-- Flip a single vertex to the other block (0 <-> 1).
flipVertex :: Vertex -> Map Vertex Block -> Map Vertex Block
flipVertex v pm =
  let cur = Map.findWithDefault 0 v pm
      new = if cur == 0 then 1 else 0
  in Map.insert v new pm

flipNeighbours :: Double -> Map Vertex Block -> [Map Vertex Block]
flipNeighbours eps pm =
  filter (isBalanced eps) (map (`flipVertex` pm) (Map.keys pm))

-- Swapping one wire from each block keeps block weights unchanged,
-- so no balance check is needed here.
swapNeighbours :: Map Vertex Block -> [Map Vertex Block]
swapNeighbours pm =
  let wires0 = [ v | v@(Wire _) <- Map.keys pm, Map.findWithDefault 0 v pm == 0 ]
      wires1 = [ v | v@(Wire _) <- Map.keys pm, Map.findWithDefault 0 v pm == 1 ]
      doSwap a b = Map.insert a 1 (Map.insert b 0 pm)  -- a:0->1, b:1->0
      allPairs = [ doSwap a b | a <- wires0, b <- wires1 ]
      -- Optional cap to bound neighbourhood size on large instances.
      maxSwapPairs = 400
  in take maxSwapPairs allPairs

neighbours :: Double -> Map Vertex Block -> [Map Vertex Block]
neighbours eps pm = flipNeighbours eps pm ++ swapNeighbours pm

-- Deduplicate partitions by their assignment list (avoids re-scoring identical maps).
dedupPartitions :: [Map Vertex Block] -> [Map Vertex Block]
dedupPartitions = go Set.empty
  where
    go _ [] = []
    go seen (pm:rest) =
      let key = Map.toAscList pm
      in if Set.member key seen
         then go seen rest
         else pm : go (Set.insert key seen) rest

{- Search strategies -}

-- Beam search over partitions, given any scoring function. Returns the best
-- partition found and its score.
beamSearchWith :: (Map Vertex Block -> Int) -> Map Vertex Block -> Double -> Int -> Int
               -> (Map Vertex Block, Int)
beamSearchWith score seed eps beamWidth depth =
  let seedScored = (seed, score seed)

      -- one round: expand every partition in the beam, dedup, keep best beamWidth
      step :: [(Map Vertex Block, Int)] -> [(Map Vertex Block, Int)]
      step beam =
        let expanded   = concatMap (\(pm,_) -> neighbours eps pm) beam
            -- include current beam so search is monotone (never loses the best)
            pool       = map fst beam ++ expanded
            uniquePool = dedupPartitions pool
            scored     = [ (pm, score pm) | pm <- uniquePool ]
        in take beamWidth (sortBy (comparing snd) scored)

      finalBeam = iterate step [seedScored] !! depth
  in minimumBy (comparing snd) (seedScored : finalBeam)

-- Exhaustive search over every balanced wire assignment, given any scoring
-- function. Only the seed's non-wire vertices are kept as-is.
exhaustiveSearchWith :: (Map Vertex Block -> Int) -> Map Vertex Block -> Double
                     -> (Map Vertex Block, Int)
exhaustiveSearchWith score seed eps =
  minimumBy (comparing snd)
    [ (pm, score pm) | pm <- allBalancedWirePartitions eps seed ]