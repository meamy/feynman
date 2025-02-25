{-# LANGUAGE ImportQualifiedPost #-}

module Feynman.Synthesis.XAG.Simplify
  ( mergeStructuralDuplicates,
    mergeStructuralDuplicateNodes,
  )
where

import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (Maybe (..))
import Feynman.Synthesis.XAG.Graph qualified as XAG

data MergeState = MergeState
  { mergeFalse :: Maybe Int,
    mergeTrue :: Maybe Int,
    mergeNot :: IntMap Int,
    mergeXor :: Map (Int, Int) Int,
    mergeAnd :: Map (Int, Int) Int,
    mergeMapping :: IntMap Int,
    mergeNodesRev :: [XAG.Node]
  }

-- Within a graph, merge nodes to canonical nodes performing the same
-- computation. This is fairly light and only merges by structure, graphs with
-- predictable structure may benefit most -- should be equivalent to ABC's
-- structural hashing, AKA "strash"
mergeStructuralDuplicates :: XAG.Graph -> XAG.Graph
mergeStructuralDuplicates inputGraph =
  XAG.Graph finalNodes (XAG.inputIDs inputGraph) finalOutputIDs
  where
    finalOutputIDs =
      map (\nID -> IntMap.findWithDefault nID nID finalMapping) (XAG.outputIDs inputGraph)
    (finalNodes, finalMapping) = mergeStructuralDuplicateNodes (XAG.nodes inputGraph)

mergeStructuralDuplicateNodes :: [XAG.Node] -> ([XAG.Node], IntMap Int)
mergeStructuralDuplicateNodes inputNodes =
  (reverse finalNodesRev, finalMapping)
  where
    MergeState
      { mergeNodesRev = finalNodesRev,
        mergeMapping = finalMapping
      } =
        foldl checkAndMergeNode emptyMerge inputNodes

    checkAndMergeNode :: MergeState -> XAG.Node -> MergeState
    checkAndMergeNode s@(MergeState {mergeFalse = Nothing}) n@(XAG.Const nID False) =
      (keepNode n s) {mergeFalse = Just nID}
    checkAndMergeNode s@(MergeState {mergeFalse = Just mID}) n@(XAG.Const nID False) =
      mergeNode nID mID s
    checkAndMergeNode s@(MergeState {mergeTrue = Nothing}) n@(XAG.Const nID True) =
      (keepNode n s) {mergeTrue = Just nID}
    checkAndMergeNode s@(MergeState {mergeTrue = Just mID}) n@(XAG.Const nID True) =
      mergeNode nID mID s
    checkAndMergeNode s n@(XAG.Not nID xID) =
      case IntMap.lookup canonXID (mergeNot s) of
        -- If it's not in the "not" map, add it. Add the original source as the
        -- negation of this not, too, in case anyone goes looking for that
        Nothing ->
          (keepNode (XAG.Not nID canonXID) s)
            { mergeNot = IntMap.insert nID canonXID (IntMap.insert canonXID nID (mergeNot s))
            }
        Just mID -> mergeNode nID mID s
      where
        canonXID = IntMap.findWithDefault xID xID (mergeMapping s)
    checkAndMergeNode s n@(XAG.Xor nID xID yID)
      | canonXID == canonYID = checkAndMergeNode s (XAG.Const nID False)
      | canonXID > canonYID = checkAndMergeNode s (XAG.Xor nID canonYID canonXID)
      | otherwise =
          case Map.lookup (canonXID, canonYID) (mergeXor s) of
            Nothing ->
              (keepNode (XAG.Xor nID canonXID canonYID) s)
                { mergeXor = Map.insert (canonXID, canonYID) nID (mergeXor s)
                }
            Just mID -> mergeNode nID mID s
      where
        canonXID = IntMap.findWithDefault xID xID (mergeMapping s)
        canonYID = IntMap.findWithDefault yID yID (mergeMapping s)
    checkAndMergeNode s n@(XAG.And nID xID yID)
      | canonXID == canonYID = mergeNode nID canonXID s
      | canonXID > canonYID = checkAndMergeNode s (XAG.And nID canonYID canonXID)
      | otherwise =
          case Map.lookup (canonXID, canonYID) (mergeAnd s) of
            Nothing ->
              (keepNode (XAG.And nID canonXID canonYID) s)
                { mergeAnd = Map.insert (canonXID, canonYID) nID (mergeAnd s)
                }
            Just mID -> mergeNode nID mID s
      where
        canonXID = IntMap.findWithDefault xID xID (mergeMapping s)
        canonYID = IntMap.findWithDefault yID yID (mergeMapping s)

    keepNode n s@(MergeState {mergeNodesRev = nodesRev}) =
      s {mergeNodesRev = n : nodesRev}
    mergeNode nID canonID s@(MergeState {mergeMapping = mm}) =
      s {mergeMapping = IntMap.insert nID canonID mm}

    emptyMerge =
      MergeState
        { mergeFalse = Nothing,
          mergeTrue = Nothing,
          mergeNot = IntMap.empty,
          mergeXor = Map.empty,
          mergeAnd = Map.empty,
          mergeMapping = IntMap.empty,
          mergeNodesRev = []
        }

-- Do the most trivial operations required to reduce the complexity of an XAG
-- normalize :: Graph -> Graph
-- normalize (Graph allNodes) =
--   case firstTrueConst allNodes of
--     Nothing -> Graph $ filterNodes IntSet.empty allNodes
--       where
--         -- If no constant true is present in the graph, there must also not be
--         -- any trivial true outputs. This arises because you can't get a true
--         -- output from an XOR or AND gate without a true input, therefore any
--         -- true outputs must be nontrivial. This is a convenient fact for us
--         -- in that the constant will always be there if we need it, but then
--         -- we still need to special-case the reduction when that happens.
--         filterNodes :: IntSet.IntSet -> [Node] -> [Node]
--         filterNodes _ [] = []
--         -- Add constant false to the trivial set
--         filterNodes trivialFalse (Const nid False : nodes) =
--           filterNodes (IntSet.insert nid trivialFalse) nodes
--         filterNodes _ (Const _ True : _) = undefined
--         -- Xor:
--         -- Remove trivial false inputs;
--         -- Remove inputs that appear an even number of times;
--         -- Remap trivial true inputs to the first constant true found.
--         filterNodes trivialFalse (Xor nid x y : nodes) =
--           Xor nid gatheredInputs : filterNodes trivialFalse nodes
--           where
--             gatheredInputs = IntSet.foldr xorGather IntSet.empty (IntSet.fromList [x, y])

--             xorGather inp gathered
--               -- Ignore trivial false inputs
--               | IntSet.member inp trivialFalse = gathered
--               -- Track whether inputs have canceled themselves out
--               | otherwise = invertMembership inp gathered

--             invertMembership n s
--               | IntSet.member n s = IntSet.delete n s
--               | otherwise = IntSet.insert n s

--         -- And:
--         -- If any input is trivial false, add this to the trivial false set;
--         -- Otherwise include it with repeated inputs removed.
--         filterNodes trivialFalse (And nid andInputs : nodes) =
--           if not (IntSet.disjoint trivialFalse andInputs)
--             then filterNodes (IntSet.insert nid trivialFalse) nodes
--             else And nid andInputs : filterNodes trivialFalse nodes
--     Just trueID -> Graph $ Const trueID True : filterNodes IntSet.empty IntSet.empty allNodes
--       where
--         filterNodes :: IntSet.IntSet -> IntSet.IntSet -> [Node] -> [Node]
--         filterNodes _ _ [] = []
--         -- Add constant true/false to the trivial set
--         filterNodes trivialFalse trivialTrue (Const nid False : nodes) =
--           filterNodes (IntSet.insert nid trivialFalse) trivialTrue nodes
--         filterNodes trivialFalse trivialTrue (Const nid True : nodes) =
--           filterNodes trivialFalse (IntSet.insert nid trivialTrue) nodes
--         -- Xor:
--         -- Remove trivial false inputs;
--         -- Remove inputs that appear an even number of times;
--         -- Remap trivial true inputs to the first constant true found.
--         filterNodes trivialFalse trivialTrue (Xor nid x y : nodes) =
--           Xor nid gatheredInputs : filterNodes trivialFalse trivialTrue nodes
--           where
--             gatheredInputs = IntSet.foldr xorGather IntSet.empty (IntSet.fromList [x, y])

--             xorGather inp gathered
--               -- Ignore trivial false inputs
--               | IntSet.member inp trivialFalse = gathered
--               -- Map trivial true to the one true ID (canceling it out if needed)
--               | IntSet.member inp trivialTrue = invertMembership trueID gathered
--               | otherwise = IntSet.insert inp gathered

--             invertMembership n s
--               | IntSet.member n s = IntSet.delete n s
--               | otherwise = IntSet.insert n s

--         -- And:
--         -- If any input is trivial false, add it to the trivial false set;
--         -- Remove any trivial true inputs;
--         --   If no inputs remain, add it to the trivial true set;
--         --   Otherwise include it with nontrivial inputs only.
--         filterNodes trivialFalse trivialTrue (And nid x y : nodes)
--           | not (IntSet.disjoint (IntSet.fromList [x, y]) trivialFalse) =
--               filterNodes (IntSet.insert nid trivialFalse) trivialTrue nodes
--           | IntSet.isSubsetOf (IntSet.fromList [x, y]) trivialTrue =
--               filterNodes (IntSet.insert nid trivialFalse) trivialTrue nodes
--           | otherwise =
--               And nid (IntSet.difference (IntSet.fromList [x, y]) trivialTrue)
--                 : filterNodes trivialFalse trivialTrue nodes
--   where
--     firstTrueConst [] = Nothing
--     firstTrueConst (Const nid True : _) = Just nid
--     firstTrueConst (_ : nodes) = firstTrueConst nodes
