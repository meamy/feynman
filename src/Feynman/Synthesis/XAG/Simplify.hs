{-# LANGUAGE ImportQualifiedPost #-}

module Feynman.Synthesis.XAG.Simplify
  ( mergeStructuralDuplicates,
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

-- Within a graph, merge nodes to canonical nodes preforming the same
-- computation. This is fairly light and only merges by structure, graphs with
-- predictable structure may benefit most -- should be equivalent to ABC's
-- structural hashing, AKA "strash"
mergeStructuralDuplicates :: XAG.Graph -> XAG.Graph
mergeStructuralDuplicates inputGraph =
  XAG.Graph
    (reverse finalNodesRev)
    (XAG.inputIDs inputGraph)
    (map (\nID -> IntMap.findWithDefault nID nID finalMapping) (XAG.outputIDs inputGraph))
  where
    MergeState
      { mergeNodesRev = finalNodesRev,
        mergeMapping = finalMapping
      } =
        foldl checkAndMergeNode emptyMerge (XAG.xagNodes inputGraph)

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
      case (IntMap.lookup canonXID (mergeNot s)) of
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
          case (Map.lookup (canonXID, canonYID) (mergeXor s)) of
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
          case (Map.lookup (canonXID, canonYID) (mergeAnd s)) of
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
