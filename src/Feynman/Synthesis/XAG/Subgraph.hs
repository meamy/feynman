{-# LANGUAGE ImportQualifiedPost #-}

module Feynman.Synthesis.XAG.Subgraph
  ( Subgraph (..),
    coverSubgraph,
    emptySubgraph,
    evalSubgraph,
    evalSubgraphPackedInOut,
    mergeStructuralDuplicatesSub,
    mergeSubgraphs,
    subgraphFromGraph,
    subgraphToGraph,
    validSubgraph,
  )
where

import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet
import Data.List (sort, sortOn)
import Data.Maybe (isNothing)
import Feynman.Synthesis.XAG.Graph qualified as XAG
import Feynman.Synthesis.XAG.Simplify qualified as XAG

data Subgraph = Subgraph
  { subNodes :: [XAG.Node],
    subInputIDs :: IntMap Int, -- index in the original input list -> input ID
    subOutputIDs :: IntMap Int -- index in the original output list -> subnode ID
  }
  deriving (Eq, Show)

emptySubgraph :: Subgraph
emptySubgraph = Subgraph [] IntMap.empty IntMap.empty

subgraphFromGraph :: XAG.Graph -> Subgraph
subgraphFromGraph g =
  Subgraph (XAG.nodes g) insMap outsMap
  where
    insMap = IntMap.fromList (zip [0 ..] (XAG.inputIDs g))
    outsMap = IntMap.fromList (zip [0 ..] (XAG.outputIDs g))

subgraphToGraph :: Subgraph -> XAG.Graph
subgraphToGraph subG
  | not (all (uncurry (==)) (zip (IntMap.keys (subInputIDs subG)) [0 ..])) =
      error "Inputs not contiguous"
  | not (all (uncurry (==)) (zip (IntMap.keys (subOutputIDs subG)) [0 ..])) =
      error "Outputs not contiguous"
  | otherwise = XAG.Graph (subNodes subG) inIDs outIDs
  where
    outIDs = map snd (IntMap.toAscList (subOutputIDs subG))
    inIDs = map snd (IntMap.toAscList (subInputIDs subG))

coverSubgraph :: Subgraph -> [Int] -> Subgraph
coverSubgraph subG outIdxs =
  Subgraph coverNodes coverInIDs coverOutIDs
  where
    coverInIDs =
      IntMap.fromList
        (filter ((`IntSet.member` inIDsUsed) . snd) (IntMap.toList (subInputIDs subG)))
    inIDsUsed = XAG.freeVariables coverNodes coverOutIDSet
    coverOutIDSet = IntSet.fromList (IntMap.elems coverOutIDs)
    coverOutIDs = IntMap.fromList [(idx, subOutputIDs subG IntMap.! idx) | idx <- outIdxs]

    coverNodes =
      XAG.cover
        (IntSet.fromList (map (subOutputIDs subG IntMap.!) outIdxs))
        (subNodes subG)

validSubgraph :: Subgraph -> Bool
validSubgraph (Subgraph subNs inIDs outIDs) =
  XAG.validNodes subNs
    -- inputIDs completely specifies the free variables (but inputs may be disconnected)
    && IntSet.isSubsetOf freeVarSet inIDSet
    -- inputIDs should be a bijection, i.e., no dups in elems
    && (IntSet.size inIDSet == length (IntMap.elems inIDs))
    -- outputIDs may have dups
    -- outputIDs may only refer to inputIDs and actual outputs
    && IntSet.isSubsetOf outIDSet (IntSet.union outSet inIDSet)
  where
    freeVarSet = XAG.freeVariables subNs outIDSet
    outSet = XAG.outputs subNs
    inIDSet = IntSet.fromList (IntMap.elems inIDs)
    outIDSet = IntSet.fromList (IntMap.elems outIDs)

evalSubgraph :: Subgraph -> IntMap Bool -> IntMap Bool
evalSubgraph subG inVals =
  IntMap.fromList (zip packedOutIdxs packedOutVals)
  where
    packedOutVals = evalSubgraphPackedInOut subG packedInVals
    packedInVals = map (inVals IntMap.!) packedInIdxs
    (packedOutIdxs, _) = unzip (IntMap.toAscList (subOutputIDs subG))
    (packedInIdxs, _) = unzip (IntMap.toAscList (subInputIDs subG))

evalSubgraphPackedInOut :: Subgraph -> [Bool] -> [Bool]
evalSubgraphPackedInOut subG packedInVals =
  XAG.eval (XAG.Graph gNodes gInIDs gOutIDs) packedInVals
  where
    (_, gOutIDs) = unzip (IntMap.toAscList (subOutputIDs subG))
    (_, gInIDs) = unzip (IntMap.toAscList (subInputIDs subG))
    gNodes = subNodes subG

-- The subgraphs must be compatible, which is a property that should be
-- maintained if they are cover slices from the same original graph. In general
-- node IDs will all be rewritten, and so inputs and outputs will be matched up
-- by their respective indexes; the one detail is that the outputs must not
-- conflict, i.e., you may not merge two subgraphs that produce map the same
-- output index

mergeSubgraphs :: Subgraph -> Subgraph -> Subgraph
mergeSubgraphs leftG rightG
  | not (validSubgraph leftG) = error "Left subgraph not valid"
  | not (validSubgraph rightG) = error "Right subgraph not valid"
  | outputCollision = error "Outputs overlap"
  | otherwise = strashMerged
  where
    strashMerged = mergeStructuralDuplicatesSub (Subgraph newNodes newInputIDs newOutputIDs)

    newNodes =
      XAG.cover
        ((IntSet.fromList . IntMap.elems) newOutputIDs)
        (leftRenumberedNodes ++ rightRenumberedNodes)
    newOutputIDs =
      IntMap.union
        (remapOutputIDs leftG leftNodesMap)
        (remapOutputIDs rightG rightNodesMap)

    remapOutputIDs :: Subgraph -> IntMap Int -> IntMap Int
    remapOutputIDs subG nodesMap =
      IntMap.fromAscList
        [ (outIdx, nodesMap IntMap.! outID)
          | (outIdx, outID) <- IntMap.toAscList (subOutputIDs subG)
        ]

    (rightRenumberedNodes, _, rightNodesMap) =
      renumberNodes rightInputsMap leftNextID (subNodes rightG)
    (leftRenumberedNodes, leftNextID, leftNodesMap) =
      renumberNodes leftInputsMap firstNodeID (subNodes leftG)

    rightInputsMap =
      IntMap.fromList
        [(inID, newInputIDs IntMap.! idx) | (idx, inID) <- IntMap.toList (subInputIDs rightG)]
    leftInputsMap =
      IntMap.fromList
        [(inID, newInputIDs IntMap.! idx) | (idx, inID) <- IntMap.toList (subInputIDs leftG)]
    firstNodeID = maybe 2 ((+ 1) . fst) (IntMap.lookupMax newInputIDIdxs)
    newInputIDIdxs = IntMap.fromList (zip [2 ..] allInputIdxs)
    newInputIDs = IntMap.fromList (zip allInputIdxs [2 ..])
    allInputIdxs =
      IntSet.toList
        ( IntSet.union
            ((IntMap.keysSet . subInputIDs) leftG)
            ((IntMap.keysSet . subInputIDs) rightG)
        )

    renumberNodes :: IntMap Int -> Int -> [XAG.Node] -> ([XAG.Node], Int, IntMap Int)
    renumberNodes idMap nextID [] = ([], nextID, idMap)
    renumberNodes idMap nextID (node : remain) =
      (renumberNode idMap nextID node : renumberedRemain, finalNextID, finalMap)
      where
        (renumberedRemain, finalNextID, finalMap) =
          renumberNodes (IntMap.insert (XAG.nodeID node) nextID idMap) (nextID + 1) remain

    renumberNode idMap nextID node@(XAG.Const nID val) = XAG.Const nextID val
    renumberNode idMap nextID node@(XAG.Not nID xID) = XAG.Not nextID (idMap IntMap.! xID)
    renumberNode idMap nextID node@(XAG.Xor nID xID yID) =
      XAG.Xor nextID (idMap IntMap.! xID) (idMap IntMap.! yID)
    renumberNode idMap nextID node@(XAG.And nID xID yID) =
      XAG.And nextID (idMap IntMap.! xID) (idMap IntMap.! yID)

    outputCollision =
      isNothing
        ( scanCollision (IntMap.keys (subOutputIDs leftG)) IntSet.empty
            >>= scanCollision (IntMap.keys (subOutputIDs rightG))
        )

scanCollision :: [Int] -> IntSet -> Maybe IntSet
scanCollision [] seen = Just seen
scanCollision (outIdx : remain) seen
  | IntSet.member outIdx seen = Nothing
  | otherwise = scanCollision remain (IntSet.insert outIdx seen)

mergeStructuralDuplicatesSub :: Subgraph -> Subgraph
mergeStructuralDuplicatesSub subG =
  Subgraph strashNodes strashInputIDs strashOutputIDs
  where
    strashOutputIDs =
      IntMap.fromList
        [(idx, strashMap outID) | (idx, outID) <- IntMap.toList (subOutputIDs subG)]
    strashInputIDs =
      IntMap.fromList
        [ (idx, strashMap inID)
          | (idx, inID) <- IntMap.toList (subInputIDs subG),
            IntSet.member inID strashUsedInputs
        ]
    strashUsedInputs =
      XAG.freeVariables
        strashNodes
        ((IntSet.fromList . IntMap.elems) (subOutputIDs subG))
    strashMap nID = IntMap.findWithDefault nID nID strashMapping
    (strashNodes, strashMapping) = XAG.mergeStructuralDuplicateNodes (subNodes subG)
