{-# LANGUAGE ImportQualifiedPost #-}

module Feynman.Synthesis.XAG.Optimize
  ( canReduce,
    findAndIDs,
    findReducible,
    findReducibleNodes,
    reduceAndToNotXor,
  )
where

import Data.IntMap.Strict qualified as IntMap
import Data.IntSet qualified as IntSet
import Data.List (sort)
import Data.Maybe (isNothing, mapMaybe)
import Feynman.Synthesis.XAG.Graph qualified as XAG
import SAT.MiniSat

canReduce :: Int -> [XAG.Node] -> Bool
canReduce reduceID allNodes =
  case findInputs allNodes of
    Nothing -> False
    Just (xID, yID) -> isNothing (solve clause)
      where
        clause = coverClause :&&: sdcClause :&&: odcClause
        -- SDC is UNSAT if we can't even produce the input in the first place
        sdcClause = (Var xID :<->: No) :&&: (Var yID :<->: No)
        -- ODC is UNSAT if the input can't possibly affect the dominators
        -- (this is a little tricky: the input of the And which we _didn't_
        -- reach has to be true, otherwise the output will be false no matter
        -- what input we're driving it with)
        -- If the dominators are empty, Some will be inherently false making
        -- the whole formula UNSAT, so in that case we need to produce Yes
        -- which will cause the formulat to fall back on just the SDC
        odcClause =
          if null dominators
            then Yes
            else Some (map (\(_, (_, nID)) -> Var nID) dominators)
  where
    findInputs :: [XAG.Node] -> Maybe (Int, Int)
    findInputs [] = Nothing
    findInputs (XAG.And nID xID yID : nodes)
      | nID == reduceID = Just (xID, yID)
      | nID > reduceID = Nothing
      | otherwise = findInputs nodes
    findInputs (node : nodes)
      | XAG.nodeID node >= reduceID = Nothing
      | otherwise = findInputs nodes

    coverClause = makeTseytin optCoverNodes

    optCoverNodes = optimizeCover 1000 coverNodes
    criticalIDs = downstreamOf (IntSet.singleton reduceID) coverNodes
    -- cover of dominatorSet should implicitly include reduceID
    coverNodes = XAG.cover dominatorIDs allNodes
    dominatorIDs = IntSet.fromList $ map fst dominators
    dominators = XAG.dominatingAnds reduceID allNodes

    downstreamOf :: IntSet.IntSet -> [XAG.Node] -> IntSet.IntSet
    downstreamOf searchSet [] = searchSet
    downstreamOf searchSet (node : nodes)
      | IntSet.member (XAG.nodeID node) searchSet =
          downstreamOf (insertDeps intSetF node searchSet) nodes
      | otherwise = downstreamOf searchSet nodes

    optimizeCover :: Int -> [XAG.Node] -> [XAG.Node]
    optimizeCover maxCount optNodes
      | length optNodes <= maxCount = optNodes
      | IntSet.size criticalIDs >= maxCount =
          filter (\n -> IntSet.member (XAG.nodeID n) criticalIDs) optNodes
      -- do a second cover here just in case we orphaned some nodes along the way
      | otherwise = XAG.cover criticalIDs mostImportantNodes
      where
        mostImportantNodes = filter (\n -> IntSet.member (XAG.nodeID n) toKeepIDs) optNodes
        toKeepIDs = IntSet.union criticalIDs (IntSet.fromList (take maxCount (map snd byImportance)))
        byImportance = sort (mapMaybe lookupImportance optNodes)
          where
            lookupImportance node =
              let nID = XAG.nodeID node
               in fmap (\x -> (x, nID)) (IntMap.lookup nID importance)
        importance :: IntMap.IntMap Double
        importance =
          distImportance
            -- Intialize the importance list with the roots at very high priority
            (IntMap.fromList (map (\nID -> (nID, 10.0)) (IntSet.toList criticalIDs)))
            optNodes

        distImportance :: IntMap.IntMap Double -> [XAG.Node] -> IntMap.IntMap Double
        distImportance impSoFar [] = impSoFar
        distImportance impSoFar (node : revNodes)
          | IntMap.member (XAG.nodeID node) impSoFar =
              let f = distF (impSoFar IntMap.! XAG.nodeID node)
               in distImportance (insertDeps f node impSoFar) revNodes
          | otherwise = distImportance impSoFar revNodes
          where
            distF :: Double -> Int -> Int -> IntMap.IntMap Double -> IntMap.IntMap Double
            distF impAmt xID (-1) theMap = IntMap.insertWith (+) xID impAmt theMap
            distF impAmt xID yID theMap =
              let mapWithX = IntMap.insertWith (+) xID impAmt theMap
               in IntMap.insertWith (+) yID impAmt mapWithX

    intSetF :: Int -> Int -> IntSet.IntSet -> IntSet.IntSet
    intSetF xID (-1) theSet = IntSet.insert xID theSet
    intSetF xID yID theSet = IntSet.insert yID (IntSet.insert xID theSet)

    insertDeps :: (Int -> Int -> a -> a) -> XAG.Node -> a -> a
    insertDeps _ (XAG.Const _ _) idSet = idSet
    insertDeps insertF (XAG.Not _ xID) idSet = insertF xID (-1) idSet
    insertDeps insertF (XAG.Xor _ xID yID) idSet = insertF xID yID idSet
    insertDeps insertF (XAG.And _ xID yID) idSet = insertF xID yID idSet

makeTseytin :: [XAG.Node] -> Formula Int
makeTseytin allNodes = All (map toClause allNodes)
  where
    toClause (XAG.Const nID True) = Var nID :<->: Yes
    toClause (XAG.Const nID False) = Var nID :<->: No
    toClause (XAG.Not nID xID) = Var nID :<->: Not (Var xID)
    toClause (XAG.Xor nID xID yID) = Var nID :<->: (Var xID :++: Var yID)
    toClause (XAG.And nID xID yID) = Var nID :<->: (Var xID :&&: Var yID)

findAndIDs :: [XAG.Node] -> [Int]
findAndIDs [] = []
findAndIDs ((XAG.And {XAG.nodeID = nID}) : found) = nID : findAndIDs found
findAndIDs (_ : found) = findAndIDs found

findReducibleNodes :: [XAG.Node] -> [Int]
findReducibleNodes allNodes =
  allReducibleOf (findAndIDs allNodes)
  where
    allReducibleOf [] = []
    allReducibleOf (tryID : idsRemaining) =
      if canReduce tryID allNodes
        then tryID : allReducibleOf idsRemaining
        else allReducibleOf idsRemaining

renumberNodes :: Int -> Int -> Int -> [XAG.Node] -> [XAG.Node]
renumberNodes atID shiftByEq shiftByGt = renumberNodesAux
  where
    renumberNodesAux [] = []
    renumberNodesAux (node : nodes) = renumberOne node : renumberNodesAux nodes

    renumberOne (XAG.Const nID value) = XAG.Const (mapID nID) value
    renumberOne (XAG.Not nID xID) = XAG.Not (mapID nID) (mapID xID)
    renumberOne (XAG.Xor nID xID yID) = XAG.Xor (mapID nID) (mapID xID) (mapID yID)
    renumberOne (XAG.And nID xID yID) = XAG.And (mapID nID) (mapID xID) (mapID yID)

    mapID = renumberID atID shiftByEq shiftByGt

renumberIDs :: Int -> Int -> Int -> [Int] -> [Int]
renumberIDs atID shiftByEq shiftByGt = map (renumberID atID shiftByEq shiftByGt)

renumberID :: Int -> Int -> Int -> Int -> Int
renumberID atID shiftByEq shiftByGt nID
  | nID < atID = nID
  | nID == atID = nID + shiftByEq
  | otherwise = nID + shiftByGt

splitNodes :: Int -> [XAG.Node] -> ([XAG.Node], [XAG.Node])
splitNodes atID allNodes = (take atIndex allNodes, rightNodes)
  where
    (atIndex, rightNodes) = findSplit 0 allNodes
    findSplit index [] = (index, [])
    findSplit index (node : nodes)
      | XAG.nodeID node < atID = findSplit (index + 1) nodes
      | otherwise = (index, node : nodes)

-- spliceNodes :: Int -> Int -> [XAG.Node] -> Int -> Int -> [XAG.Node] -> [XAG.Node]
-- spliceNodes fromID toID insNodes shiftByEq shiftByGt allNodes =
--   leftNodes ++ insNodes ++ renumberNodes toID shiftByEq shiftByGt rightNodes
--   where
--     (_, rightNodes) = splitNodes toID notLeftNodes
--     (leftNodes, notLeftNodes) = splitNodes fromID allNodes

findReducible :: XAG.Graph -> [Int]
findReducible (XAG.Graph allNodes _ _) = findReducibleNodes allNodes

reduceAndToNotXor :: Int -> XAG.Graph -> Maybe XAG.Graph
reduceAndToNotXor andID (XAG.Graph allNodes inIDs outIDs) =
  case splitNodes andID allNodes of
    (leftNodes, XAG.And _ xID yID : rightNodes) -> Just (updateGraph leftNodes xID yID rightNodes)
    (_, _) -> Nothing
  where
    updateGraph leftNodes xID yID rightNodes =
      XAG.Graph updatedNodes inIDs (renumberIDs andID 1 1 outIDs)
      where
        updatedNodes =
          leftNodes
            ++ [XAG.Xor andID xID yID, XAG.Not (andID + 1) andID]
            ++ renumberNodes andID 1 1 rightNodes
