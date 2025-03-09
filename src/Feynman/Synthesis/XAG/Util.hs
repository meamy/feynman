{-# LANGUAGE ImportQualifiedPost #-}

{-# HLINT ignore "Use second" #-}

module Feynman.Synthesis.XAG.Util (fromMCTs, fromSBools, toMCTs) where

import Control.Exception (assert)
import Control.Monad
import Control.Monad.State.Strict
import Data.Foldable (foldl')
import Data.Map.Strict (Map, (!))
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Debug.Trace (traceM)
import Feynman.Algebra.Base
import Feynman.Algebra.Pathsum.Balanced
import Feynman.Algebra.Polynomial.Multilinear
import Feynman.Control (traceIf)
import Feynman.Core
import Feynman.Synthesis.Pathsum.Util
import Feynman.Synthesis.XAG.Graph
import Feynman.Synthesis.XAG.Simplify (mergeStructuralDuplicates)

fromSBools :: Int -> [SBool Var] -> Graph
fromSBools nvars sbools =
  -- all vars in all terms in all SBools must be IVar
  assert (all (all (all isIVar . (vars . snd)) . toTermList) sbools) $
    mergeStructuralDuplicates finGraph
  where
    finGraph = Graph (reverse finNodesRev) [0 .. nvars - 1] finOutIDs

    (finOutIDs, GenState {gsNodes = finNodesRev}) =
      runState genAllSBools (GenState nvars [])

    genAllSBools = mapM genSBool sbools

isIVar :: Var -> Bool
isIVar (IVar _) = True
isIVar _ = False

fromMCTs :: [ExtractionGates] -> [ID] -> [ID] -> (Graph, [ID], [ID])
fromMCTs mcts _ _ =
  ( mergeStructuralDuplicates
      (Graph (reverse finNodesRev) inputNIDs (map (finIDMap !) allOutIDs)),
    allInIDs,
    allOutIDs
  )
  where
    (finIDMap, GenState {gsNodes = finNodesRev}) =
      runState genAllMCTs (GenState firstNonInputNID [])

    genAllMCTs = foldM genMCT inIDMap mcts

    inIDMap = Map.fromList (zip allInIDs inNIDs)
    (inNIDs, nonInNIDs) = splitAt (length allInIDs) [2 ..]

    firstNonInputNID = numInputs + 2
    inputNIDs = [2 .. numInputs + 2 - 1]
    numInputs = length allInIDs
    allInIDs = Set.toList (foldl' Set.union allOutIDsSet (map mctControlsSet mcts))
    allOutIDs = Set.toList allOutIDsSet
    allOutIDsSet = foldl' Set.union Set.empty (map mctTargetSet mcts)

    mctTargetSet (MCT _ target) = Set.singleton target
    mctTargetSet _ = Set.empty

    mctControlsSet (MCT controls _) = Set.fromList controls
    mctControlsSet _ = Set.empty

data GenState = GenState
  { gsNextID :: Int,
    gsNodes :: [Node]
  }

genMCT :: Map ID Int -> ExtractionGates -> State GenState (Map ID Int)
genMCT curIDMap (MCT [] target) = do
  notID <- addNode (`Not` (curIDMap ! target))
  return $ Map.insert target notID curIDMap
genMCT curIDMap (MCT controls target) = do
  controlID <- genTree And (map (curIDMap !) controls)
  xorID <- addNode (\newID -> Xor newID controlID (curIDMap ! target))
  return $ Map.insert target xorID curIDMap
genMCT _ _ = error "Encountered non-MCT gate in genMCT"

genSBool :: SBool Var -> State GenState Int
genSBool sbool = do
  let terms = toSynthesizableTerms id sbool
  termIDs <- mapM genTerm terms
  genTree Xor termIDs

toSynthesizableTerms :: (Int -> a) -> SBool Var -> [(FF2, [a])]
toSynthesizableTerms mapInput outPoly =
  -- Get all the monomial var sets as ID lists
  map (\(val, term) -> (val, termIDs term)) (toTermList outPoly)
  where
    -- Map each IVar in the monomial through the idList
    termIDs term = [mapInput i | IVar i <- Set.toList (vars term)]

genTerm :: (FF2, [Int]) -> State GenState Int
genTerm (1, varIDs) = genTree And varIDs
genTerm (0, varIDs) = do
  error "Unexpected?"
  xID <- genTree And varIDs
  addNode (`Not` xID)

genTree :: (Int -> Int -> Int -> Node) -> [Int] -> State GenState Int
genTree ctor [] = error "Can't generate tree of 0 things"
genTree ctor [xID] = return xID
genTree ctor xys = do
  let idx = length xys `div` 2
      (xs, ys) = splitAt idx xys
  xID <- genTree ctor xs
  yID <- genTree ctor ys
  addNode (\newID -> ctor newID xID yID)

addNode :: (Int -> Node) -> State GenState Int
addNode nodeF = do
  gs <- gets id
  let newNode = nodeF (gsNextID gs)
  put $ GenState (gsNextID gs + 1) (newNode : gsNodes gs)
  return $ nodeID newNode

data MCTState = MCTState
  { msNodeMap :: Map Int ID,
    msRemainIDs :: [ID],
    msMCTsRev :: [ExtractionGates]
  }

toMCTs :: Graph -> [ID] -> [ID] -> [ID] -> ([ExtractionGates], [ID])
toMCTs xag inIDs outIDs idSource =
  (reverse finMCTsRev, finIDSource)
  where
    (_, MCTState {msRemainIDs = finIDSource, msMCTsRev = finMCTsRev}) =
      runState (mapM_ addMCTOf (nodes xag)) initMCTState
    initMCTState = MCTState {msNodeMap = Map.empty, msRemainIDs = idSource, msMCTsRev = []}

-- I apologize for how extremely terse this is but I couldn't pass it up
addMCTOf :: Node -> State MCTState ID
addMCTOf (Const nID False) = addMCTs [] nID
addMCTOf (Const nID True) = addMCTs [[]] nID
addMCTOf (Not nID xID) = addMCTs [[xID]] nID
addMCTOf (Xor nID xID yID) = addMCTs [[xID], [yID]] nID
addMCTOf (And nID xID yID) = addMCTs [[xID, yID]] nID

addMCTs :: [[Int]] -> Int -> State MCTState ID
addMCTs ctlNIDs nID = do
  s <- get
  let (mctID : remainIDSource) = msRemainIDs s
      nodeMap = msNodeMap s
      ctlIDs = map (map (nodeMap !)) ctlNIDs
      mcts = map (`MCT` mctID) ctlIDs
  put
    ( s
        { msRemainIDs = remainIDSource,
          msNodeMap = Map.insert nID mctID nodeMap,
          msMCTsRev = mcts ++ msMCTsRev s
        }
    )
  return mctID
