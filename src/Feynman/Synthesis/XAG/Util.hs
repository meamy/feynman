{-# LANGUAGE ImportQualifiedPost #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use second" #-}

module Feynman.Synthesis.XAG.Util (fromSBools) where

import Control.Exception (assert)
import Control.Monad
import Control.Monad.State.Strict
import Data.Set (Set)
import Data.Set qualified as Set
import Feynman.Algebra.Base
import Feynman.Algebra.Pathsum.Balanced
import Feynman.Algebra.Polynomial.Multilinear
import Feynman.Synthesis.XAG.Graph

-- Merge graphs using the given input mappings. Output will return a merged
-- input mapping, with outputs list [the first graph outputs] ++ [the second
-- graph outputs]
merge :: (Ord a) => [a] -> Graph -> [a] -> Graph -> ([a], Graph)
merge mapA graphA mapB graphB = undefined
  where
    foo = undefined

data GenState = GenState
  { gsNextID :: Int,
    gsNodes :: [Node]
  }

fromSBools :: Int -> [SBool Var] -> Graph
fromSBools nvars sbools
  -- all vars in all terms in all SBools must be IVar
  | assert (all (all (all isIVar . (vars . snd)) . toTermList) sbools) $
      assert (valid completeGraph) otherwise =
      completeGraph
  where
    completeGraph = Graph (reverse completeNodesRev) [0 .. nvars - 1] completeOutIDs

    (completeOutIDs, GenState {gsNodes = completeNodesRev}) =
      runState fullGen (GenState nvars [])

    fullGen :: State GenState [Int]
    fullGen = mapM genSBool sbools

    genSBool :: SBool Var -> State GenState Int
    genSBool sbool = do
      let terms = toSynthesizableTerms id sbool
      termIDs <- mapM genTerm terms
      genTree Xor termIDs

    genTerm :: (FF2, [Int]) -> State GenState Int
    genTerm (1, varIDs) = genTree And varIDs
    genTerm (0, varIDs) = do
      error "Unexpected?"
      xID <- genTree And varIDs
      addNode (`Not` xID)

    genTree :: (Int -> Int -> Int -> Node) -> [Int] -> State GenState Int
    genTree ctor [] = error "Can't generate tree of 0 things"
    genTree ctor [xID] = return xID
    genTree ctor (xID : xs) = do
      yID <- genTree ctor xs
      addNode (\newID -> ctor newID xID yID)

    addNode :: (Int -> Node) -> State GenState Int
    addNode nodeF = do
      gs <- gets id
      let newNode = nodeF (gsNextID gs)
      put $ GenState (gsNextID gs + 1) (newNode : gsNodes gs)
      return $ nodeID newNode

isIVar (IVar _) = True
isIVar _ = False

toSynthesizableTerms :: (Int -> a) -> SBool Var -> [(FF2, [a])]
toSynthesizableTerms mapInput outPoly =
  -- Get all the monomial var sets as ID lists
  map (\(val, term) -> (val, termIDs term)) (toTermList outPoly)
  where
    -- Map each IVar in the monomial through the idList
    termIDs term = [mapInput i | IVar i <- Set.toList (vars term)]
