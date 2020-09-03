{-|
Module      : Symbolic
Description : Symbolic verification based on path sums
Copyright   : (c) Matthew Amy, 2020
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Feynman.Verification.Symbolic where

import Data.Map (Map, (!))
import qualified Data.Map as Map
import Control.Monad.State.Lazy
import Data.Semigroup
import Data.Set (Set)
import qualified Data.Set as Set

import Feynman.Core
import Feynman.Algebra.Base
import Feynman.Algebra.Polynomial.Multilinear
import Feynman.Algebra.Pathsum.Balanced

{------------------------------------
 Path sum actions
 ------------------------------------}

-- | Context for computing path sums of circuits
type Context = Map ID Int

-- | Retrieve the path sum representation of a primitive gate
primitiveAction :: Primitive -> Pathsum DMod2
primitiveAction gate = case gate of
  H _           -> hgate
  X _           -> xgate
  Y _           -> ygate
  Z _           -> zgate
  CNOT _ _      -> cxgate
  S _           -> sgate
  Sinv _        -> rzgate $ dyadic 3 1
  T _           -> tgate
  Tinv _        -> rzgate $ dyadic 7 2
  Swap _ _      -> swapgate
  Rz theta _    -> rzgate $ discretize theta
  Rx theta _    -> hgate * rzgate (discretize theta) * hgate
  Ry theta _    -> rzgate (discretize theta) * hgate * rzgate (discretize theta) * hgate
  Uninterp _ _  -> error "Uninterpreted gates not supported"

-- | Find the relevant index or allocate one for the given qubit
findOrAlloc :: ID -> State Context Int
findOrAlloc x = do
  result <- gets $ Map.lookup x
  case result of
    Just i  -> return i
    Nothing -> gets Map.size >>= \i -> modify (Map.insert x i) >> return i

-- | Apply a circuit to a state
applyCircuit :: Pathsum DMod2 -> [Primitive] -> State Context (Pathsum DMod2)
applyCircuit = foldM absorbGate
  where absorbGate sop gate = do
          args <- mapM findOrAlloc $ getArgs gate
          nOut <- gets Map.size
          let sop' = sop <> identity (nOut - outDeg sop)
          let g    = extend (primitiveAction gate)
                            (nOut - length args)
                            ((Map.fromList $ zip [0..] args)!)
          return $ sop' .> g

-- | Create an initial state given a set of variables and inputs
makeInitial :: [ID] -> [ID] -> State Context ([SBool ID])
makeInitial vars inputs = fmap Map.elems $ foldM go Map.empty vars
  where go st x = do
          i <- findOrAlloc x
          if elem x inputs
            then return $ Map.insert i (ofVar x) st
            else return $ Map.insert i 0 st

-- | Compute the path sum action of a primitive circuit
computeAction :: [Primitive] -> State Context (Pathsum DMod2)
computeAction = applyCircuit (identity 0)

-- | Shortcut for computing an action in the empty context
simpleAction :: [Primitive] -> Pathsum DMod2
simpleAction = (flip evalState) Map.empty . computeAction

-- | Shortcut for computing an action given a set of variables and inputs
complexAction :: [ID] -> [ID] -> [Primitive] -> Pathsum DMod2
complexAction vars inputs circ = evalState st Map.empty where
  st = do
    init <- makeInitial vars inputs
    action <- computeAction circ
    return $ ket init .> action

{------------------------------------
 Verification methods
 ------------------------------------}

-- | The return type of verification queries
data Result =
    Identity
  | NotIdentity String
  | Inconclusive (Pathsum DMod2)
  deriving (Show)

-- | Check if a circuit is the identity
isIdentity :: [ID] -> [ID] -> [Primitive] -> Result
isIdentity vars inputs circuit =
  let sopWithContext = do
        st <- makeInitial vars inputs
        action <- computeAction circuit
        return $ ket st .> action .> bra st
      sop = grind $ evalState sopWithContext Map.empty
  in
    case sop of
      Triv       -> Identity
      HHKill _ p -> NotIdentity . show $ getSolution p
      _          -> Inconclusive sop


