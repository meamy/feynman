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
  Uninterp _ _  -> error "Uninterpreted gates currently not supported"

-- | Find the relevant index or allocate one for the given qubit
findOrAlloc :: ID -> State Context Int
findOrAlloc x = do
  result <- gets $ Map.lookup x
  case result of
    Just i  -> return i
    Nothing -> gets Map.size >>= \i -> modify (Map.insert x i) >> return i

-- | Compute the path sum action of a primitive circuit
computeAction :: [Primitive] -> State Context (Pathsum DMod2)
computeAction = foldM absorbGate (identity 0)
  where absorbGate sop gate = do
          args <- mapM findOrAlloc $ getArgs gate
          nOut <- gets Map.size
          let sop' = sop <> identity (nOut - inDeg sop)
          let g    = extend (primitiveAction gate)
                            (nOut - length args)
                            ((Map.fromList $ zip [0..] args)!)
          return $ sop' .> g

-- | Shortcut for computing an action in the empty context
simpleAction :: [Primitive] -> Pathsum DMod2
simpleAction = (flip evalState) Map.empty . computeAction

-- | Create an initial state given a set of variables and inputs
makeInitial :: [ID] -> [ID] -> State Context ([SBool ID])
makeInitial vars inputs = fmap Map.elems $ foldM go Map.empty vars
  where go st x = do
          i <- findOrAlloc x
          if elem x inputs
            then return $ Map.insert i (ofVar x) st
            else return $ Map.insert i 0 st

{------------------------------------
 Verification methods
 ------------------------------------}

-- | The return type of verification queries
data Result =
    Identity
  | NotIdentity (Var, SBool Var)
  | Inconclusive (Pathsum DMod2)
  deriving (Show)

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
      HHKill _ p -> NotIdentity $ getSolution p
      _          -> Inconclusive sop
