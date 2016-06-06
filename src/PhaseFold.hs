module PhaseFold where

import Data.List hiding (transpose)

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Data.BitVector hiding (replicate, foldr)
import Syntax
import Linear

import Control.Monad.State.Strict

{-- Phase folding optimization -}
{- We have two options for implementation here:
 -
 -  1. Maintain a current state of each qubit
 -     over the standard basis. When a Hadamard
 -     gate is applied we then need to write all
 -     phases over the new standard basis.
 -     Cost: 1 XOR per CNOT,
 -           n^2 + n*num keys XORs per H
 -
 -  2. Express each phase as XORs over the current
 -     value of the qubits. Need some way to ensure
 -     the current values of all qubits forms a
 -     basis, otherwise might miss some collisions.
 -     Could map qubit IDs with unique values to unique
 -     indices. On application of a Hadamard we then
 -     only need to remove any phase with a 1 at the
 -     location the Hadamard was applied. Every CNOT
 -     triggers an update of all phases though
 -     Cost: num keys XORs/conditional bit flips per CNOT, 
 -           num keys bit tests per H -} 

data AnalysisState = SOP {
  dim     :: Int,
  qvals   :: Map ID F2Vec,
  terms   :: Map F2Vec (Set Loc, Int),
  orphans :: [(Set Loc, Int)]
} deriving Show

type Analysis = State AnalysisState

bitI :: Int -> Integer
bitI = bit

{- Get the bitvector for variable v, or otherwise allocate one -}
getSt :: ID -> Analysis F2Vec
getSt v = do 
  st <- get
  case Map.lookup v (qvals st) of
    Just bv -> return bv
    Nothing -> do put $ st { dim = dim', qvals = qvals' }
                  return bv'
      where dim' = dim st + 1
            bv' = F2Vec $ bitVec dim' $ bitI (dim' -1)
            qvals' = Map.insert v bv' (qvals st)

{- exists removes a variable (existentially quantifies it) then
 - orphans all terms that are no longer in the linear span of the
 - remaining variable states and assigns the quantified variable
 - a fresh (linearly independent) state -}
exists :: ID -> AnalysisState -> AnalysisState
exists v st@(SOP dim qvals terms orphans) =
  let (vars, vecs)  = unzip $ Map.toList $ Map.delete v qvals
      (terms', orp) = Map.partitionWithKey (\b _ -> inLinearSpan vecs b) terms
      (dim', vecs') = addIndependent vecs
      orphans'      = (snd $ unzip $ Map.toList orp) ++ orphans
      extendTerms   = Map.mapKeysMonotonic (F2Vec . (zeroExtend 1) . getBV)
  in
    if dim' > dim
    then SOP dim' (Map.fromList $ zip (vars ++ [v]) vecs') (extendTerms terms') orphans'
    else SOP dim' (Map.fromList $ zip (vars ++ [v]) vecs') terms' orphans'

updateQval :: ID -> F2Vec -> AnalysisState -> AnalysisState
updateQval v bv st = st { qvals = Map.insert v bv $ qvals st }

addTerm :: Loc -> F2Vec -> Int -> AnalysisState -> AnalysisState
addTerm l bv i st = st { terms = Map.alter f bv $ terms st }
  where f oldt = case oldt of
          Just (s, x) -> Just (Set.insert l s, x + i `mod` 8)
          Nothing     -> Just (Set.singleton l, i `mod` 8)
 
{-- The main analysis -}
applyGate :: (Primitive, Loc) -> Analysis ()
applyGate (H v, l) = do
  bv <- getSt v
  modify $ exists v

applyGate (CNOT c t, l) = do
  bvc <- getSt c
  bvt <- getSt t
  modify $ updateQval t (F2Vec $ (getBV bvc) `xor` (getBV bvt))

applyGate (T v, l) = do
  bv <- getSt v
  modify $ addTerm l bv 1

applyGate (Tinv v, l) = do
  bv <- getSt v
  modify $ addTerm l bv 7

runAnalysis :: [ID] -> [ID] -> [Primitive] -> AnalysisState
runAnalysis vars inputs gates =
  let init = 
        SOP { dim = dim', 
              qvals = Map.fromList ivals, 
              terms = Map.empty,
              orphans = [] }
  in
    execState (mapM_ applyGate $ zip gates [0..]) init
  where dim'    = length inputs
        bitvecs = [F2Vec $ bitVec dim' $ bitI x | x <- [0..]] 
        ivals   = zip (inputs ++ (vars \\ inputs)) bitvecs

minimalSequence :: ID -> Int -> [Primitive]
minimalSequence x i = case i `mod` 8 of
  0 -> []
  1 -> [T x]
  2 -> [S x]
  3 -> [S x, T x]
  4 -> [Z x]
  5 -> [Z x, T x]
  6 -> [Sinv x]
  7 -> [Tinv x]

phaseFold :: [ID] -> [ID] -> [Primitive] -> [Primitive]
phaseFold vars inputs gates =
  let (SOP _ _ terms orphans) = runAnalysis vars inputs gates
      choose = Set.findMin
      f gates (locs, exp) =
        let i = choose locs
            getTarget gate = case gate of
              T x -> x
              S x -> x
              Z x -> x
              Tinv x -> x
              Sinv x -> x
            g x@(gate, j) xs
              | j == i            = (zip (minimalSequence (getTarget gate) exp) (repeat i)) ++ xs
              | Set.member j locs = xs
              | otherwise         = x:xs
        in
          foldr g [] gates
  in
    fst $ unzip $ foldl' f (zip gates [0..]) ((snd $ unzip $ Map.toList terms) ++ orphans)
      

{- Tests -}
foo = [ T "x", CNOT "x" "y", H "x", T "x", T "y", CNOT "y" "x" ]
runFoo = runAnalysis ["x", "y"] ["x", "y"] foo
