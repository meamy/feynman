module TPar where

import Data.List hiding (transpose)

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Data.BitVector hiding (replicate, foldr, concat, reverse)
import Syntax
import Linear

import Control.Monad.State.Strict
import Control.Monad.Writer.Lazy

import Data.Graph.Inductive as Graph
import Data.Graph.Inductive.Query.DFS

import PhaseFold (foo)

{-- Generalized T-par -}
{-  The idea is to traverse the circuit, tracking the phases,
    and whenever a Hadamard (or more generally something that
    maps a computational basis state to either a non-computational
    basis state or a probabilistic mixture, i.e. measurement)
    is applied synthesize a circuit for the phases that are no
    longer in the state space. Synthesis can proceed by either
    T-depth optimal matroid partitioning or CNOT-optimal ways -}
       
{- TODO: Merge with phase folding eventually -}

data AnalysisState = SOP {
  dim     :: Int,
  ivals   :: Map ID F2Vec,
  qvals   :: Map ID F2Vec,
  terms   :: Map F2Vec Int
} deriving Show

type Analysis = State AnalysisState

type Synthesizer = Map ID F2Vec -> Map ID F2Vec -> [(F2Vec, Int)] -> [Primitive]

bitI :: Int -> Integer
bitI = bit

{- Get the bitvector for variable v, or otherwise allocate one -}
getSt :: ID -> Analysis F2Vec
getSt v = do 
  st <- get
  case Map.lookup v (qvals st) of
    Just bv -> return bv
    Nothing -> do put $ st { dim = dim', ivals = ivals', qvals = qvals' }
                  return bv'
      where dim' = dim st + 1
            bv' = F2Vec $ bitVec dim' $ bitI (dim' -1)
            ivals' = Map.insert v bv' (ivals st)
            qvals' = Map.insert v bv' (qvals st)

{- exists removes a variable (existentially quantifies it) then
 - orphans all terms that are no longer in the linear span of the
 - remaining variable states and assigns the quantified variable
 - a fresh (linearly independent) state -}
exists :: ID -> AnalysisState -> Analysis [(F2Vec, Int)]
exists v st@(SOP dim ivals qvals terms) =
  let (vars, vecs)  = unzip $ Map.toList $ Map.delete v qvals
      (terms', orp) = Map.partitionWithKey (\b _ -> inLinearSpan vecs b) terms
      (dim', vecs') = addIndependent vecs
      extendTerms   = Map.mapKeysMonotonic (F2Vec . (zeroExtend 1) . getBV)
      terms''       = if dim' > dim then extendTerms terms' else terms'
      vals          = Map.fromList $ zip (vars ++ [v]) vecs'
  in do
    put $ SOP dim' vals vals terms''
    return $ Map.toList orp

updateQval :: ID -> F2Vec -> AnalysisState -> AnalysisState
updateQval v bv st = st { qvals = Map.insert v bv $ qvals st }

addTerm :: F2Vec -> Int -> AnalysisState -> AnalysisState
addTerm bv i st = st { terms = Map.alter f bv $ terms st }
  where f oldt = case oldt of
          Just x  -> Just $ x + i `mod` 8
          Nothing -> Just $ i `mod` 8
 
{-- The main analysis -}
applyGate :: Synthesizer -> [Primitive] -> Primitive -> Analysis [Primitive]
applyGate synth gates g = case g of
  T v      -> do
    bv <- getSt v
    modify $ addTerm bv 1
    return gates
  Tinv v   -> do
    bv <- getSt v
    modify $ addTerm bv 7
    return gates
  S v      -> do
    bv <- getSt v
    modify $ addTerm bv 2
    return gates
  Sinv v   -> do
    bv <- getSt v
    modify $ addTerm bv 6
    return gates
  Z v      -> do
    bv <- getSt v
    modify $ addTerm bv 4
    return gates
  CNOT c t -> do
    bvc <- getSt c
    bvt <- getSt t
    modify $ updateQval t (F2Vec $ (getBV bvc) `xor` (getBV bvt))
    return gates
  H v      -> do
    bv <- getSt v
    st <- get
    orphans <- exists v st
    return $ gates ++ synth (ivals st) (qvals st) orphans ++ [H v]

finalize :: Synthesizer -> [Primitive] -> Analysis [Primitive]
finalize synth gates = do
  st <- get
  return $ gates ++ (synth (ivals st) (qvals st) $ Map.toList (terms st))
    
gtpar :: Synthesizer -> [ID] -> [ID] -> [Primitive] -> [Primitive]
gtpar synth vars inputs gates =
  let init = 
        SOP { dim = dim', 
              ivals = Map.fromList ivals, 
              qvals = Map.fromList ivals, 
              terms = Map.empty }
  in
    evalState (foldM (applyGate synth) [] gates >>= finalize synth) init
  where dim'    = length inputs
        bitvecs = [F2Vec $ bitVec dim' $ bitI x | x <- [0..]] 
        ivals   = zip (inputs ++ (vars \\ inputs)) bitvecs

{-- Synthesizers -}
emptySynth :: Synthesizer
emptySynth _ _ _ = []

linearSynth :: Synthesizer
linearSynth input output _ =
  let (ids, ivecs) = unzip $ Map.toList input
      (idt, ovecs) = unzip $ Map.toList output
      mat  = transformMat (fromList ivecs) (fromList ovecs)
      rops = snd $ runWriter $ toReducedEchelon mat
      f op = case op of
        Add i j  -> [CNOT (ids !! i) (ids !! j)]
        Swap i j ->
          let (v, u) = (ids !! i, ids !! j) in
            [CNOT v u, CNOT u v, CNOT v u]
  in
    if ids /= idt
    then error "Fatal: map keys not equal"
    else concatMap f rops

synthVec :: [(ID, F2Vec)] -> F2Vec -> Maybe ((ID, F2Vec), [Primitive])
synthVec ids vec =
  let lst = zip ids $ reverse $ toBits $ getBV vec
      f acc ((v, bv), insum) = case (insum, acc) of
        (False, _)                 -> acc
        (True, Nothing)            -> Just ((v, bv), [])
        (_, Just ((t, bt), gates)) -> Just ((t, F2Vec $ getBV bt `xor` getBV bv), (CNOT v t):gates)
  in
    foldl' f Nothing lst

cnotMin :: Synthesizer
cnotMin input output [] = linearSynth input output []
cnotMin input output ((x, i):xs) =
  let ivecs  = Map.toList input
      solver = minSolution $ transpose $ fromList $ snd $ unzip ivecs
  in
    case solver x >>= synthVec ivecs of
      Nothing            -> error "Fatal: something bad happened"
      Just ((v, bv), gates) -> gates ++ minimalSequence v i ++ cnotMin (Map.insert v bv input) output xs
  
cnotMinMore :: Synthesizer
cnotMinMore input output [] = linearSynth input output []
cnotMinMore input output (x:xs) =
  let ivecs  = Map.toList input
      solver = minSolution $ transpose $ fromList $ snd $ unzip ivecs
      takeMin (bv, x, acc) x' bv' =
        if wt bv <= wt bv'
        then Just (bv, x, x':acc)
        else Just (bv', x', x:acc)
      f (bv, x, acc) x' = solver (fst x') >>= takeMin (bv, x, acc) x'
      synthIt (bv, (_, i), acc) = synthVec ivecs bv >>= \(res, gates) -> Just (res, i, gates, acc)
  in
    case solver (fst x) >>= \bv -> foldM f (bv, x, []) xs >>= synthIt of
      Nothing                    -> error "Fatal: something bad happened"
      Just ((v, bv), i, gates, xs') -> gates ++ minimalSequence v i ++ cnotMin (Map.insert v bv input) output xs'

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
