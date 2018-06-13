module Synthesis.Reversible where

import Data.List hiding (transpose)
import Data.Tuple (swap)
import Data.Maybe (fromJust)

import Data.Map.Strict (Map, (!))
import qualified Data.Map.Strict as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Control.Monad.State.Strict
import Control.Monad.Writer.Lazy

import Algebra.Base
import Algebra.Linear
import Synthesis.Phase
import Core

type AffineSynthesizer     = Map ID (F2Vec, Bool) -> Map ID (F2Vec, Bool) -> [(F2Vec, Angle)] -> [Primitive]
type Synthesizer           = Map ID F2Vec -> Map ID F2Vec -> [(F2Vec, Angle)] -> [Primitive]
type AffineOpenSynthesizer = Map ID (F2Vec, Bool) -> [(F2Vec, Angle)] -> (Map ID (F2Vec, Bool), [Primitive])
type OpenSynthesizer       = Map ID F2Vec -> [(F2Vec, Angle)] -> (Map ID F2Vec, [Primitive])


{-- Synthesizers -}
affineTrans :: Synthesizer -> AffineSynthesizer
affineTrans synth = \input output xs ->
  let f    = Map.foldrWithKey (\id (_, b) xs -> if b then (X id):xs else xs) []
      inX  = f input
      outX = f output
  in
    inX ++ (synth (Map.map fst input) (Map.map fst output) xs) ++ outX

affineTransOpen :: OpenSynthesizer -> AffineOpenSynthesizer
affineTransOpen synth = \input xs ->
  let f    = Map.foldrWithKey (\id (_, b) xs -> if b then (X id):xs else xs) []
      inX  = f input
      (out, circ) = synth (Map.map fst input) xs
  in
    (Map.map (\bv -> (bv, False)) out, inX ++ circ)

emptySynth :: Synthesizer
emptySynth _ _ _ = []

linearSynth :: Synthesizer
linearSynth input output _ =
  let (ids, ivecs) = unzip $ Map.toList input
      (idt, ovecs) = unzip $ Map.toList output
      mat  = transformMat (fromList ivecs) (fromList ovecs)
      rops = snd $ runWriter $ toReducedEchelonPMHA mat
      rops' = snd $ runWriter $ toReducedEchelonA mat
      isadd g = case g of
        Add _ _   -> True
        otherwise -> False
      counta = length . filter isadd
      f op = case op of
        Add i j      -> [CNOT (ids !! i) (ids !! j)]
        Exchange i j -> [Swap (ids !! i) (ids !! j)]
  in
    if ids /= idt
      then error "Fatal: map keys not equal"
      else reverse $ concatMap f (if counta rops > counta rops' then rops' else rops)

synthVec :: [(ID, F2Vec)] -> F2Vec -> Maybe ((ID, F2Vec), [Primitive])
synthVec ids vec =
  let lst = zip ids $ reverse $ toBits $ vec
      f acc ((v, bv), insum) = case (insum, acc) of
        (False, _)                 -> acc
        (True, Nothing)            -> Just ((v, bv), [])
        (_, Just ((t, bt), gates)) -> Just ((t, bt + bv), (CNOT v t):gates)
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
      Just ((v, bv), gates) -> gates ++ synthesizePhase v i ++ cnotMin (Map.insert v bv input) output xs
  
cnotMinMore :: Synthesizer
cnotMinMore input output [] = linearSynth input output []
cnotMinMore input output (x:xs) =
  let ivecs  = Map.toList input
      solver = minSolution $ transpose $ fromList $ snd $ unzip ivecs
      takeMin (bv, x, acc) x' bv'
        | wt bv <= wt bv' = Just (bv, x, x':acc)
        | otherwise       = Just (bv', x', x:acc)
      f (bv, x, acc) x' = solver (fst x') >>= takeMin (bv, x, acc) x'
      synthIt (bv, (_, i), acc) = synthVec ivecs bv >>= \(res, gates) -> Just (res, i, gates, acc)
  in
    case solver (fst x) >>= \bv -> foldM f (bv, x, []) xs >>= synthIt of
      Nothing                       -> error "Fatal: something bad happened"
      Just ((v, bv), i, g, xs') -> g ++ synthesizePhase v i ++ cnotMinMore (Map.insert v bv input) output xs'

cnotMinMost :: Synthesizer
cnotMinMost input output xs = cnotMinMore input output xs'
  where xs' = filter (\(_, i) -> order i /= 1) xs

-- Given x, U and V, apply a linear transformation L to U such that
--   1) LU(x) = V(x), and
--   2) span(LU - x) = span(V - x)

synthV :: ID -> F2Vec -> Map ID F2Vec -> (Map ID F2Vec, [Primitive])
synthV v x input = case oneSolution (transpose . fromList . Map.elems $ input) x of
  Nothing -> error "Fatal: vector not in linear span"
  Just y  ->
    let u      = case find (y@.) [0..width y-1] of
          Nothing -> v
          Just i  -> (Map.keys input)!!i
        input' = Map.insert u x input
        gates  = linearSynth input input' []
    in
      if v == u
        then (input', gates)
        else (Map.insert v x (Map.insert u (input!v) input), gates ++ [Swap u v])
    

addToSpan :: ID -> Map ID F2Vec -> (Map ID F2Vec, [Primitive])
addToSpan v input
  | inLinearSpan (Map.elems . Map.delete v $ input) (input!v) = (input, [])
  | otherwise =
    let (ids, vecs) = unzip $ Map.toList input in
      case findDependent vecs of
        Nothing -> error "Fatal: Adding to span of independent set"
        Just i  -> (Map.insert (ids!!i) (vecs!!i + input!v) input, [CNOT v (ids!!i)])

subsetize :: ID -> Map ID F2Vec -> (F2Vec -> Bool) -> (Map ID F2Vec, [Primitive])
subsetize v input solver =
  let x = input!v 
      f accum u vec
        | u == v || solver vec = (accum, vec)
        | otherwise            = (accum ++ [CNOT v u], vec + x)
  in
    swap $ Map.mapAccumWithKey f [] input

unify :: ID -> Map ID F2Vec -> Map ID F2Vec -> (Map ID F2Vec, [Primitive])
unify v input output =
  let (input', gates) = synthV v (output!v) input
      vSolve = inLinearSpan (Map.elems . Map.delete v $ output)
      (output', gates')
        | vSolve $ output!v = addToSpan v input'
        | otherwise         = subsetize v input' vSolve
  in
    if sameSpace (Map.elems . Map.delete v $ output') (Map.elems . Map.delete v $ output)
      then (output', gates ++ gates')
      else (output, gates ++ (linearSynth input' output []))

unifyAffine v input output =
  let f    = Map.foldrWithKey (\id (_, b) xs -> if b then (X id):xs else xs) []
      inX  = f input
      (out, gates) = unify v (Map.map fst input) (Map.map fst output)
  in
    (Map.map (\bv -> (bv, False)) out, inX ++ gates)
  
