module Feynman.Synthesis.Reversible where

import Feynman.Algebra.Base
import Feynman.Algebra.Linear
import Feynman.Synthesis.Phase
import Feynman.Core

import Data.List hiding (transpose)
import Data.Tuple (swap)
import Data.Maybe (fromJust)

import Data.Map.Strict (Map, (!))
import qualified Data.Map.Strict as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Control.Monad.State.Strict
import Control.Monad.Writer.Lazy

{- Type synonyms for convenience -}
type LinearTrans = Map ID F2Vec
type AffineTrans = Map ID (F2Vec, Bool)
type Phase       = (F2Vec, Angle)

type AffineSynthesizer     = AffineTrans -> AffineTrans -> [Phase] -> [Phase] -> ([Primitive], [Phase])
type Synthesizer           = LinearTrans -> LinearTrans -> [Phase] -> [Phase] -> ([Primitive], [Phase])
type AffineOpenSynthesizer = AffineTrans -> [Phase] -> (AffineTrans, [Primitive])
type OpenSynthesizer       = LinearTrans -> [Phase] -> (LinearTrans, [Primitive])


{- Basic synthesizers & transformers -}
affineTrans :: Synthesizer -> AffineSynthesizer
affineTrans synth = \input output must may ->
  let f            = Map.foldrWithKey (\id (_, b) xs -> if b then (X id):xs else xs) []
      inX          = f input
      outX         = f output
      (circ, may') = synth (Map.map fst input) (Map.map fst output) must may
  in
    (inX ++ circ ++ outX, may')

affineTransOpen :: OpenSynthesizer -> AffineOpenSynthesizer
affineTransOpen synth = \input xs ->
  let f    = Map.foldrWithKey (\id (_, b) xs -> if b then (X id):xs else xs) []
      inX  = f input
      (out, circ) = synth (Map.map fst input) xs
  in
    (Map.map (\bv -> (bv, False)) out, inX ++ circ)

emptySynth :: Synthesizer
emptySynth _ _ _ _ = ([], [])

-- Assumes span(input) = span(output)
linearSynth :: LinearTrans -> LinearTrans -> [Primitive]
linearSynth input output =
  let (ids, ivecs) = unzip $ Map.toList input
      (idt, ovecs) = unzip $ Map.toList output
      mat  = transformMatStrict (fromList ivecs) (fromList ovecs)
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

affineSynth :: AffineTrans -> AffineTrans -> [Primitive]
affineSynth input output =
  let f    = Map.foldrWithKey (\id (_, b) xs -> if b then (X id):xs else xs) []
      inX  = f input
      outX = f output
      circ = linearSynth (Map.map fst input) (Map.map fst output)
  in
    inX ++ circ ++ outX

-- Applies linear simplifications
simplifyLinear :: LinearTrans -> [Primitive]
simplifyLinear output =
  let (ids, ovecs) = unzip $ Map.toList output
      mat  = fromListSafe ovecs
      {- Significant area for improvement here. We can't use any of bi-directional (i.e. column ops)
         methods since we don't have a transformation matrix. -}
      rops = snd $ runWriter $ toReducedEchelon mat
      f op = case op of
        Add i j      -> [CNOT (ids !! i) (ids !! j)]
        Exchange i j -> [Swap (ids !! i) (ids !! j)]
  in
      reverse $ concatMap f rops

-- Affine simplifications
simplifyAffine :: AffineTrans -> [Primitive]
simplifyAffine output =
  let f    = Map.foldrWithKey (\id (_, b) xs -> if b then (X id):xs else xs) []
      outX = f output
      circ = simplifyLinear (Map.map fst output)
  in
    circ ++ outX

liftMatOp :: (F2Mat -> F2Mat) -> LinearTrans -> LinearTrans
liftMatOp f = Map.fromList . uncurry zip . go . unzip . Map.toList where
  go (ids,vecs) = (ids, toList . f . fromList $ vecs)

{- Deprecated CNOT minimizing CNOT-dihedral synthesis -}
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
cnotMin input output [] may = (linearSynth input output, may)
cnotMin input output ((x, i):xs) may =
  let ivecs  = Map.toList input
      solver = minSolution $ transpose $ fromList $ snd $ unzip ivecs
  in
    case solver x >>= synthVec ivecs of
      Nothing               -> error "Fatal: something bad happened"
      Just ((v, bv), gates) ->
        let (circ, may') = cnotMin (Map.insert v bv input) output xs may in
          (gates ++ synthesizePhase v i ++ circ, may')
  
cnotMinMore :: Synthesizer
cnotMinMore input output [] may     = (linearSynth input output, may)
cnotMinMore input output (x:xs) may =
  let ivecs  = Map.toList input
      solver = minSolution $ transpose $ fromList $ snd $ unzip ivecs
      takeMin (bv, x, acc) x' bv'
        | wt bv <= wt bv' = Just (bv, x, x':acc)
        | otherwise       = Just (bv', x', x:acc)
      f (bv, x, acc) x' = solver (fst x') >>= takeMin (bv, x, acc) x'
      synthIt (bv, (_, i), acc) = synthVec ivecs bv >>= \(res, gates) -> Just (res, i, gates, acc)
  in
    case solver (fst x) >>= \bv -> foldM f (bv, x, []) xs >>= synthIt of
      Nothing                   -> error "Fatal: something bad happened"
      Just ((v, bv), i, g, xs') ->
        let (circ, may') = cnotMinMore (Map.insert v bv input) output xs' may in
            (g ++ synthesizePhase v i ++ circ, may')

cnotMinMost :: Synthesizer
cnotMinMost input output xs may = cnotMinMore input output xs' may
  where xs' = filter (\(_, i) -> order i /= 1) xs


{- Tools for open-ended CNOT-dihedral synthesis -}

-- Given x, U and V, apply a linear transformation L to U such that
--   1) LU(x) = V(x), and
--   2) span(LU - x) = span(V - x)
synthV :: ID -> F2Vec -> LinearTrans -> (LinearTrans, [Primitive])
synthV v x input = case oneSolution (transpose . fromList . Map.elems $ input) x of
  Nothing -> error "Fatal: vector not in linear span"
  Just y  ->
    let u      = case find (y@.) [0..width y-1] of
          Nothing -> v
          Just i  -> (Map.keys input)!!i
        input' = Map.insert u x input
        gates  = linearSynth input input'
    in
      if v == u
        then (input', gates)
        else (Map.insert v x (Map.insert u (input!v) input), gates ++ [Swap u v])
    

addToSpan :: ID -> LinearTrans -> (LinearTrans, [Primitive])
addToSpan v input
  | inLinearSpan (Map.elems . Map.delete v $ input) (input!v) = (input, [])
  | otherwise =
    let (ids, vecs) = unzip $ Map.toList input in
      case findDependent vecs of
        Nothing -> error "Fatal: Adding to span of independent set"
        Just i  -> (Map.insert (ids!!i) (vecs!!i + input!v) input, [CNOT v (ids!!i)])

subsetize :: ID -> LinearTrans -> (F2Vec -> Bool) -> (LinearTrans, [Primitive])
subsetize v input solver =
  let x = input!v 
      f accum u vec
        | u == v || solver vec = (accum, vec)
        | otherwise            = (accum ++ [CNOT v u], vec + x)
  in
    swap $ Map.mapAccumWithKey f [] input

unify :: ID -> LinearTrans -> LinearTrans -> (LinearTrans, [Primitive])
unify v input output =
  let (input', gates) = synthV v (output!v) input
      vSolve = inLinearSpan (Map.elems . Map.delete v $ output)
      (output', gates')
        | vSolve $ output!v = addToSpan v input'
        | otherwise         = subsetize v input' vSolve
  in
    if sameSpace (Map.elems . Map.delete v $ output') (Map.elems . Map.delete v $ output)
      then (output', gates ++ gates')
      else (output, gates ++ (linearSynth input' output))

unifyAffine v input output =
  let f    = Map.foldrWithKey (\id (_, b) xs -> if b then (X id):xs else xs) []
      inX  = f input
      (out, gates) = unify v (Map.map fst input) (Map.map fst output)
  in
    (Map.map (\bv -> (bv, False)) out, inX ++ gates)
  
