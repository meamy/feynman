module Synthesis.Reversible where

import Data.List hiding (transpose)

import Data.Map.Strict (Map, (!))
import qualified Data.Map.Strict as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Control.Monad.State.Strict
import Control.Monad.Writer.Lazy


import Algebra.Linear
import Synthesis.Phase
import Syntax

type AffineSynthesizer = Map ID (F2Vec, Bool) -> Map ID (F2Vec, Bool) -> [(F2Vec, Int)] -> [Primitive]
type Synthesizer       = Map ID F2Vec -> Map ID F2Vec -> [(F2Vec, Int)] -> [Primitive]

{-- Synthesizers -}
affineTrans :: Synthesizer -> AffineSynthesizer
affineTrans synth = \input output xs ->
  let f    = Map.foldrWithKey (\id (_, b) xs -> if b then (X id):xs else xs) []
      inX  = f input
      outX = f output
  in
    inX ++ (synth (Map.map fst input) (Map.map fst output) xs) ++ outX

emptySynth :: Synthesizer
emptySynth _ _ _ = []

linearSynth :: Synthesizer
linearSynth input output _ =
  let (ids, ivecs) = unzip $ Map.toList input
      (idt, ovecs) = unzip $ Map.toList output
      mat  = transformMat (fromList ivecs) (fromList ovecs)
      rops = snd $ runWriter $ toReducedEchelonPMH mat
      rops' = snd $ runWriter $ toReducedEchelonSqr mat
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
      Nothing                       -> error "Fatal: something bad happened"
      Just ((v, bv), i, g, xs') -> g ++ minimalSequence v i ++ cnotMinMore (Map.insert v bv input) output xs'

cnotMinMost :: Synthesizer
cnotMinMost input output xs = cnotMinMore input output xs'
  where xs' = filter (\(_, i) -> i `mod` 8 /= 0) xs

