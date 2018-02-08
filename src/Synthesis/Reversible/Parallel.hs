module Synthesis.Reversible.Parallel where

import Data.Map.Strict (Map, (!))
import qualified Data.Map.Strict as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Control.Monad.State.Strict
import Control.Monad.Writer.Lazy

import Core
import Algebra.Linear
import Algebra.Matroid
import Synthesis.Phase
import Synthesis.Reversible

-- The Matroid from the t-par paper [AMM2014]
instance Matroid ((F2Vec, Int), Int) where
  independent s
    | Set.null s = True
    | otherwise  =
      let ((v, _), n) = head $ Set.toList s
          (vecs, exps) = unzip $ fst $ unzip $ Set.toList s
      in
      (all (\i -> i `mod` 2 == 1) exps || all (\i -> i `mod` 2 == 0) exps)
      && width v - rank (fromList vecs) <= n - (length vecs)

tpar :: Synthesizer
tpar input output [] = linearSynth input output []
tpar input output xs =
  let partition      = partitionAll (zip xs $ repeat $ length input)
      (circ, input') = foldr synthPartition ([], input) partition
  in
    circ ++ linearSynth input' output []

synthPartition set (circ, input) =
  let (ids, ivecs) = unzip $ Map.toList input
      (vecs, exps) = unzip $ fst $ unzip $ Set.toList set
      inp = fromList ivecs
      targ = fromList vecs
      mat = increaseRankN (transformMat inp targ) (length input - length vecs)
      rops = snd $ runWriter $ toReducedEchelon mat
      f op = case op of
        Add i j  -> [CNOT (ids !! i) (ids !! j)]
        Exchange i j ->
          let (v, u) = (ids !! i, ids !! j) in
            [Swap v u]
      g (n, i) = minimalSequence (ids !! i) n
      perm = concatMap f rops
      phase = concatMap g (zip exps [0..])
      output = Map.fromList $ zip ids $ vals $ mult mat inp
  in
    (circ++perm++phase, output)

tparMore input output xs = tpar input output xs'
  where xs' = filter (\(_, i) -> i `mod` 8 /= 0) xs
