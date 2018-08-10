module Feynman.Synthesis.Reversible.Parallel where

import Feynman.Core
import Feynman.Algebra.Base
import Feynman.Algebra.Linear
import Feynman.Algebra.Matroid
import Feynman.Synthesis.Phase
import Feynman.Synthesis.Reversible

import Data.List (partition, intersect)

import Data.Map.Strict (Map, (!))
import qualified Data.Map.Strict as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Control.Monad.State.Strict
import Control.Monad.Writer.Lazy

-- The Matroid from the t-par paper [AMM2014]
instance Matroid (Phase, Int) where
  independent s
    | Set.null s = True
    | otherwise  =
      let ((v, _), n) = head $ Set.toList s
          (vecs, exps) = unzip $ fst $ unzip $ Set.toList s
      in
      (all ((8 <=) . order) exps || all ((8 >) . order) exps)
      && width v - rank (fromList vecs) <= n - (length vecs)

synthPartition :: [Phase] -> ([Primitive], LinearTrans) -> ([Primitive], LinearTrans)
synthPartition xs (circ, input) =
  let (ids, ivecs) = unzip $ Map.toList input
      (vecs, exps) = unzip $ xs
      inp     = fromList ivecs
      targ    = resizeMat (m inp) (n inp) . (flip fillFrom $ inp) . fromList $ vecs
      output  = Map.fromList (zip ids $ toList targ)
      g (n,i) = synthesizePhase (ids!!i) n
      perm    = linearSynth input output
      phase   = concatMap g (zip exps [0..])
  in
    (circ++perm++phase, output)

-- Strictly lazy
tpar :: Synthesizer
tpar input output [] may   = (linearSynth input output, may)
tpar input output must may = (circ ++ linearSynth input' output, may)
  where partitions     = map unwrap . partitionAll $ [(x, length input) | x <- must]
        (circ, input') = foldr synthPartition ([], input) partitions
        unwrap         = fst . unzip . Set.toList

-- Partitions eagerly, but applies partitions lazily
tparAMM :: Synthesizer
tparAMM input output [] may   = (linearSynth input output, may)
tparAMM input output must may = (circ ++ linearSynth input' output, concat may')
  where partitions     = map unwrap . partitionAll $ [(x, length input) | x <- must++may]
        (must', may')  = partition isMust partitions
        (circ, input') = foldr synthPartition ([], input) must'
        unwrap         = fst . unzip . Set.toList
        isMust part    = (intersect must part) /= []

tparMaster input output must may = tparAMM input output must' may'
  where (must', may') = (filter f must, filter f may)
        f (bv, i)     = order i /= 1 && wt bv /= 0
