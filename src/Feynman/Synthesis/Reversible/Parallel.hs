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

import Debug.Trace (trace)

-- The Matroid from the t-par paper [AMM2014]
-- Note that this is kind of a nasty hack due to the way Matroids
-- were programmed. TODO: fix Matroid partitioning so that we don't
-- need to carry all the context information necessary for defining
-- independence with each element
-- AMM t m n gives the independence instance where a set of phase terms
-- T is independent if and only if m - rank(T) <= n - |T|
data AMM = AMM Phase Int Int

instance Eq AMM where
  (AMM t _ _) == (AMM t' _ _) = t == t'

instance Ord AMM where
  (AMM t _ _) <= (AMM t' _ _) = t <= t'

instance Show AMM where
  show (AMM t _ _) = show t
  
instance Matroid AMM where
  independent s
    | Set.null s = True
    | otherwise  =
      let (AMM _ m n)  = head $ Set.toList s
          (vecs, exps) = unzip . map (\(AMM t _ _) -> t) $ Set.toList s
          toTorNotToT  = all ((8 ==) . order) exps || all ((8 /=) . order) exps
          extensible   = m - rank (fromList vecs) <= n - (length vecs)
      in
        toTorNotToT && extensible

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
tparLazy :: Synthesizer
tparLazy input output [] may   = (linearSynth input output, may)
tparLazy input output must may = (circ ++ linearSynth input' output, may)
  where terms          = [AMM x (rank . fromList $ Map.elems input) (length input) | x <- must]
        partitions     = map (map (\(AMM t _ _) -> t) . Set.toList) . partitionAll $ terms
        (circ, input') = foldr synthPartition ([], input) partitions

-- Partitions eagerly, but applies partitions lazily
tparAMM :: Synthesizer
tparAMM input output must may = (circ ++ linearSynth input' output, concat may')
  where terms          = [AMM x (rank . fromList $ Map.elems input) (length input) | x <- must++may]
        partitions     = map (map (\(AMM t _ _) -> t) . Set.toList) . partitionAll $ terms
        (must', may')  = partition isMust partitions
        (circ, input') = foldr synthPartition ([], input) must'
        isMust part    = (intersect must part) /= []

tparMaster input output must may = tparAMM input output must' may'
  where (must', may') = (filter f must, filter f may)
        f (bv, i)     = order i /= 1 && wt bv /= 0
