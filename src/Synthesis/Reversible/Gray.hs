module Synthesis.Reversible.Gray where

import Data.List hiding (transpose)

import Data.Map.Strict (Map, (!))
import qualified Data.Map.Strict as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Control.Monad.State.Strict
import Control.Monad.Writer.Lazy

import Data.Bits

import Algebra.Base
import Algebra.Linear
import Synthesis.Phase
import Synthesis.Reversible
import Core

{- Gray code synthesis -}
data Pt = Pt {
  candidates :: [Int],
  target     :: Maybe Int,
  pending    :: Maybe Int,
  vectors    :: [(F2Vec, Angle)]
} deriving Show

adjust :: Int -> Int -> [Pt] -> [Pt]
adjust t p xs = map f xs
  where f (Pt c t p vecs) = Pt c t p $ map g vecs
        g (bv, i) = (if bv@.t then complementBit bv p else bv, i)

findColumnSplit :: [Int] -> [(F2Vec, Angle)] -> ([(F2Vec, Angle)], Int, [Int], [(F2Vec, Angle)])
findColumnSplit (c:cs) vecs = foldl' g init cs
  where f c  = partition (\(bv, _) -> not $ bv@.c) vecs
        init = case f c of (l, r) -> (l, c, [], r)
        g (l, c, cs, r) c' =
          let (l', r') = f c' in
            if length r' > length r
            then (l', c', c:cs, r')
            else (l, c, c':cs, r)

findBestSplit :: [Int] -> [(F2Vec, Angle)] -> ([(F2Vec, Angle)], Int, [Int], [(F2Vec, Angle)])
findBestSplit (c:cs) vecs = foldl' g init cs
  where f c  = partition (\(bv, _) -> not $ bv@.c) vecs
        init = case f c of (l, r) -> (l, c, [], r)
        g (l, c, cs, r) c' =
          let (l', r') = f c' in
            if max (length l') (length r') > max (length l) (length r)
            then (l', c', c:cs, r')
            else (l, c, c':cs, r)

graySynthesis :: [ID] -> Map ID F2Vec -> [Pt] -> Writer [Primitive] (Map ID F2Vec)
graySynthesis ids out []     = return out
graySynthesis ids out (x:xs) = case x of
  Pt _ _ _ [] -> graySynthesis ids out xs
  Pt c (Just t) (Just p) v ->
    let idp  = ids !! p
        idt  = ids !! t
        xs'  = (Pt c (Just t) Nothing v):(adjust t p xs)
        out' = case (out!idp, out!idt) of
          (bvp, bvt) -> Map.insert idt (bvp + bvt) out
    in do
      tell [CNOT idp idt]
      graySynthesis ids out' xs'
  Pt [] (Just t) Nothing [(_, a)] -> do
    tell $ synthesizePhase (ids !! t) a
    graySynthesis ids out xs
  Pt [] Nothing _ _ -> graySynthesis ids out xs
  Pt (c:cs) targ Nothing vecs ->
    let (vl, c', cs', vr) = findBestSplit (c:cs) vecs
        xzero = Pt cs' targ Nothing vl
        xone  = case targ of
          Just t  -> Pt cs' targ (Just c') vr
          Nothing -> Pt cs' (Just c') Nothing vr
    in
      graySynthesis ids out $ xzero:xone:xs

cnotMinGray0 :: Synthesizer
cnotMinGray0 input output [] = linearSynth input output []
cnotMinGray0 input output xs =
  let ivecs  = Map.toList input
      solver = oneSolution $ transpose $ fromList $ snd $ unzip ivecs
  in
    case mapM (\(vec, i) -> solver vec >>= \vec' -> Just (vec', i)) xs of
      Nothing  -> error "Fatal: something bad happened"
      Just xs' ->
        let initPt         = [Pt [0..length ivecs - 1] Nothing Nothing xs']
            (outin, gates) = runWriter $ graySynthesis (fst $ unzip ivecs) input initPt
        in
          gates ++ linearSynth outin output []

cnotMinGray input output xs =
  let gates  = cnotMinGray0 input output xs
      gates' = cnotMinGray0 input output $ filter (\(_, i) -> order i /= 1) xs
      isct g = case g of
        CNOT _ _  -> True
        otherwise -> False
      countc = length . filter isct
  in
    if countc gates < countc gates' then gates else gates'

{- Temp for testing -}
ids  = ["a", "b", "c", "d"]
vecs = Set.fromList [bitVec 4 6, bitVec 4 1, bitVec 4 9, bitVec 4 7, bitVec 4 11, bitVec 4 3]
outs = Map.fromList [("a", bitVec 4 1), ("b", bitVec 4 2), ("c", bitVec 4 4), ("d", bitVec 4 8)]

idsz  = ["a", "b", "c"]
vecsz = Set.delete (bitVec 3 0) $ Set.fromList $ allVecs 3
outsz = Map.fromList [("a", bitVec 3 1), ("b", bitVec 3 2), ("c", bitVec 3 4)]

-- Verification & brute force for skeletons

maximalSkeleton :: [ID] -> Map ID F2Vec -> [Primitive] -> Set F2Vec
maximalSkeleton ids st gates = snd $ Data.List.foldl f (st, Set.fromList $ Map.elems st) gates
  where f (st, vals) (CNOT c t) =
          let tmp = (st!t) + (st!c) in
            (Map.insert t tmp st, Set.insert tmp vals)
        f (st, vals) _          = (st, vals)

maximalASkeleton :: [ID] -> Map ID F2Vec -> [Primitive] -> (Map ID F2Vec, Set F2Vec)
maximalASkeleton ids st gates = Data.List.foldl f (st, Set.fromList $ Map.elems st) gates
  where f (st, vals) (CNOT c t) =
          let tmp = (st!t) + (st!c) in
            (Map.insert t tmp st, Set.insert tmp vals)
        f (st, vals) _          = (st, vals)

allCNOTs :: [ID] -> [[Primitive]]
allCNOTs ids = concatMap f ids
  where f id = [ [CNOT id id'] | id'<-ids, id /= id']

allSkeletons :: [ID] -> [[Primitive]]
allSkeletons ids = allCNOTs ids ++ [x++y | y<-allSkeletons ids, x<-allCNOTs ids]

bruteForceSkeleton :: [ID] -> Set F2Vec -> Maybe [Primitive]
bruteForceSkeleton ids vals = find (Set.isSubsetOf vals . maximalSkeleton ids st) $ allSkeletons ids
  where st = genInitSt ids

bruteForceASkeleton :: [ID] -> Set F2Vec -> Map ID F2Vec -> Maybe [Primitive]
bruteForceASkeleton ids vals out = find (verify . maximalASkeleton ids st) $ allSkeletons ids
  where st               = genInitSt ids
        verify (st, set) = st == out && Set.isSubsetOf vals set

genInitSt :: [ID] -> Map ID F2Vec
genInitSt ids = Map.fromList $ map (\(id, i) -> (id, bitI (length ids) i)) $ zip ids [0..]
