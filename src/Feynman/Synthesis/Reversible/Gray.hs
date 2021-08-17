module Feynman.Synthesis.Reversible.Gray where

import Feynman.Core
import Feynman.Algebra.Base
import Feynman.Algebra.Linear
import Feynman.Synthesis.Phase
import Feynman.Synthesis.Reversible

import Data.List hiding (transpose)

import Data.Map.Strict (Map, (!))
import qualified Data.Map.Strict as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Ord (comparing)

import Data.Maybe

import Control.Monad.State.Strict
import Control.Monad.Writer.Lazy

import Data.Bits
import Debug.Trace

{- Gray code synthesis -}
data Pt = Pt {
  candidates :: [Int],
  target     :: Maybe Int,
  pending    :: Maybe Int,
  vectors    :: [Phase]
} deriving Show

adjust :: Int -> Int -> [Pt] -> [Pt]
adjust t p xs = map f xs
  where f (Pt c t p vecs) = Pt c t p $ map g vecs
        g (bv, i) = (if bv@.t then complementBit bv p else bv, i)

findBestSplit :: [Int] -> [Phase] -> ([Phase], Int, [Int], [Phase])
findBestSplit (c:cs) vecs = foldl' g init cs
  where f c  = partition (\(bv, _) -> not $ bv@.c) vecs
        init = case f c of (l, r) -> (l, c, [], r)
        g (l, c, cs, r) c' =
          let (l', r') = f c' in
            if max (length l') (length r') >= max (length l) (length r)
            then (l', c', c:cs, r')
            else (l, c, c':cs, r)

findBestSplitMono :: [Int] -> [Phase] -> ([Phase], Int, [Int], [Phase])
findBestSplitMono xs vecs = (l, c, delete c xs, r)
  where f c  = partition (\(bv, _) -> not $ bv@.c) vecs
        countCol c =
            let (l, r) = f c in
            max (length l) (length r)
        c = maximumBy (comparing countCol) xs
        (l, r) = f c

graySynthesis :: [ID] -> LinearTrans -> [Pt] -> [Phase] -> Writer [Primitive] (LinearTrans, [Phase])
graySynthesis ids out []     may = return (out, may)
graySynthesis ids out (x:xs) may = case x of
  Pt _ _ _ [] -> graySynthesis ids out xs may
  Pt c (Just t) (Just p) v ->
    let (idp, idt) = (ids!!p, ids!!t)
        (bvp, bvt) = (out!idp, out!idt)
        xs'  = (Pt c (Just t) Nothing v):(adjust t p xs)
        out' = Map.insert idt (bvp + bvt) out
    in do
      tell [CNOT idp idt]
      case find (\(bv, _) -> bvp + bvt == bv) may of
        Nothing      -> graySynthesis ids out' xs' may
        Just (bv, a) -> do
          tell $ synthesizePhase idt a
          graySynthesis ids out' xs' (delete (bv, a) may)
  Pt [] (Just t) Nothing [(_, a)] -> do
    tell $ synthesizePhase (ids !! t) a
    graySynthesis ids out xs may
  Pt [] Nothing _ _ -> graySynthesis ids out xs may
  Pt (c:cs) targ Nothing vecs ->
    let (vl, c', cs', vr) = findBestSplitMono (c:cs) vecs
        xzero = Pt cs' targ Nothing vl
        xone  = case targ of
          Just t  -> Pt cs' targ (Just c') vr
          Nothing -> Pt cs' (Just c') Nothing vr
    in
      graySynthesis ids out (xzero:xone:xs) may

-- Optionally adds "may" phases whenever possible
addMay :: LinearTrans -> [Phase] -> [Primitive] -> ([Primitive], [Phase])
addMay st phases = (\(a,b) -> (reverse a,b)) . snd . foldl' go (st,([],phases)) where
  go (st,(circ,may)) gate@(CNOT c t) =
    let tmp = (st!t) + (st!c) in
      case partition (\phase -> fst phase == tmp) may of
        ([], may')      -> (Map.insert t tmp st, (gate:circ, may'))
        ([phase], may') -> (Map.insert t tmp st, (circ', may')) where
          circ' = synthesizePhase t (snd phase) ++ (gate:circ)
  go (st,(circ,may)) gate = (st,(gate:circ,may))

-- Pointed
cnotMinGrayPointed0 :: Synthesizer
cnotMinGrayPointed0 input output [] may = (linearSynth input output, may)
cnotMinGrayPointed0 input output xs may =
  let ivecs    = Map.toList input
      solver   = oneSolution $ transpose $ fromList $ snd $ unzip ivecs
      f (v, i) = solver v >>= \v' -> Just (v', i)
  in
    case mapM f xs of
      Nothing  -> error "Fatal: something bad happened"
      Just xs' ->
        let initPt       = [Pt [0..length ivecs - 1] Nothing Nothing xs']
            ((o, []), g) = runWriter $ graySynthesis (fst $ unzip ivecs) input initPt []
            (g',m')      = addMay input may g
        in
          (g' ++ linearSynth o output, m')

-- non-pointed synthesis
cnotMinGrayOpen0 :: OpenSynthesizer
cnotMinGrayOpen0 input [] = (input, [])
cnotMinGrayOpen0 input xs =
  let ivecs    = Map.toList input
      solver   = oneSolution $ transpose $ fromList $ snd $ unzip ivecs
      f (v, i) = solver v >>= \v' -> Just (v', i)
  in
    case mapM f xs of
      Nothing  -> error "Fatal: something bad happened"
      Just xs' ->
        let initPt      = [Pt [0..length ivecs - 1] Nothing Nothing xs']
            ((o, _), g) = runWriter $ graySynthesis (fst $ unzip ivecs) input initPt []
        in
          (o, g)

{- Master method -}

-- Fastest
cnotMinGray i o must may = cnotMinGrayPointed0 i o (filter (\(_, i) -> order i /= 1) must) may

-- Eagerly applies phases
cnotMinGrayEager = \i o mu ma -> cnotMinGrayPointed0 i o (mu ++ ma) []

-- Compares between configurations (doubles runtime but best performance)
cnotMinGrayPointed input output xs may =
  let result1 = cnotMinGrayPointed0 input output xs may
      result2 = cnotMinGrayPointed0 input output (filter (\(_, i) -> order i /= 1) xs) may
      isct g = case g of
        CNOT _ _  -> True
        otherwise -> False
      countc = length . filter isct . fst
  in
    minimumBy (comparing countc) [result1, result2]

-- Compares between open-ended configurations
cnotMinGrayOpen input xs =
  let gates   = cnotMinGrayOpen0 input xs
      gates'  = cnotMinGrayOpen0 input $ filter (\(_, i) -> order i /= 1) xs
      isct g = case g of
        CNOT _ _  -> True
        otherwise -> False
      countc = length . filter isct . snd
  in
    minimumBy (comparing countc) [gates, gates']

{- Recursive gray-synth (slower) -}
graySynth :: [ID] -> [Phase] -> ([Primitive], F2Mat)
graySynth ids xs = runState (go [0..n-1] Nothing xs) (identity n) where
  n = length ids
  go _  _        []  = return []
  go [] (Just t) [x] = return $ synthesizePhase (ids!!t) (snd x)
  go [] Nothing  _   = return []
  go cs target   xs  = do
    a <- get
    let xs' = map (\(xor,angle) -> (multRow xor a, angle)) xs
    let (zeros, pivot, cs', ones) = findBestSplitMono cs xs'
    put $ identity n
    lcirc <- go cs' target zeros
    case ones of
      [] -> modify (mult a) >> return lcirc
      _  -> do
        modify $ fromMaybe id (fmap (addRow pivot) target)
        let gate = fmap (\t -> [CNOT (ids!!pivot) (ids!!t)]) target
        rcirc <- go cs' (mplus target $ Just pivot) ones
        modify $ mult a
        return $ lcirc ++ (fromMaybe [] gate) ++ rcirc
    
{- Brute force synthesis -}

maximalSkeleton :: [ID] -> LinearTrans -> [Primitive] -> Set F2Vec
maximalSkeleton ids st gates = snd $ Data.List.foldl f (st, Set.fromList $ Map.elems st) gates
  where f (st, vals) (CNOT c t) =
          let tmp = (st!t) + (st!c) in
            (Map.insert t tmp st, Set.insert tmp vals)
        f (st, vals) _          = (st, vals)

maximalASkeleton :: [ID] -> LinearTrans -> [Primitive] -> (LinearTrans, Set F2Vec)
maximalASkeleton ids st gates = Data.List.foldl f (st, Set.fromList $ Map.elems st) gates
  where f (st, vals) (CNOT c t) =
          let tmp = (st!t) + (st!c) in
            (Map.insert t tmp st, Set.insert tmp vals)
        f (st, vals) _          = (st, vals)

allCNOTs :: [ID] -> [[Primitive]]
allCNOTs ids = concatMap f ids
  where f id = [ [CNOT id id'] | id'<-ids, id /= id']

allSkeletons :: [ID] -> [[Primitive]]
allSkeletons ids = [[]] ++ allCNOTs ids ++ [x++y | y<-allSkeletons ids, x<-allCNOTs ids]

check :: [ID] -> LinearTrans -> Set F2Vec -> [Primitive] -> Bool
check ids st vals = Set.isSubsetOf vals . maximalSkeleton ids st

bruteForceSkeleton :: [ID] -> Set F2Vec -> Maybe [Primitive]
bruteForceSkeleton ids vals = find (Set.isSubsetOf vals . maximalSkeleton ids st) $ allSkeletons ids
  where st = genInitSt ids

bruteForceASkeleton :: [ID] -> Set F2Vec -> LinearTrans -> Maybe [Primitive]
bruteForceASkeleton ids vals out = find (verify . maximalASkeleton ids st) $ allSkeletons ids
  where st               = genInitSt ids
        verify (st, set) = st == out && Set.isSubsetOf vals set

genInitSt :: [ID] -> LinearTrans
genInitSt ids = Map.fromList $ map (\(id, i) -> (id, bitI (length ids) i)) $ zip ids [0..]
