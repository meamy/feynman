module TPar where

import Data.List hiding (transpose)

import Data.Map.Strict (Map, (!))
import qualified Data.Map.Strict as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Data.BitVector hiding (replicate, foldr, concat, reverse, not)
import Syntax
import Linear

import Control.Monad.State.Strict
import Control.Monad.Writer.Lazy

import Data.Graph.Inductive as Graph
import Data.Graph.Inductive.Query.DFS

import PhaseFold (foo)
import Matroid

import Debug.Trace

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
      rops = snd $ runWriter $ toReducedEchelonSqr mat
      f op = case op of
        Add i j  -> [CNOT (ids !! i) (ids !! j)]
        Exchange i j ->
          let (v, u) = (ids !! i, ids !! j) in
            [Swap v u]
  in
    if ids /= idt
    then error "Fatal: map keys not equal"
    else reverse $ concatMap f rops

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
      Nothing                       -> error "Fatal: something bad happened"
      Just ((v, bv), i, g, xs') -> g ++ minimalSequence v i ++ cnotMinMore (Map.insert v bv input) output xs'

cnotMinMost :: Synthesizer
cnotMinMost input output xs = cnotMinMore input output xs'
  where xs' = filter (\(_, i) -> i `mod` 8 /= 0) xs

-- The Matroid from the t-par paper [AMM2014]
instance Matroid ((F2Vec, Int), Int) where
  independent s
    | Set.null s = True
    | otherwise  =
      let ((v, _), n) = head $ Set.toList s
          (vecs, exps) = unzip $ fst $ unzip $ Set.toList s
      in
      (all (\i -> i `mod` 2 == 1) exps || all (\i -> i `mod` 2 == 0) exps)
      && width (getBV v) - rank (fromList vecs) <= n - (length vecs)

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

{- General synthesis utilities -}
minimalSequence :: ID -> Int -> [Primitive]
minimalSequence x i = case i `mod` 8 of
  0 -> []
  1 -> [T x]
  2 -> [S x]
  3 -> [Z x, Tinv x]
  4 -> [Z x]
  5 -> [Z x, T x]
  6 -> [Sinv x]
  7 -> [Tinv x]

{- Gray code synthesis -}
data Pt = Pt {
  candidates :: [Int],
  target     :: Maybe Int,
  pending    :: Maybe Int,
  vectors    :: [(F2Vec, Int)]
} deriving Show

adjust :: Int -> Int -> [Pt] -> [Pt]
adjust t p xs = map f xs
  where f (Pt c t p vecs) = Pt c t p $ map g vecs
        g (F2Vec bv, i) = (if bv@.t then F2Vec $ complementBit bv p else F2Vec $ bv, i)

findColumnSplit :: [Int] -> [(F2Vec, Int)] -> ([(F2Vec, Int)], Int, [Int], [(F2Vec, Int)])
findColumnSplit (c:cs) vecs = foldl' g init cs
  where f c  = partition (\(F2Vec bv, _) -> not $ bv@.c) vecs
        init = case f c of (l, r) -> (l, c, [], r)
        g (l, c, cs, r) c' =
          let (l', r') = f c' in
            if length r' > length r then (l', c', c:cs, r') else (l, c, c':cs, r)

findBestSplit :: [Int] -> [(F2Vec, Int)] -> ([(F2Vec, Int)], Int, [Int], [(F2Vec, Int)])
findBestSplit (c:cs) vecs = foldl' g init cs
  where f c  = partition (\(F2Vec bv, _) -> not $ bv@.c) vecs
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
          (F2Vec bvp, F2Vec bvt) -> Map.insert idt (F2Vec $ bvp `xor` bvt) out
    in do
      tell [CNOT idp idt]
      graySynthesis ids out' xs'
  Pt [] (Just t) Nothing [(_, a)] -> do
    tell $ minimalSequence (ids !! t) a
    graySynthesis ids out xs
  Pt (c:cs) targ Nothing vecs ->
    let (vl, c', cs', vr) = findBestSplit (c:cs) vecs
        xzero = Pt cs' targ Nothing vl
        xone  = case targ of
          Just t  -> Pt cs' targ (Just c') vr
          Nothing -> Pt cs' (Just c') Nothing vr
    in
      graySynthesis ids out $ xzero:xone:xs

cnotMinGray :: Synthesizer
cnotMinGray input output [] = linearSynth input output []
cnotMinGray input output xs =
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

{- Temp for testing -}
ids  = ["a", "b", "c"]
ot   = Map.fromList [("a", bb 3 1), ("b", bb 3 2), ("c", bb 3 4)]
cs   = [0, 1, 2]
vecs = tail $ zip (allVecs 3) (repeat 1)
test = graySynthesis ids ot [Pt cs Nothing Nothing vecs]
