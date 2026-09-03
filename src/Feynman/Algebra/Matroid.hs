module Feynman.Algebra.Matroid where

import Data.Sequence (Seq, (|>), viewl, ViewL(EmptyL, (:<)))
import qualified Data.Sequence as Seq

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Map (Map)
import qualified Data.Map as Map

-- Replace with a union-find-delete implementation eventually
--data Partition a = Partition [Set a] deriving (Show)
type Partition a = [Set a]

foldParts :: (b -> Set a -> b) -> b -> Partition a -> b
foldParts f x lst = foldl f x lst

-- This is done in a weird way so that x is only found in s once. Not
-- sure if it actually matters with GHC's optimizations
swap :: Ord a => a -> a -> Partition a -> Partition a
swap x y []     = []
swap x y (s:xs) =
  let s' = Set.delete x s in
    if Set.size s' < Set.size s
    then (Set.insert y s'):xs
    else s:(swap x y xs)

-- | The Matroid type class represents mathematical matroids. Matroids are
--   defined by a base set/type a together with an oracle for checking
--   independence of subsets of a. The independence relation should satisfy
--   the following laws:
--
-- > independent Set.empty
-- > independent A /\ Set.isSubsetOf B A ==> independent B
-- > independent A /\ independent B /\ Set.size A > Set.size B ==>
-- >   exists x. Set.member (Set.difference A B) /\ independent (Set.insert x B)
class Ord a => Matroid a where
  independent     :: Set a -> Bool
  independentFrom :: Set a -> a -> Bool
  independentSwap :: Set a -> a -> a -> Bool
  -- Default implementations
  independentFrom s   = independent . (flip Set.insert) s
  independentSwap s x = independent . (Set.insert x) . (flip Set.delete) s

-- | Partitions all elements in a foldable collection
partitionAll :: (Matroid a, Foldable t) => t a -> Partition a
partitionAll = foldr partitionElem []

-- | Adds a single element to a minimal matroid partition
partitionElem :: Matroid a => a -> Partition a -> Partition a
partitionElem x xs =
  let bfs (queue, seen) = case viewl queue of
        EmptyL         -> (Set.singleton x):xs
        path :< queue' ->
          case processNode path (queue', seen) xs of
            Left partition         -> partition
            Right (queue'', seen') -> bfs (queue'', seen')
  in
    bfs (Seq.singleton [x], Set.singleton x)

applyUpdates :: Ord a => [a] -> Partition a -> Partition a
applyUpdates []       partition = partition
applyUpdates (x:[])   partition = case partition of
  []   -> error "Impossible"
  s:xs -> (Set.insert x s):xs
applyUpdates (x:y:xs) partition = applyUpdates (y:xs) $ swap y x partition

tryUpdate :: Matroid a => [a] -> (Seq [a], Set a) -> Set a -> Either (Set a) (Seq [a], Set a)
tryUpdate [] _ _                     = error "Fatal: queue has an empty path"
tryUpdate path@(x:_) (queue, seen) s
  | Set.member x s = Right (queue, seen)
  | otherwise      =
    let s' = Set.insert x s
        f (queue, seen) y =
          if Set.notMember y seen && independent (Set.delete y s')
          then (queue |> (y:path), Set.insert y seen)
          else (queue, seen)
    in
      case independent s' of
        True  -> Left s'
        False -> Right $ Set.foldl f (queue, seen) s

processNode :: Matroid a => [a] -> (Seq [a], Set a) -> Partition a -> Either (Partition a) (Seq [a], Set a)
processNode path (queue, seen) xs =
  let processNodeAcc (queue, seen) sx []     = Right (queue, seen)
      processNodeAcc (queue, seen) sx (s:xs) =
        case tryUpdate path (queue, seen) s of
          Left s'               -> Left $ applyUpdates (reverse path) (s:sx++xs)
          Right (queue', seen') -> processNodeAcc (queue', seen') (s:sx) xs
  in
    processNodeAcc (queue, seen) [] xs

-- Augmentation Algorithm for Matroid Intersection
-- Input: Two matroid M1 = (X, I1) and M2 = (X, I2) and Y subset of I1 /\ I2
-- Output: A larger independent set of M1 and M2, if one exists

matroidIntersection :: Ord a => Set a -> (Set a -> Bool) -> (Set a -> Bool) -> (Set a, Set a, Set a)
matroidIntersection ground indep1 indep2 = go Set.empty
  where
    go y = case findAugmentingPath ground indep1 indep2 y of
      -- If there is existed direct path from Z1 to Z2, output Y'
      -- Y' = {z0,...,zn} \/ {ym+1,...yn} 
      Right path  -> go (symmetricDifference y (Set.fromList path))
      -- Else Y is the largest common independent set of M1 and M2
      -- Return y, partition A and B
      Left (a, b) -> (y, a, b)

symmetricDifference :: Ord a => Set a -> Set a -> Set a
symmetricDifference a b = (a `Set.difference` b) `Set.union` (b `Set.difference` a)

findAugmentingPath:: Ord a => Set a -> (Set a -> Bool) -> (Set a -> Bool) -> Set a -> Either (Set a, Set a)[a]
findAugmentingPath ground indep1 indep2 y
  | not (Set.null trivial) = Right [Set.findMin trivial]
  | otherwise               = bfs initialQueue initialPred
  where
    outside = ground `Set.difference` y

    z1 = Set.filter (\z -> indep1 (Set.insert z y)) outside
    z2 = Set.filter (\z -> indep2 (Set.insert z y)) outside
    trivial = Set.intersection z1 z2

    initialQueue = Seq.fromList (Set.toList z1)
    initialPred  = Map.fromList [(z, Nothing) | z <- Set.toList z1]

    neighbors u
      | Set.member u y = [v | v <- Set.toList outside, indep1 (Set.insert v (Set.delete u y))]
      | otherwise       = [v | v <- Set.toList y,       indep2 (Set.insert u (Set.delete v y))]

    reconstruct pred target = walk target []
      where
        walk n acc = case Map.lookup n pred of
          Just (Just parent) -> walk parent (n:acc)
          _                   -> n:acc

    bfs queue pred = case viewl queue of
      EmptyL    -> Left (reachable, ground `Set.difference` reachable)
        where reachable = Map.keysSet pred
      u :< rest
        | Set.member u z2 -> Right (reconstruct pred u)
        | otherwise         ->
            let new    = [v | v <- neighbors u, not (Map.member v pred)]
                pred'  = foldr (\v m -> Map.insert v (Just u) m) pred new
                queue' = foldl (|>) rest new
            in bfs queue' pred'
