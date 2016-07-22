module Matroid where

import Data.Sequence (Seq, (|>), viewl, ViewL(EmptyL, (:<)))
import qualified Data.Sequence as Seq

import Data.Set (Set)
import qualified Data.Set as Set

-- Replace with a union-find-delete implementation eventually
data Partition a = Partition [Set a] deriving (Show)

foldParts :: (b -> Set a -> b) -> b -> Partition a -> b
foldParts f x (Partition lst) = foldl f x lst

-- This is done in a weird way so that x is only found in s once. Not
-- sure if it actually matters with GHC's optimizations
swap :: Ord a => a -> a -> Partition a -> Partition a
swap x y (Partition [])     = Partition []
swap x y (Partition (s:xs)) =
  let s' = Set.delete x s in
    if Set.size s' < Set.size s
    then Partition $ (Set.insert y s'):xs
    else
      let (Partition res) = swap x y (Partition xs) in
        Partition (s:res)

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


-- | Adds a single element to a minimal matroid partition
partitionElem :: Matroid a => a -> Partition a -> Partition a
partitionElem x (Partition xs) =
  let bfs (queue, seen) = case viewl queue of
        EmptyL         -> Partition ((Set.singleton x):xs)
        path :< queue' ->
          case processNode path (queue', seen) (Partition xs) of
            Left partition        -> partition
            Right (queue', seen') -> bfs (queue', seen')
  in
    bfs (Seq.singleton [x], Set.empty)

applyUpdates :: Ord a => [a] -> Partition a -> Partition a
applyUpdates []       partition = partition
applyUpdates (x:[])   partition = partition
applyUpdates (x:y:xs) partition = applyUpdates (y:xs) $ swap x y partition

tryUpdate :: Matroid a => [a] -> (Seq [a], Set a) -> Set a -> Either (Set a) (Seq [a], Set a)
tryUpdate [] _ _                     = error "Fatal: queue has an empty path"
tryUpdate path@(x:_) (queue, seen) s =
  let s' = Set.insert x s
      f (queue, seen) y =
        if Set.notMember y seen && independentFrom s' y
        then (queue |> (y:path), Set.insert y seen)
        else (queue, seen)
  in
    case independent s of
      True  -> Left s'
      False -> Right $ Set.foldl f (queue, seen) s

processNode :: Matroid a => [a] -> (Seq [a], Set a) -> Partition a -> Either (Partition a) (Seq [a], Set a)
processNode path (queue, seen) (Partition xs) =
  let processNodeAcc (queue, seen) sx []     = Right (queue, seen)
      processNodeAcc (queue, seen) sx (s:xs) =
        case tryUpdate path (queue, seen) s of
          Left s'               -> Left $ applyUpdates path $ Partition (sx ++ s':xs)
          Right (queue', seen') -> processNodeAcc (queue', seen') (s:sx) xs
  in
    processNodeAcc (queue, seen) [] xs

{-
enqueue :: a -> State (Seq a) ()
enqueue x = modify (|> x)

dequeue :: State (Seq a) (Maybe a)
dequeue = get >>= dequeue'
  where dequeue' queue = case viewl queue of
          EmptyL      -> return Nothing
          x <: queue' -> put queue' >> return x

tryUpdate [] _ _ = error "Fatal: queue has an empty path"
tryUpdate path@(x:_) marks s =
  let s' = Set.insert x s
      f marks y =
        if not (Set.elem y marks) && independentFrom s' y
        then do
          enqueue (y:path)
          return $ Right $ Set.insert y marks
        else
          return $ Right marks
  in
    case independent s of
      True  -> return $ Left s'
      False -> foldM f marks s

-- Experiment here. 
processNode :: [a] -> Set a -> Partition a -> StateT (Seq a) (Either (Set a)) Set a
processNode [] _ _ = error "Fatal: queue has an empty path"
processNode path marks partition = do
  res <- foldM (tryUpdate path) marks partition
  case res of
    Left s' -> 

return $ Right marks
processNode path@(x:_) marks s =
  let s' = Set.insert x s
      f marks y =
        if not (Set.elem y marks) && independentFrom s' y
        then do
          enqueue (y:path)
          return $ Set.insert y marks
        else
          return marks
  in
    case independent s of
      True  -> return $ Left $ applyUpdates path (Partition $ s':xs)
      False -> foldM f marks s

  evalState partitionWithQueue Seq.empty
-}
