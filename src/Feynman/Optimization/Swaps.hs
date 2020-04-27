module Feynman.Optimization.Swaps (pushSwaps) where

import Data.Map (Map, (!))
import qualified Data.Map as Map

import Feynman.Core

-- Permutations on /a/
data Permutation a = Permutation !(Map a a) !(Map a a) deriving (Eq, Ord, Show)

identity :: Permutation a
identity = Permutation Map.empty Map.empty

fLookup :: Ord a => a -> Permutation a -> a
fLookup x (Permutation fperm _) = Map.findWithDefault x x fperm

bLookup :: Ord a => a -> Permutation a -> a
bLookup x (Permutation _ bperm) = Map.findWithDefault x x bperm

swap :: Ord a => a -> a -> Permutation a -> Permutation a
swap x y (Permutation fperm bperm) = Permutation fperm' bperm' where
  x0 = Map.findWithDefault x x bperm
  y0 = Map.findWithDefault y y bperm
  fperm' = Map.insert x0 y (Map.insert y0 x fperm)
  bperm' = Map.insert x y0 (Map.insert y x0 bperm)

unSwap :: Ord a => a -> a -> Permutation a -> Permutation a
unSwap x y (Permutation fperm bperm) = Permutation fperm' bperm' where
  x' = Map.findWithDefault x x fperm
  y' = Map.findWithDefault y y fperm
  fperm' = Map.insert x y' (Map.insert y x' fperm)
  bperm' = Map.insert x' y (Map.insert y' x bperm)

support :: Ord a => Permutation a -> [a]
support (Permutation fperm _) = Map.keys fperm

toSwaps :: Permutation ID -> [Primitive]
toSwaps perm = go perm (support perm) where
  go perm []     = []
  go perm (x:xs)
    | bLookup x perm == x = go perm xs
    | otherwise           = (Swap x y):(go (unSwap x y perm) xs) where
        y = bLookup x perm

-- Hoist swaps out of code. Useful mainly so that T-par doesn't
-- have to worry about clever orderings itself

pushSwaps :: [Primitive] -> [Primitive]
pushSwaps = go identity where
  go perm []          = toSwaps perm
  go perm (gate:circ) = case gate of
    Swap x y -> go (swap x y perm) circ
    _        -> gate':(go perm circ) where
      gate' = substGate (flip bLookup $ perm) gate
