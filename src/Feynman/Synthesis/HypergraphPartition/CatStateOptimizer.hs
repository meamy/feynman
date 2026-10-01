module Feynman.Synthesis.HypergraphPartition.CatStateOptimizer
  ( fusePersistentCats
  , CatSpan(..)
  , findCatSpans
  , parseCatEntangler
  , parseCatDisentangler
  , findMatchingCatClose
  , preservesZValue
  , sameCatResource
  , fusionRemoval
  ) where

import Feynman.Core (Primitive(..), ID, getArgs, isZBasisPhaseGate)

import Data.List (sortBy)
import Data.Ord (comparing)

import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

-- One cat-entangler/disentangler pair found in a circuit. The indices are
-- positions in the gate list; *End indices are exclusive.
data CatSpan = CatSpan
  { catOpenStart  :: Int
  , catOpenEnd    :: Int
  , catCloseStart :: Int
  , catCloseEnd   :: Int
  , catBell1      :: ID
  , catBell2      :: ID
  , catSources    :: [ID]
  } deriving (Show)

{- Span detection -}

parseCatEntangler :: [Primitive] -> Maybe (Int, ID, ID, [ID])
parseCatEntangler (H b1 : CNOT c b2 : rest)
  | c == b1 = collect 2 [] rest
  where
    collect k srcs (CNOT src t : xs)
      | t == b2 = collect (k + 1) (srcs ++ [src]) xs
    collect k srcs (Measure m : CNOT c' t' : _)
      | m == b2 && c' == b2 && t' == b1 && not (null srcs)
      = Just (k + 2, b1, b2, srcs)
    collect _ _ _ = Nothing
parseCatEntangler _ = Nothing

parseCatDisentangler :: ID -> Set ID -> [Primitive] -> Maybe Int
parseCatDisentangler b1 wanted (H b : Measure m : rest)
  | b == b1 && m == b1 = collect 2 Set.empty rest
  where
    collect k srcs (CZ b' src : xs)
      | b' == b1 = collect (k + 1) (Set.insert src srcs) xs
    collect k srcs _
      | srcs == wanted && not (Set.null srcs) = Just k
      | otherwise                            = Nothing
parseCatDisentangler _ _ _ = Nothing

findMatchingCatClose :: [Primitive] -> Int -> ID -> Set ID -> Maybe (Int, Int)
findMatchingCatClose circ start b1 srcs = go start (drop start circ)
  where
    go _ [] = Nothing
    go i xs =
      case parseCatDisentangler b1 srcs xs of
        Just len -> Just (i, i + len)
        Nothing  -> go (i + 1) (tail xs)

findCatSpans :: [Primitive] -> [CatSpan]
findCatSpans circ = go 0 circ
  where
    go _ [] = []
    go i xs =
      let rest = go (i + 1) (tail xs)
      in case parseCatEntangler xs of
           Nothing -> rest
           Just (openLen, b1, b2, srcs) ->
             case findMatchingCatClose circ (i + openLen) b1 (Set.fromList srcs) of
               Nothing -> rest
               Just (closeStart, closeEnd) ->
                 CatSpan i (i + openLen) closeStart closeEnd b1 b2 srcs : rest

-- True when a gate leaves the computational-basis value of q unchanged.
-- This is the invariant needed to keep a cat copy of q valid.
preservesZValue :: ID -> Primitive -> Bool
preservesZValue q g
  | q `notElem` getArgs g = True
  | isZBasisPhaseGate g   = True
  | otherwise =
      case g of
        CNOT c _ -> c == q      -- a CNOT does not change its control
        CZ _ _   -> True        -- diagonal in the computational basis
        _        -> False       -- H/X/reset/measure/target-CNOT/etc. are barriers

sameCatResource :: CatSpan -> CatSpan -> Bool
sameCatResource a b =
     catBell1 a == catBell1 b
  && catBell2 a == catBell2 b
  && Set.fromList (catSources a) == Set.fromList (catSources b)

-- Return indices that can be removed when two adjacent uses of the same cat
-- resource can be joined, together with one saved ebit.
fusionRemoval :: [Primitive] -> CatSpan -> CatSpan -> Maybe (Set Int)
fusionRemoval circ a b
  | not (sameCatResource a b) = Nothing
  | catCloseEnd a > catOpenStart b = Nothing
  | otherwise =
      let lo      = catCloseEnd a
          hi      = catOpenStart b
          middle  = zip [lo .. hi - 1] (take (hi - lo) (drop lo circ))
          b1      = catBell1 a
          b2      = catBell2 a
          srcs    = catSources a

          reset1  = [ i | (i, Reset q) <- middle, q == b1 ]
          reset2  = [ i | (i, Reset q) <- middle, q == b2 ]

          -- Bell qubits may only be idle or reset between the two uses.
          bellSafe (_, Reset q) | q == b1 || q == b2 = True
          bellSafe (_, g) = b1 `notElem` getArgs g && b2 `notElem` getArgs g

          -- All source values must remain valid while the cat state is kept.
          srcSafe (_, g) = all (\q -> preservesZValue q g) srcs

          closeIdx = Set.fromList [catCloseStart a .. catCloseEnd a - 1]
          openIdx  = Set.fromList [catOpenStart b  .. catOpenEnd b  - 1]
          resetIdx = Set.fromList (reset1 ++ reset2)
      in if length reset1 == 1 && length reset2 == 1
            && all bellSafe middle && all srcSafe middle
         then Just (Set.unions [closeIdx, resetIdx, openIdx])
         else Nothing

-- Fuse all safe adjacent uses of the same cat resource.  The Int result is the
-- number of ebit initializations removed.
fusePersistentCats :: [Primitive] -> ([Primitive], Int)
fusePersistentCats circ =
  let spans = findCatSpans circ
      key s = (catBell1 s, catBell2 s, Set.fromList (catSources s))
      grouped = Map.elems $ Map.fromListWith (++) [ (key s, [s]) | s <- spans ]
      ordered = map (sortBy (comparing catOpenStart)) grouped
      pairs   = concatMap (\xs -> zip xs (drop 1 xs)) ordered
      removals = [ r | (a,b) <- pairs, Just r <- [fusionRemoval circ a b] ]
      removeSet = Set.unions removals
      optimized = [ g | (i,g) <- zip [0..] circ, Set.notMember i removeSet ]
  in (optimized, length removals)