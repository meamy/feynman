{-|
Module      : Clifford
Description : Optimization of Clifford circuits
Copyright   : (c) Matthew Amy, 2021
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Feynman.Optimization.Clifford(simplifyCliffords,simplifyCliffords') where

import Feynman.Core(Primitive(..),
                    AnnotatedPrimitive,
                    annotate,
                    annotateWith,
                    unannotate,
                    ids)
import Feynman.Synthesis.Pathsum.Clifford(resynthesizeClifford)

{-----------------------------------
 Utilities
 -----------------------------------}

-- | Check whether a primitive gate is Clifford
isClifford :: Primitive -> Bool
isClifford gate = case gate of
  H _      -> True
  X _      -> True
  Y _      -> True
  Z _      -> True
  CNOT _ _ -> True
  CZ _ _   -> True
  S _      -> True
  Sinv _   -> True
  T _      -> False
  Tinv _   -> False
  Swap _ _ -> True
  Rz _ _   -> False
  Rx _ _   -> False
  Ry _ _   -> False
  _        -> False

-- | Check whether two gates commute
commutes :: Primitive -> Primitive -> Bool
commutes g1 g2
  | all (`notElem` (ids [g2])) $ ids [g1] = True
  | otherwise                             = case (g1, g2) of
      (Z _, T _)                  -> True
      (Z _, Tinv _)               -> True
      (Z _, Rz _ _)               -> True
      (S _, T _)                  -> True
      (S _, Tinv _)               -> True
      (S _, Rz _ _)               -> True
      (Sinv _, T _)               -> True
      (Sinv _, Tinv _)            -> True
      (Sinv _, Rz _ _)            -> True
      (CNOT x _, T y)    | x == y -> True
      (CNOT x _, Tinv y) | x == y -> True
      (CNOT x _, Rz _ y) | x == y -> True
      _                           -> False

-- | Check whether a gate commutes with a circuit
commutesWith :: Primitive -> [Primitive] -> Bool
commutesWith g = all (commutes g)

{-----------------------------------
 Optimization
 -----------------------------------}

-- | Takes a gate list, partitions it into Clifford circuits greedily & re-synthesizes the Clifford parts
simplifyCliffords :: [Primitive] -> [Primitive]
simplifyCliffords = go [] ([], []) where
  finalize (c, t)           = (resynthesizeClifford $ reverse c) ++ (reverse t)
  go acc (c, t) []          = acc ++ finalize (c, t)
  go acc (c, t) (gate:xs)
    | not (isClifford gate) = go acc (c, gate:t) xs
    | gate `commutesWith` t = go acc (gate:c, t) xs
    | otherwise             = go (acc ++ finalize (c, t)) ([gate], []) xs

-- | Annotated version
simplifyCliffords' :: [AnnotatedPrimitive] -> [AnnotatedPrimitive]
simplifyCliffords' circ = go mx [] ([], []) circ where
  mx = maximum . map snd $ circ

  finalize mx (c, t) =
    let c' = resynthesizeClifford . reverse . unannotate $ c in
      (mx + length c', ((flip zip) [mx+1..] c') ++ reverse t)

  go mx acc (c, t) []                    = acc ++ snd (finalize mx (c, t))
  go mx acc (c, t) ((gate,l):xs)
    | not (isClifford gate)              = go mx acc (c, (gate,l):t) xs
    | gate `commutesWith` (unannotate t) = go mx acc ((gate,l):c, t) xs
    | otherwise                          =
      let (mx', circ') = finalize mx (c, t) in
        go mx' (acc ++ circ') ([(gate,l)], []) xs
