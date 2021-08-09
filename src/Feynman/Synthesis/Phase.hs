module Feynman.Synthesis.Phase where

import Feynman.Core
import Feynman.Algebra.Base

synthesizePhase :: ID -> Angle -> [Primitive]
synthesizePhase x theta@(Continuous _) = [Rz theta x]
synthesizePhase x theta@(Discrete dy)
  | a == 0 = []
  | n == 0 = [Z x]
  | n == 1 = case a `mod` 4 of
      1 -> [S x]
      3 -> [Sinv x]
  | n == 2 = case a `mod` 8 of
      1 -> [T x]
      3 -> [Tinv x, Z x]
      5 -> [T x, Z x]
      7 -> [Tinv x]
  | otherwise = [Rz theta x]
  where (Dy a n) = unpack dy

globalPhase :: ID -> Angle -> [Primitive]
globalPhase x theta@(Continuous _) = [Rz theta x, X x, Rz theta x, X x]
globalPhase x theta@(Discrete dy)
  | a == 0 = []
  | n == 0 = [Z x, X x, Z x, X x]
  | n == 1 = case a `mod` 4 of
      1 -> [S x, X x, S x, X x]
      3 -> [Sinv x, X x, Sinv x, X x]
  | n == 2 = case a `mod` 8 of
      1 -> [H x, S x, H x, S x, H x, S x]
      3 -> [H x, S x, H x, S x, H x, Z x, X x, S x, X x]
      5 -> [H x, S x, H x, S x, H x, Sinv x, X x, Z x, X x]
      7 -> [H x, Sinv x, H x, Sinv x, H x, Sinv x]
  | otherwise = [Rz theta x, X x, Rz theta x, X x]
  where (Dy a n) = unpack dy
