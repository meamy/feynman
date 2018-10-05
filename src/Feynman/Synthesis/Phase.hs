module Feynman.Synthesis.Phase where

import Feynman.Core
import Feynman.Algebra.Base

synthesizePhase :: ID -> Angle -> [Primitive]
synthesizePhase x theta@(Continuous _) = [Rz theta x]
synthesizePhase x theta@(Discrete a)
  | a == zero = []
  | a == dyadicUnit 1 1 = [Z x]
  | a == dyadicUnit 1 2 = [S x]
  | a == dyadicUnit 3 2 = [Sinv x]
  | a == dyadicUnit 1 3 = [T x]
  | a == dyadicUnit 3 3 = [Tinv x, Z x]
  | a == dyadicUnit 5 3 = [T x, Z x]
  | a == dyadicUnit 7 3 = [Tinv x]
  | otherwise = [Rz theta x]

globalPhase :: ID -> Angle -> [Primitive]
globalPhase x theta@(Continuous _) = [Rz theta x, X x, Rz theta x, X x]
globalPhase x theta@(Discrete a)
  | a == zero = []
  | a == dyadicUnit 1 1 = [Z x, X x, Z x, X x]
  | a == dyadicUnit 1 2 = [S x, X x, S x, X x]
  | a == dyadicUnit 3 2 = [Sinv x, X x, Sinv x, X x]
  | a == dyadicUnit 1 3 = [H x, S x, H x, S x, H x, S x]
  | a == dyadicUnit 3 3 = [H x, S x, H x, S x, H x, Z x, X x, S x, X x]
  | a == dyadicUnit 5 3 = [H x, S x, H x, S x, H x, Sinv x, X x, Z x, X x]
  | a == dyadicUnit 7 3 = [H x, Sinv x, H x, Sinv x, H x, Sinv x]
  | otherwise = [Rz theta x, X x, Rz theta x, X x]
