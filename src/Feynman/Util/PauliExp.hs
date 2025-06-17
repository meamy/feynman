{-|
Module      : Feynman.Util.PauliExp
Description : Pauli exponential representation
Copyright   : (c) Matthew Amy, 2025
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Feynman.Util.PauliExp where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Map.Merge.Lazy

import Data.Bits

import Feynman.Core
import Feynman.Algebra.Base hiding (Z4)

{----------------------------
 Pauli gates with phase
 ----------------------------}

-- | Pauli gates
data PauliOp = PauliI | PauliX | PauliZ | PauliY deriving (Eq, Ord, Show)
newtype Z4   = Z4 Int deriving (Eq, Ord, Show)
data Pauli   = Pauli Z4 (Map ID PauliOp) deriving (Eq, Ord, Show)

instance Num Z4 where
  (Z4 a) + (Z4 b) = Z4 $ (a + b) `mod` 4
  (Z4 a) - (Z4 b) = Z4 $ (a - b) `mod` 4
  (Z4 a) * (Z4 b) = Z4 $ (a + b) `mod` 4
  negate (Z4 a)   = Z4 $ 4 - a
  abs a           = a
  signum a        = a
  fromInteger a   = Z4 . fromInteger $ a `mod` 4

-- Matrix product order
instance Semigroup Pauli where
  (Pauli r p) <> (Pauli s q) = Pauli phase pauli where

    (phase, pauli) = Map.mapAccum go (r + s) $ Map.unionWith addP (Map.map inj p) (Map.map inj q)

    go acc (r, p) = (acc + r, p)

    inj g = (0, g)

    addP (r, p) (s, q) = (r + s + t, p') where
      (t, p') = case (p, q) of
        (PauliI, p)      -> (0, p)
        (p, PauliI)      -> (0, p)
        (PauliX, PauliX) -> (0, PauliI)
        (PauliX, PauliZ) -> (3, PauliY)
        (PauliX, PauliY) -> (1, PauliZ)
        (PauliZ, PauliX) -> (1, PauliY)
        (PauliZ, PauliZ) -> (0, PauliI)
        (PauliZ, PauliY) -> (3, PauliX)
        (PauliY, PauliX) -> (3, PauliZ)
        (PauliY, PauliZ) -> (1, PauliX)
        (PauliY, PauliY) -> (0, PauliI)

instance Monoid Pauli where
  mempty = Pauli 0 Map.empty

-- | Projects a pauli to the X part
pauliProjX :: PauliOp -> PauliOp
pauliProjX pauli = case pauli of
  PauliI -> PauliI
  PauliX -> PauliX
  PauliZ -> PauliI
  PauliY -> PauliX

-- | Projects a pauli to the Z part
pauliProjZ :: PauliOp -> PauliOp
pauliProjZ pauli = case pauli of
  PauliI -> PauliI
  PauliX -> PauliI
  PauliZ -> PauliZ
  PauliY -> PauliZ

-- | Projects a pauli to the Y part
pauliProjY :: PauliOp -> PauliOp
pauliProjY pauli = case pauli of
  PauliI -> PauliI
  PauliX -> PauliI
  PauliZ -> PauliI
  PauliY -> PauliY

-- | Maps a pauli gate to its X, Y, and Z strings
unzipPauli :: [PauliOp] -> ([PauliOp], [PauliOp], [PauliOp])
unzipPauli pauli = (map pauliProjX pauli, map pauliProjY pauli, map pauliProjZ pauli)

-- | Gets the phase of a Pauli
pauliPhase :: Pauli -> Z4
pauliPhase (Pauli phase _) = phase

-- | Unfolds a Pauli to a list of Pauli operators
pauliOps :: Pauli -> [(ID, PauliOp)]
pauliOps (Pauli _ pauli) = Map.toList pauli

-- | Checks whether two Paulis commute
commute :: Pauli -> Pauli -> Bool
commute (Pauli _ p) (Pauli _ q) = not . foldr xor False $ merge g1 g2 f p q where
  g1 = dropMissing
  g2 = dropMissing
  f  = zipWithMatched (\_ x y -> x /= y)

{----------------------------
 Clifford gates
 ----------------------------}

newtype Clifford = Clifford (Map (ID, PauliOp) Pauli) deriving (Eq, Ord, Show)

-- Matrix product order
instance Semigroup Clifford where
  (Clifford a) <> (Clifford b) = Clifford $ Map.union (Map.map (conj $ Clifford a) b) a

instance Monoid Clifford where
  mempty = Clifford $ Map.empty

-- | Computes a tableau from a Clifford circuit
toClifford :: [Primitive] -> Clifford
toClifford = foldl (flip (<>)) mempty . map gateToClifford where
  gateToClifford gate = Clifford $ case gate of

    X x      -> Map.fromList [((x, PauliZ), Pauli 2 $ Map.fromList [(x, PauliZ)]),
                              ((x, PauliY), Pauli 2 $ Map.fromList [(x, PauliY)])]

    Z x      -> Map.fromList [((x, PauliX), Pauli 2 $ Map.fromList [(x, PauliX)]),
                              ((x, PauliY), Pauli 2 $ Map.fromList [(x, PauliY)])]

    Y x      -> Map.fromList [((x, PauliX), Pauli 2 $ Map.fromList [(x, PauliX)]),
                              ((x, PauliZ), Pauli 2 $ Map.fromList [(x, PauliZ)])]

    H x      -> Map.fromList [((x, PauliX), Pauli 0 $ Map.fromList [(x, PauliZ)]),
                              ((x, PauliZ), Pauli 0 $ Map.fromList [(x, PauliX)]),
                              ((x, PauliY), Pauli 2 $ Map.fromList [(x, PauliY)])]

    S x      -> Map.fromList [((x, PauliX), Pauli 0 $ Map.fromList [(x, PauliY)]),
                              ((x, PauliY), Pauli 2 $ Map.fromList [(x, PauliX)])]

    Sinv x   -> Map.fromList [((x, PauliX), Pauli 2 $ Map.fromList [(x, PauliY)]),
                              ((x, PauliY), Pauli 0 $ Map.fromList [(x, PauliX)])]

    CNOT x y -> Map.fromList [((x, PauliX), Pauli 0 $ Map.fromList [(x, PauliX), (y, PauliX)]),
                              ((x, PauliY), Pauli 0 $ Map.fromList [(x, PauliY), (y, PauliX)]),
                              ((y, PauliY), Pauli 0 $ Map.fromList [(x, PauliZ), (y, PauliY)]),
                              ((y, PauliZ), Pauli 0 $ Map.fromList [(x, PauliZ), (y, PauliZ)])]

    CZ x y   -> Map.fromList [((x, PauliX), Pauli 0 $ Map.fromList [(x, PauliX), (y, PauliZ)]),
                              ((x, PauliY), Pauli 0 $ Map.fromList [(x, PauliY), (y, PauliZ)]),
                              ((y, PauliX), Pauli 0 $ Map.fromList [(x, PauliZ), (y, PauliX)]),
                              ((y, PauliY), Pauli 0 $ Map.fromList [(x, PauliZ), (y, PauliY)])]

    Swap x y -> Map.fromList [((x, PauliX), Pauli 0 $ Map.fromList [(y, PauliX)]),
                              ((x, PauliY), Pauli 0 $ Map.fromList [(y, PauliY)]),
                              ((x, PauliZ), Pauli 0 $ Map.fromList [(y, PauliZ)]),
                              ((y, PauliX), Pauli 0 $ Map.fromList [(x, PauliX)]),
                              ((y, PauliY), Pauli 0 $ Map.fromList [(x, PauliY)]),
                              ((y, PauliZ), Pauli 0 $ Map.fromList [(x, PauliZ)])]

    _ -> error "Not a Clifford circuit"

-- | Conjugates a Pauli P by a Clifford C as C^\dagger P C
conj :: Clifford -> Pauli -> Pauli
conj (Clifford c) (Pauli phase gates) = foldl (<>) pzero . map conjP $ pauliOps where
  pzero         = Pauli phase Map.empty
  pauliOps      = Map.toList gates
  conjP pauliOp = Map.findWithDefault (Pauli 0 $ Map.fromList [pauliOp]) pauliOp c

{----------------------------
 Pauli exponentials
 ----------------------------}

-- | Pauli exponentials with angles of type /a/
data PauliExp a = PauliExp a Pauli deriving (Eq, Ord, Show)

-- | Compute the Pauli exponential representation of a Primitive circuit
toPauliExp :: [Primitive] -> ([PauliExp Angle], Clifford)
toPauliExp = foldl go ([], mempty) where

  go (rp, cliff) g = case g of
    T    x -> let pauli = conj cliff (Pauli 0 $ Map.fromList [(x, PauliZ)]) in
      (rp ++ [PauliExp (dyadicPhase $ dyadic 2 1) pauli], cliff)
    Tinv x -> let pauli = conj cliff (Pauli 0 $ Map.fromList [(x, PauliZ)]) in
      (rp ++ [PauliExp (dyadicPhase $ dyadic 2 7) pauli], cliff)
    _      -> (rp, toClifford [g] <> cliff)


