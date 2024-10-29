module Feynman.Frontend.OpenQASM.VerificationSyntax where

import Feynman.Algebra.Pathsum.Balanced hiding (Zero)
import Feynman.Algebra.Polynomial.Multilinear
import Feynman.Algebra.Base

data GateSpec = GateSpec {
  k :: Int,
  qubits :: Int,
  sumN :: Int,
  phasePoly :: PolySpec,
  out :: OutputSpec
} deriving (Eq, Show)

type OutputSpec = [BoolSpec]

data BoolSpec =
    BZero
  | BOne
  | BPvar Int
  | BIvar Int
  | BPlus BoolSpec BoolSpec
  | BTimes BoolSpec BoolSpec
  deriving (Eq, Show)

data ScalarSpec =
    Dyadic Int
  | Exponential PolySpec
  deriving (Eq, Show)

data PolySpec =
    Half
  | PPvar Int
  | PIvar Int
  | PPlus PolySpec PolySpec
  | PTimes PolySpec PolySpec
  deriving (Eq, Show)

sopOfSpec :: GateSpec -> Pathsum DMod2
sopOfSpec (GateSpec a b c d e) =
  Pathsum a b b c (polyOfSpec d) (map outputOfSpec e)

polyOfSpec :: PolySpec -> PseudoBoolean Var DMod2
polyOfSpec p =
  case p of 
    Half -> constant half 
    PPvar n -> ofVar $ PVar n
    PIvar n -> ofVar $ IVar n
    PPlus p1 p2 -> (polyOfSpec p1) + (polyOfSpec p2)
    PTimes p1 p2 -> (polyOfSpec p1) * (polyOfSpec p2)

outputOfSpec :: BoolSpec -> SBool Var
outputOfSpec b =
  case b of
    BZero -> 0
    BOne -> 1
    BPvar n -> ofVar $ PVar n
    BIvar n -> ofVar $ IVar n
    BPlus b1 b2 -> (outputOfSpec b1) + (outputOfSpec b2)
    BTimes b1 b2 -> (outputOfSpec b1) * (outputOfSpec b2)

