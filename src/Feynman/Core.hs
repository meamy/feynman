{-# LANGUAGE Rank2Types #-}
module Feynman.Core where

import Feynman.Algebra.Base

import Data.List

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Map (Map)
import qualified Data.Map as Map

import Text.ParserCombinators.Parsec hiding (space)
import Control.Monad

type ID = String
type Loc = Int

{- Phase angles -}
data Angle = Discrete Dyadic | Continuous Double deriving (Eq, Ord)

apply :: (forall a. Num a => a -> a) -> Angle -> Angle
apply f (Discrete a)   = Discrete $ f a
apply f (Continuous a) = Continuous $ f a

apply2 :: (forall a. Num a => a -> a -> a) -> Angle -> Angle -> Angle
apply2 f a b = case (a,b) of
  (Discrete a, Discrete b)     -> Discrete $ f a b
  (Discrete a, Continuous b)   -> Continuous $ f (toDouble a) b
  (Continuous a, Discrete b)   -> Continuous $ f a (toDouble b)
  (Continuous a, Continuous b) -> Continuous $ f a b

instance Show Angle where
  show (Discrete a)   = "2pi*" ++ show a
  show (Continuous a) = show a

instance Num Angle where
  (+)         = apply2 (+)
  (-)         = apply2 (-)
  (*)         = apply2 (*)
  negate      = apply negate
  abs         = apply abs
  signum      = apply signum
  fromInteger = Discrete . fromInteger

instance Abelian Angle where
  zero  = Discrete zero
  pow i = (fromInteger i +)

instance Periodic Angle where
  order (Discrete a)   = order a
  order (Continuous _) = 0

{- Circuits -}
data Primitive =
    H    ID
  | X    ID
  | Y    ID
  | Z    ID
  | CNOT ID ID
  | S    ID
  | Sinv ID
  | T    ID
  | Tinv ID
  | Swap ID ID
  | Rz   Angle ID
  | Rx   Angle ID
  | Ry   Angle ID

data Stmt =
    Gate Primitive
  | Seq [Stmt]
  | Call ID [ID]
  | Repeat Int Stmt
   
data Decl = Decl { name   :: ID,
                   params :: [ID],
                   body   :: Stmt }
 
data Circuit = Circuit { qubits :: [ID],
                         inputs :: Set ID,
                         decls  :: [Decl] }

foldCirc f b c = foldl (foldStmt f . body) b (decls c)

foldStmt f (Seq st)      b = f (Seq st) (foldr (foldStmt f) b st)
foldStmt f (Repeat i st) b = f (Repeat i st) (foldStmt f st b)
foldStmt f s             b = f s b

countGates (Circuit _ _ decls) = foldl' f [0,0,0,0,0,0,0,0] decls
  where plus                   = zipWith (+)
        f cnt (Decl _ _ stmt)  = g cnt stmt
        g cnt (Seq xs)         = foldl' g cnt xs
        g cnt (Call _ _)       = error "Unimplemented call"
        g cnt (Repeat 0 stmt)  = g cnt stmt
        g cnt (Repeat i stmt)  = g (g cnt stmt) (Repeat (i-1) stmt)
        g cnt (Gate gate)      = case gate of
          H _      -> plus cnt [1,0,0,0,0,0,0,0]
          X _      -> plus cnt [0,1,0,0,0,0,0,0]
          Y _      -> plus cnt [0,0,1,0,0,0,0,0]
          Z _      -> plus cnt [0,0,0,1,0,0,0,0]
          CNOT _ _ -> plus cnt [0,0,0,0,1,0,0,0]
          S _      -> plus cnt [0,0,0,0,0,1,0,0]
          Sinv _   -> plus cnt [0,0,0,0,0,1,0,0]
          T _      -> plus cnt [0,0,0,0,0,0,1,0]
          Tinv _   -> plus cnt [0,0,0,0,0,0,1,0]
          Swap _ _ -> plus cnt [0,0,0,0,0,0,0,1]
          Rx _ _   -> plus cnt [0,1,0,0,0,0,0,0]
          Ry _ _   -> plus cnt [0,0,1,0,0,0,0,0]
          Rz _ _   -> plus cnt [0,0,0,1,0,0,0,0]

-- Transformations

daggerGate :: Primitive -> Primitive
daggerGate x = case x of
  H _      -> x
  X _      -> x
  Y _      -> x -- WARNING: this is incorrect
  Z _      -> x
  CNOT _ _ -> x
  S x      -> Sinv x
  Sinv x   -> S x
  T x      -> Tinv x
  Tinv x   -> T x
  Swap _ _ -> x

dagger :: [Primitive] -> [Primitive]
dagger = reverse . map daggerGate

substGate :: Map ID ID -> Primitive -> Primitive
substGate sub gate = case gate of
  H x      -> H $ f x
  X x      -> H $ f x
  Y x      -> Y $ f x
  Z x      -> Z $ f x
  CNOT x y -> CNOT (f x) (f y)
  S x      -> S $ f x
  Sinv x   -> Sinv $ f x
  T x      -> T $ f x
  Tinv x   -> Tinv $ f x
  Swap x y -> Swap (f x) (f y)
  where f x = Map.findWithDefault x x sub

subst :: Map ID ID -> [Primitive] -> [Primitive]
subst sub = map (substGate sub)

-- Builtin circuits

ccz :: ID -> ID -> ID -> [Primitive]
ccz x y z = [T x, T y, T z, CNOT x y, CNOT y z,
             CNOT z x, Tinv x, Tinv y, T z, CNOT y x,
             Tinv x, CNOT y z, CNOT z x, CNOT x y]

cz  :: ID -> ID -> [Primitive]
cz x y = [S x, S y, CNOT x y, Sinv y, CNOT x y]

-- Printing

instance Show Primitive where
  show (H x)      = "H " ++ x
  show (X x)      = "X " ++ x
  show (Z x)      = "Z " ++ x
  show (Y x)      = "Y " ++ x
  show (CNOT x y) = "tof " ++ x ++ " " ++ y
  show (S x)      = "S " ++ x
  show (Sinv x)   = "S* " ++ x
  show (T x)      = "T " ++ x
  show (Tinv x)   = "T* " ++ x
  show (Swap x y) = "swap " ++ x ++ " " ++ y

instance Show Stmt where
  show (Gate gate)               = show gate
  show (Seq lst)                 = intercalate "\n" (map show lst)
  show (Call id args)            = show id ++ showLst args
  show (Repeat i (Call id args)) = show id ++ "^" ++ show i ++ showLst args
  show (Repeat i stmt)           = "BEGIN^" ++ show i ++ "\n" ++ show stmt ++ "\n" ++ "END"

instance Show Decl where
  show decl = "BEGIN " ++ putName (name decl) ++ showLst (params decl) ++ "\n" ++ show (body decl) ++ "\n" ++ "END"
    where putName "main" = ""
          putName s      = s

instance Show Circuit where
  show circ = intercalate "\n" (qubitline:inputline:body)
    where qubitline = ".v " ++ showLst (qubits circ)
          inputline = ".i " ++ showLst (filter (`Set.member` inputs circ) (qubits circ))
          body      = map show (decls circ)

showLst = intercalate " "

-- Test

toffoli = Circuit { qubits = ["x", "y", "z"],
                    inputs = Set.fromList ["x", "y", "z"],
                    decls  = [tof] }
    where tof = Decl { name = "main",
                       params = [],
                       body = Seq [ Gate $ H "z",
                                    Gate $ T "x", Gate $ T "y", Gate $ T "z", 
                                    Gate $ CNOT "x" "y", Gate $ CNOT "y" "z", Gate $ CNOT "z" "x",
                                    Gate $ Tinv "x", Gate $ Tinv "y", Gate $ T "z",
                                    Gate $ CNOT "y" "x",
                                    Gate $ Tinv "x",
                                    Gate $ CNOT "y" "z", Gate  $CNOT "z" "x", Gate $ CNOT "x" "y",
                                    Gate $ H "z" ] }

