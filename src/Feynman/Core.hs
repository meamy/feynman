{-# LANGUAGE Rank2Types #-}
module Feynman.Core where

import Feynman.Algebra.Base

import Data.List

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Map (Map)
import qualified Data.Map as Map

type ID = String
type Loc = Int

{- Phase angles -}
data Angle = Discrete DyadicRational | Continuous Double deriving (Eq, Ord)

apply :: (forall a. Num a => a -> a) -> Angle -> Angle
apply f (Discrete a)   = Discrete $ f a
apply f (Continuous a) = Continuous $ f a

apply2 :: (forall a. Num a => a -> a -> a) -> Angle -> Angle -> Angle
apply2 f a b = case (a,b) of
  (Discrete a, Discrete b)     -> Discrete $ f a b
  (Discrete a, Continuous b)   -> Continuous $ f (toDouble a) b
  (Continuous a, Discrete b)   -> Continuous $ f a (toDouble b)
  (Continuous a, Continuous b) -> Continuous $ f a b
  where toDouble = fromRational . toRational

discretize :: Angle -> DyadicRational
discretize (Discrete a)   = a
discretize (Continuous a) = toDyadic a

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
  power i (Discrete a)   = Discrete $ power i a
  power i (Continuous a) = Continuous $ (fromInteger i) * a

instance Periodic Angle where
  order (Discrete a)   = order . (fromDyadic :: DyadicRational -> DMod2) $ power 2 a
  order (Continuous _) = 0

{- Circuits -}
data Primitive =
    H        ID
  | X        ID
  | Y        ID
  | Z        ID
  | CNOT     ID ID
  | S        ID
  | Sinv     ID
  | T        ID
  | Tinv     ID
  | Swap     ID ID
  | Rz       Angle ID
  | Rx       Angle ID
  | Ry       Angle ID
  | Uninterp ID [ID]
  deriving (Eq)

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

getArgs :: Primitive -> [ID]
getArgs gate = case gate of
  H x           -> [x]
  X x           -> [x]
  Y x           -> [x]
  Z x           -> [x]
  CNOT x y      -> [x,y]
  S x           -> [x]
  Sinv x        -> [x]
  T x           -> [x]
  Tinv x        -> [x]
  Swap x y      -> [x,y]
  Rz theta x    -> [x]
  Rx theta x    -> [x]
  Ry theta x    -> [x]
  Uninterp s xs -> xs

-- Transformations

daggerGate :: Primitive -> Primitive
daggerGate x = case x of
  H _           -> x
  X _           -> x
  Y _           -> x -- WARNING: this is incorrect
  Z _           -> x
  CNOT _ _      -> x
  S x           -> Sinv x
  Sinv x        -> S x
  T x           -> Tinv x
  Tinv x        -> T x
  Swap _ _      -> x
  Rz theta x    -> Rz (-theta) x
  Rx theta x    -> Rx (-theta) x
  Ry theta x    -> Ry (-theta) x
  Uninterp s xs -> Uninterp (s ++ "*") xs

dagger :: [Primitive] -> [Primitive]
dagger = reverse . map daggerGate

substGate :: (ID -> ID) -> Primitive -> Primitive
substGate f gate = case gate of
  H x           -> H $ f x
  X x           -> X $ f x
  Y x           -> Y $ f x
  Z x           -> Z $ f x
  CNOT x y      -> CNOT (f x) (f y)
  S x           -> S $ f x
  Sinv x        -> Sinv $ f x
  T x           -> T $ f x
  Tinv x        -> Tinv $ f x
  Swap x y      -> Swap (f x) (f y)
  Rz theta x    -> Rz theta (f x)
  Rx theta x    -> Rx theta (f x)
  Ry theta x    -> Ry theta (f x)
  Uninterp s xs -> Uninterp s (map f xs)

subst :: (ID -> ID) -> [Primitive] -> [Primitive]
subst f = map (substGate f)

ids :: [Primitive] -> [ID]
ids = Set.toList . foldr f Set.empty
  where f gate set   = foldr Set.insert set (idsGate gate)
        idsGate gate = case gate of
          H x           -> [x]
          X x           -> [x]
          Y x           -> [x]
          Z x           -> [x]
          CNOT x y      -> [x,y]
          S x           -> [x]
          Sinv x        -> [x]
          T x           -> [x]
          Tinv x        -> [x]
          Swap x y      -> [x,y]
          Rz theta x    -> [x]
          Rx theta x    -> [x]
          Ry theta x    -> [x]
          Uninterp s xs -> xs

converge :: Eq a => (a -> a) -> a -> a
converge f a
  | a' == a   = a'
  | otherwise = converge f a'
  where a' = f a

simplifyPrimitive :: [Primitive] -> [Primitive]
simplifyPrimitive circ =
  let circ'         = zip circ [0..]
      simplify circ =
        let erasures = snd $ foldl' f (Map.empty, Set.empty) circ
            f (frontier, erasures) (gate, uid) =
              let args@(x:xs) = getArgs gate
                  checkDagger (gate', uid')
                    | gate' == daggerGate gate = Just (gate, uid')
                    | otherwise                = Nothing
                  checkArg (gate, uid) q = do
                    (_, uid') <- Map.lookup q frontier
                    if uid' == uid then Just (gate, uid) else Nothing
              in
                case Map.lookup x frontier >>= checkDagger >>= (\g -> foldM checkArg g xs) of
                  Just (_, uid') -> (foldr Map.delete frontier args, foldr Set.insert erasures [uid, uid'])
                  Nothing        -> (foldr (\q -> Map.insert q (gate, uid)) frontier args, erasures)
        in
          filter (\(_, uid) -> not $ Set.member uid erasures) circ
  in
    fst . unzip . (converge simplify) $ circ'

-- Builtin circuits

ccx :: ID -> ID -> ID -> [Primitive]
ccx x y z = [H z] ++ ccz x y z ++ [H z]

ccz :: ID -> ID -> ID -> [Primitive]
ccz x y z = [T x, T y, T z, CNOT x y, CNOT y z,
             CNOT z x, Tinv x, Tinv y, T z, CNOT y x,
             Tinv x, CNOT y z, CNOT z x, CNOT x y]

cz  :: ID -> ID -> [Primitive]
cz x y = [S x, S y, CNOT x y, Sinv y, CNOT x y]

-- Printing

instance Show Primitive where
  show (H x)           = "H " ++ x
  show (X x)           = "X " ++ x
  show (Z x)           = "Z " ++ x
  show (Y x)           = "Y " ++ x
  show (CNOT x y)      = "tof " ++ x ++ " " ++ y
  show (S x)           = "S " ++ x
  show (Sinv x)        = "S* " ++ x
  show (T x)           = "T " ++ x
  show (Tinv x)        = "T* " ++ x
  show (Swap x y)      = "swap " ++ x ++ " " ++ y
  show (Rz theta x)    = "Rz(" ++ show theta ++ ") " ++ x
  show (Rx theta x)    = "Rx(" ++ show theta ++ ") " ++ x
  show (Ry theta x)    = "Ry(" ++ show theta ++ ") " ++ x
  show (Uninterp s xs) = s ++ concatMap (" " ++) xs

instance Show Stmt where
  show (Gate gate)               = show gate
  show (Seq lst)                 = intercalate "\n" (map show lst)
  show (Call id args)            = show id ++ showLst args
  show (Repeat i (Call id args)) = show id ++ "^" ++ show i ++ showLst args
  show (Repeat i stmt)           = "BEGIN^" ++ show i ++ "\n" ++ show stmt ++ "\n" ++ "END"

instance Show Decl where
  show decl = "BEGIN " ++ putName (name decl) ++ showLst (params decl) ++ "\n"
              ++ show (body decl) ++ "\n"
              ++ "END"
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

