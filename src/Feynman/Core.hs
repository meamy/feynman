{-# LANGUAGE Rank2Types, DeriveGeneric #-}
module Feynman.Core where

import Data.List
import Control.Monad
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map

import Control.DeepSeq (NFData)
import GHC.Generics (Generic)

import Feynman.Algebra.Base


type ID = String
type Loc = Int

{- Phase angles -}
-- Phase angles either have the form pi*(a/2^b) reduced mod 2, or theta
data Angle = Discrete DMod2 | Continuous Double deriving (Eq, Ord, Generic)

instance NFData Angle

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
discretize (Discrete a)   = unpack a
discretize (Continuous a) = toDyadic a

-- Phase of pi*(a/2^b) reduced mod 2
dyadicPhase :: DyadicRational -> Angle
dyadicPhase = Discrete . fromDyadic

-- Phase of theta
continuousPhase :: Double -> Angle
continuousPhase = Continuous

instance Show Angle where
  show (Discrete a)
    | a == 0    = show a
    | a == 1    = "pi"
    | otherwise = "pi*" ++ show a
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
  order (Discrete a)   = order a
  order (Continuous _) = 0

{- Circuits -}
data Primitive =
    H        ID
  | X        ID
  | Y        ID
  | Z        ID
  | CNOT     ID ID
  | CZ       ID ID
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

type AnnotatedPrimitive = (Primitive, Loc)

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

{- Flow-agnostic while programs -}

data WStmt a =
    WSkip a
  | WGate a Primitive
  | WSeq a [WStmt a]
  | WReset a ID
  | WMeasure a ID
  | WIf a (WStmt a) (WStmt a)
  | WWhile a (WStmt a)
  deriving (Eq)

{- Utilities -}
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
  CZ x y        -> [x,y]
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
  CZ _ _        -> x
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
  CZ x y        -> CZ (f x) (f y)
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
          CZ x y        -> [x,y]
          S x           -> [x]
          Sinv x        -> [x]
          T x           -> [x]
          Tinv x        -> [x]
          Swap x y      -> [x,y]
          Rz theta x    -> [x]
          Rx theta x    -> [x]
          Ry theta x    -> [x]
          Uninterp s xs -> xs

idsW :: WStmt a -> [ID]
idsW = Set.toList . go where
  go (WSkip _)      = Set.empty
  go (WGate _ g)    = Set.fromList $ ids [g]
  go (WSeq _ xs)    = Set.unions $ map go xs
  go (WReset _ x)   = Set.singleton x
  go (WMeasure _ x) = Set.singleton x
  go (WIf _ s1 s2)  = Set.union (go s1) (go s2)
  go (WWhile _ s)   = go s

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

-- Removes all swap gates by re-indexing
removeSwaps :: [Primitive] -> [Primitive]
removeSwaps = reverse . go (Map.empty, []) where
  get ctx q = Map.findWithDefault q q ctx
  go (ctx, acc) []        = acc
  go (ctx, acc) (x:xs)    = case x of
    Swap q1 q2 ->
      let (q1', q2') = (get ctx q1, get ctx q2) in
        go (Map.insert q1 q2' $ Map.insert q2 q1' ctx, acc) xs
    _          -> go (ctx, (substGate (get ctx) x):acc) xs

expandCNOT :: [Primitive] -> [Primitive]
expandCNOT = concatMap go where
  go x = case x of
    CNOT c t      -> [H t, CZ c t, H t]
    _             -> [x]

expandCZ :: [Primitive] -> [Primitive]
expandCZ = concatMap go where
  go x = case x of
    CZ c t      -> [H t, CNOT c t, H t]
    _           -> [x]

-- Annotated passes

annotate :: [Primitive] -> [AnnotatedPrimitive]
annotate = (flip zip) [1..]

annotateWith :: Loc -> [Primitive] -> [AnnotatedPrimitive]
annotateWith l = (flip zip) (repeat l)

unannotate :: [AnnotatedPrimitive] -> [Primitive]
unannotate = fst . unzip
  
expandCNOT' :: [AnnotatedPrimitive] -> [AnnotatedPrimitive]
expandCNOT' = concatMap go where
  go (x,l) = case x of
    CNOT c t      -> [(H t,l), (CZ c t,l), (H t,l)]
    _             -> [(x,l)]

simplifyPrimitive' :: [AnnotatedPrimitive] -> [AnnotatedPrimitive]
simplifyPrimitive' = converge simplify where
  simplify :: [AnnotatedPrimitive] -> [AnnotatedPrimitive]
  simplify circ =
    let erasures = snd $ foldl' f (Map.empty, Set.empty) $ zip circ [2..]

        allSame xs = foldM (\x y -> if fst x == fst y then Just x else Nothing) (head xs) (tail xs)

        f (last, erasures) ((gate,_), uid) =
          let args     = getArgs gate
              last'    = foldr (\q -> Map.insert q (gate, uid)) last args
              frontier = mapM (\q -> Map.lookup q last) args
              checkDagger (gate', uid')
                | gate' == daggerGate gate = Just (gate', uid')
                | otherwise                = Nothing
          in
            case frontier >>= allSame >>= checkDagger of
              Nothing            -> (last', erasures)
              Just (gate', uid') ->
                (foldr Map.delete last' args, Set.insert uid $ Set.insert uid' erasures)
    in
      fst . unzip . filter (\(_, uid) -> not $ Set.member uid erasures) . zip circ $ [2..]

-- WStmt passes
simplifyWStmt' :: WStmt Loc -> WStmt Loc
simplifyWStmt' = converge simplify where
  simplify wstmt = case wstmt of
    WSkip l      -> WSkip l
    WGate l gate -> WGate l gate
    WSeq l xs    -> case go [] xs of
      []  -> WSkip l
      xs' -> WSeq l xs'
    WReset l v   -> WReset l v
    WMeasure l v -> WMeasure l v
    WIf l s1 s2  -> WIf l (simplify s1) (simplify s2)
    WWhile l s   -> WWhile l (simplify s)

  go gates []     = toGates gates
  go gates (x:xs) = case x of
    WSkip _      -> go gates xs
    WGate l gate -> go (gates ++ [(gate,l)]) xs
    WSeq l xs'   -> go gates (xs' ++ xs)
    _            -> toGates gates ++ [simplify x] ++ go [] xs

  toGates = map (\(g,l) -> WGate l g) . simplifyPrimitive'

-- Builtin circuits

cs :: ID -> ID -> [Primitive]
cs x y = [T x, T y, CNOT x y, Tinv y, CNOT x y]

cz :: ID -> ID -> [Primitive]
cz x y = [S x, S y, CNOT x y, Sinv y, CNOT x y]

ccx :: ID -> ID -> ID -> [Primitive]
ccx x y z = [H z] ++ ccz x y z ++ [H z]

ccz :: ID -> ID -> ID -> [Primitive]
ccz x y z = [T x, T y, T z, CNOT x y, CNOT y z,
             CNOT z x, Tinv x, Tinv y, T z, CNOT y x,
             Tinv x, CNOT y z, CNOT z x, CNOT x y]

-- Printing

instance Show Primitive where
  show (H x)           = "H " ++ x
  show (X x)           = "X " ++ x
  show (Z x)           = "Z " ++ x
  show (Y x)           = "Y " ++ x
  show (CNOT x y)      = "CNOT " ++ x ++ " " ++ y
  show (CZ x y)        = "CZ " ++ x ++ " " ++ y
  show (S x)           = "S " ++ x
  show (Sinv x)        = "S* " ++ x
  show (T x)           = "T " ++ x
  show (Tinv x)        = "T* " ++ x
  show (Swap x y)      = "Swap " ++ x ++ " " ++ y
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

instance Show (WStmt a) where
  show stmt = intercalate "\n" $ go stmt where
    go (WSkip a)      = ["SKIP"]
    go (WGate a gate) = [show gate]
    go (WSeq a xs)    = concatMap go xs
    go (WReset a v)   = ["RESET " ++ v]
    go (WMeasure a v) = ["* <- MEASURE " ++ v]
    go (WIf a s1 s2)  = ["IF * THEN:"] ++ (map ('\t':) $ go s1)
                        ++ ["ELSE:"] ++ (map ('\t':) $ go s2)
    go (WWhile a s)   = ["WHILE *:"] ++ (map ('\t':) $ go s)

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
                                    Gate $ CNOT "y" "z", Gate  $ CNOT "z" "x", Gate $ CNOT "x" "y",
                                    Gate $ H "z" ] }

