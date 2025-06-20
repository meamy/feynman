{-# LANGUAGE Rank2Types #-}

{-|
Module      : Core
Description : Core circuit representations and utilities
Copyright   : (c) 2016--2025 Matthew Amy
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable

This module contains the core data structures, types, and
representations of circuits and programs in Feynman.
-}

module Feynman.Core where

import Data.List
import Control.Monad
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map

import Feynman.Algebra.Base

{- ----------------------------------------------------------------------------- -}

-- * Pervasive types

-- | Variable identifiers
type ID = String

-- | Program locations (e.g. syntax nodes)
type Loc = Int

-- | Angles are either represented as a discrete multiple of 'pi' by
--   a dyadic fraction @a/2^b@ reduced mod 2, or as a real-valued
--   number (the continuous representation)
data Angle = Discrete DMod2 | Continuous Double deriving (Eq, Ord)

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

-- | Applies a numeric unary function to an angle
apply :: (forall a. Num a => a -> a) -> Angle -> Angle
apply f (Discrete a)   = Discrete $ f a
apply f (Continuous a) = Continuous $ f a

-- | Applies a numeric binary function to a pair of angles.
--   If either angle is continuous the result will be continuous
apply2 :: (forall a. Num a => a -> a -> a) -> Angle -> Angle -> Angle
apply2 f a b = case (a,b) of
  (Discrete a, Discrete b)     -> Discrete $ f a b
  (Discrete a, Continuous b)   -> Continuous $ f (toDouble a) b
  (Continuous a, Discrete b)   -> Continuous $ f a (toDouble b)
  (Continuous a, Continuous b) -> Continuous $ f a b
  where toDouble = (pi *) . fromRational . toRational

-- | Discretizes an angle
discretize :: Angle -> DyadicRational
discretize (Discrete a)   = unpack a
discretize (Continuous a) = toDyadic (a/pi)

-- | Constructs a discrete angle of @pi*(a/2^b)@ from a dyadic rational @a/2^b@
dyadicPhase :: DyadicRational -> Angle
dyadicPhase = Discrete . fromDyadic

-- | Constructs a continuous angle from a floating point number
continuousPhase :: Double -> Angle
continuousPhase = Continuous


{- ----------------------------------------------------------------------------- -}

-- * Circuits
--
-- $ Circuits are represented as lists of primitive operations which consist of
--
--     1. gates over Clifford+T and single qubit rotations
--     2. uninterpreted operations which have no defined semantics, and
--     3. non-destructive measurement

-- | Primitive gates & operations
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
  | Measure  ID ID
  -- ^ Measures the first argument in the computational basis and copies into the second
  | Reset    ID
  | Uninterp ID [ID]
  deriving (Eq)

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


-- | Gates annotated with a unique location for the purpose of optimization
type AnnotatedPrimitive = (Primitive, Loc)

-- ** Circuit utilities

-- | Returns the qubits involved in a gate
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

-- | Returns all qubit IDs used in a circuit
ids :: [Primitive] -> [ID]
ids = Set.toList . foldr (Set.union) Set.empty . map (Set.fromList . getArgs)

-- | Returns the adjoint of a primitive gate
daggerGate :: Primitive -> Primitive
daggerGate x = case x of
  H _           -> x
  X _           -> x
  Y _           -> x
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

-- | Returns the adjoint of a circuit
dagger :: [Primitive] -> [Primitive]
dagger = reverse . map daggerGate

-- | Performs a substitution given by a function on a gate application
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

-- | Performs a substitution given by a function on a circuit
subst :: (ID -> ID) -> [Primitive] -> [Primitive]
subst f = map (substGate f)

-- | Count the number of T-gates in a circuit
countT :: [Primitive] -> Int
countT = foldr (+) 0 . map go where
  go (T _) = 1
  go (Tinv _) = 1
  go _     = 0

-- ** Basic transformations

-- | Removes gates which are adjacent to their dagger
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
                  Just (_, uid') -> (foldr Map.delete frontier args,
                                     foldr Set.insert erasures [uid, uid'])
                  Nothing        -> (foldr (\q -> Map.insert q (gate, uid)) frontier args,
                                     erasures)
        in
          filter (\(_, uid) -> not $ Set.member uid erasures) circ
  in
    fst . unzip . (converge simplify) $ circ'

-- | Expands CNOT gates over H and CZ
expandCNOT :: [Primitive] -> [Primitive]
expandCNOT = concatMap go where
  go x = case x of
    CNOT c t      -> [H t, CZ c t, H t]
    _             -> [x]

-- | Expands CZ gates over H and CNOT
expandCZ :: [Primitive] -> [Primitive]
expandCZ = concatMap go where
  go x = case x of
    CZ c t      -> [H t, CNOT c t, H t]
    _           -> [x]

-- | Factors swaps out into an output permutation
factorSwaps :: [Primitive] -> (Map ID ID, [Primitive])
factorSwaps = go (Map.empty, []) where

  get :: Map ID ID -> ID -> ID
  get ctx q               = Map.findWithDefault q q ctx

  go :: (Map ID ID, [Primitive]) -> [Primitive] -> (Map ID ID, [Primitive])
  go (ctx, acc) []        = (ctx, reverse acc)
  go (ctx, acc) (x:xs)    = case x of
    Swap q1 q2 ->
      let (q1', q2') = (get ctx q1, get ctx q2) in
        go (Map.insert q1 q2' $ Map.insert q2 q1' ctx, acc) xs
    gate       -> go (ctx, substGate (get ctx) gate:acc) xs

-- | Synthesizes a qubit permutation
synthesizePermutation :: Map ID ID -> [Primitive]
synthesizePermutation = reverse . synthesize where

  synthesize :: Map ID ID -> [Primitive]
  synthesize ctx = case Map.toList ctx of
    []        -> []
    (q, q'):_ -> synthesizeOrbit q' (Map.delete q ctx)

  synthesizeOrbit :: ID -> Map ID ID -> [Primitive]
  synthesizeOrbit q ctx =
      case ctx Map.!? q of
        Just q' -> (Swap q q'):synthesizeOrbit q' (Map.delete q ctx)
        Nothing -> synthesize ctx
  
-- | Removes swap gates. The resulting circuit is correct only up to permutation of the outputs
removeSwaps :: [Primitive] -> [Primitive]
removeSwaps = snd . factorSwaps

-- | Pushes swap gates to the end
pushSwaps :: [Primitive] -> [Primitive]
pushSwaps = (\(ctx, acc) -> acc ++ synthesizePermutation ctx) . factorSwaps

-- ** Annotated circuits

-- | Annotates a circuit with unique identifiers
annotate :: [Primitive] -> [AnnotatedPrimitive]
annotate = (flip zip) [1..]

-- | Annotates a circuit with a given identifier
annotateWith :: Loc -> [Primitive] -> [AnnotatedPrimitive]
annotateWith l = (flip zip) (repeat l)

-- | Removes all annotations
unannotate :: [AnnotatedPrimitive] -> [Primitive]
unannotate = fst . unzip

-- | Annotated simplification pass
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

-- | Annotated CNOT expansion
expandCNOT' :: [AnnotatedPrimitive] -> [AnnotatedPrimitive]
expandCNOT' = concatMap go where
  go (x,l) = case x of
    CNOT c t      -> [(H t,l), (CZ c t,l), (H t,l)]
    _             -> [(x,l)]

{- ----------------------------------------------------------------------------- -}

-- * Structured circuits
--
-- $ Provides a structured representation for quantum circuits by extending
--   gate lists with subcircuits and simple loops (repeated gates or subcircuits).
--   Coincides with the DotQC program model.
--
--   Structured circuits are represented as lists of declarations, with a
--   distinguished declaration 'main' which is the entrypoint for the program

-- | Valid statements within a structured circuit
data Stmt =
    Gate Primitive
  | Seq [Stmt]
  | Call ID [ID]
  | Repeat Int Stmt

-- | Sub-circuit declarations
data Decl = Decl { name   :: ID,
                   params :: [ID],
                   body   :: Stmt }
 
-- | Top-level representation of structured circuits
data Circuit = Circuit { qubits :: [ID],
                         inputs :: Set ID,
                         decls  :: [Decl] }

instance Show Stmt where
  show (Gate gate)               = show gate
  show (Seq lst)                 = intercalate "\n" (map show lst)
  show (Call id args)            = show id ++ intercalate " " args
  show (Repeat i (Call id args)) = show id ++ "^" ++ show i ++ intercalate " " args
  show (Repeat i stmt)           = "BEGIN^" ++ show i ++ "\n" ++ show stmt ++ "\n" ++ "END"

instance Show Decl where
  show decl = "BEGIN " ++ putName (name decl) ++ intercalate " " (params decl) ++ "\n"
              ++ show (body decl) ++ "\n"
              ++ "END"
    where putName "main" = ""
          putName s      = s

instance Show Circuit where
  show circ = intercalate "\n" (qubitline:inputline:body)
    where qubitline = ".v " ++ intercalate " " (qubits circ)
          inputline = ".i " ++ intercalate " " (filter (`Set.member` inputs circ) (qubits circ))
          body      = map show (decls circ)

{- ----------------------------------------------------------------------------- -}

-- * Non-deterministic WHILE programs
--
-- $ The non-deterministic WHILE language extends primitive circuits with
--   constructs for non-deterministic classical control flow (looping and branching)
--   as well as primitive reset and measure statements. Control-flow paths correspond
--   to regular expressions over a language of quantum actions including gates, reset,
--   and measurement.
--
--   Used as an intermediate language for analysis of programs which involve classical
--   control (non-deterministic or otherwise)

-- | Representation of non-deterministic WHILE programs.
--   Individual statements are annotated with data of type 'a'
data WStmt a =
    WSkip a
  | WGate a Primitive
  | WSeq a [WStmt a]
  | WReset a ID
  | WMeasure a ID
  | WIf a (WStmt a) (WStmt a)
  | WWhile a (WStmt a)
  deriving (Eq)

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

-- | Returns the identifiers used in a program
idsW :: WStmt a -> [ID]
idsW = Set.toList . go where
  go (WSkip _)      = Set.empty
  go (WGate _ g)    = Set.fromList $ ids [g]
  go (WSeq _ xs)    = Set.unions $ map go xs
  go (WReset _ x)   = Set.singleton x
  go (WMeasure _ x) = Set.singleton x
  go (WIf _ s1 s2)  = Set.union (go s1) (go s2)
  go (WWhile _ s)   = go s

-- | Basic inverse cancellation pass
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

{- ----------------------------------------------------------------------------- -}

-- * Misc

-- | Finds the least fixpoint of a function by repeated iteration
converge :: Eq a => (a -> a) -> a -> a
converge f a
  | a' == a   = a'
  | otherwise = converge f a'
  where a' = f a
