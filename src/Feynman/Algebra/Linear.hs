{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE BangPatterns #-}

{-|
Module      : Linear
Description : Linear algebra over the binary field
Copyright   : (c) 2016--2025 Matthew Amy
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable

This module provides vectors and matrices over the binary field
\(\mathbb{F}_2\), together with row reduction, rank, pseudoinverse, and
linear-system routines.
-}

module Feynman.Algebra.Linear where

import Feynman.Algebra.Matroid

import Data.List hiding (transpose)
--import Data.Tuple
import Control.Monad
import Control.Monad.Writer

import Data.Map (Map, (!))
import qualified Data.Map as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Coerce

import Data.Bits
import qualified Data.BitVector as BitVector

import Test.QuickCheck hiding ((.&.))

{- ----------------------------------------------------------------------------- -}

-- * Binary vectors
--
-- Vectors are represented by packed, fixed-width bit vectors. Bit @i@ is the
-- coefficient of the @i@th standard basis vector. The 'Show' instance prints
-- vectors in little-endian order, so the character at the left is bit @0@.
--
-- The 'Num' instance implements the algebra of \(\mathbb{F}_2^n\): addition
-- and subtraction are exclusive or, negation is the identity, and
-- multiplication is component-wise conjunction. 'fromInteger' creates a
-- width-32 vector.

-- ** Representation

-- | A packed vector over \(\mathbb{F}_2\).
--
-- The width is part of the underlying bit-vector representation. Arithmetic
-- treats @(+)@ and @(-)@ as exclusive or, and @(\*)@ as bitwise conjunction.
newtype F2Vec = F2Vec { getBV :: BitVector.BV } deriving (Eq, Ord, Bits)

instance Show F2Vec where
  show v = map (f . (v @.)) [0..width v - 1]
    where f b = if b then '1' else '0'

instance Num F2Vec where
  (+)         = xor
  (*)         = (.&.)
  (-)         = xor
  negate      = id
  abs         = id
  signum      = id
  fromInteger = bitVec 32

instance Matroid F2Vec where
  independent s = (Set.size s) == (rank $ fromList $ Set.toList s)

-- ** Construction and conversion

-- | Constructs a vector of the given width from the low-order bits of an
-- integral value.
bitVec :: Integral a => Int -> a -> F2Vec
bitVec n i = coerce $ BitVector.bitVec n i

-- | Constructs a width-@n@ standard basis vector with bit @i@ set.
bitI :: Int -> Int -> F2Vec
bitI n i = coerce $ BitVector.bitVec n (shift 1 i :: Integer)

-- | Constructs a vector whose bits are all set.
ones :: Int -> F2Vec
ones = coerce $ BitVector.ones

-- | Tests the bit at a zero-based index.
(@.) :: Integral a => F2Vec -> a -> Bool
(@.) v i = coerce $ (BitVector.@.) (coerce v) i

-- | Extracts an inclusive range of bits @(high, low)@.
(@@) :: Integral a => F2Vec -> (a, a) -> F2Vec
(@@) v (i, j) = coerce $ (BitVector.@@) (coerce v) (i, j)

-- | Extends a vector on the high-order end with the given number of zero bits.
zeroExtend :: Integral a => a -> F2Vec -> F2Vec
zeroExtend i v = coerce $ BitVector.zeroExtend i (coerce v)

-- | Returns the fixed width of a vector.
width :: F2Vec -> Int
width = coerce BitVector.width

-- | Packs a list of bits into a vector.
fromBits :: [Bool] -> F2Vec
fromBits = coerce BitVector.fromBits

-- | Unpacks a vector into a list of bits.
toBits :: F2Vec -> [Bool]
toBits = coerce BitVector.toBits

-- | Concatenates two vectors.
append :: F2Vec -> F2Vec -> F2Vec
append = coerce BitVector.append

-- | Concatenates a list of vectors.
appends :: [F2Vec] -> F2Vec
appends = coerce BitVector.concat

-- | Returns the index of the least-significant set bit.
lsb1 :: F2Vec -> Int
lsb1 = coerce BitVector.lsb1

-- | Reverses the order of the bits in a vector.
mirror :: F2Vec -> F2Vec
mirror = coerce BitVector.reverse

-- ** Enumeration and weight

-- | Enumerates all vectors of the given width.
allVecs :: Int -> [F2Vec]
allVecs n = map (bitVec n) [0..2^n-1]

-- | Returns the Hamming weight of a vector.
wt :: F2Vec -> Int
wt = popCount

-- | Returns a vector of minimum Hamming weight, choosing the second argument
-- in case of a tie.
minWt :: F2Vec -> F2Vec -> F2Vec
minWt u v = if wt u < wt v then u else v

{- ----------------------------------------------------------------------------- -}

-- * Binary matrices
--
-- Matrices are stored in row-major order. An @m@-by-@n@ matrix contains @m@
-- vectors of width @n@ in its 'vals' field. The dimensions are stored
-- explicitly, which allows a matrix to retain its column count when it has no
-- rows.

-- ** Representation

-- | A row-major matrix over \(\mathbb{F}_2\).
--
-- An @'F2Mat' m n rows@ represents an @m@-by-@n@ matrix. The list must contain
-- exactly @m@ vectors and every vector must have width @n@. Construction with
-- 'F2Mat' does not check this invariant; prefer the constructors below when
-- possible.
data F2Mat = F2Mat {
  m :: Int,       -- ^ Number of rows.
  n :: Int,       -- ^ Number of columns.
  vals :: [F2Vec] -- ^ Matrix rows, in increasing row-index order.
  } deriving (Eq)

instance Show F2Mat where
  show (F2Mat m n vals) = intercalate "\n" $ map show vals

-- ** Construction and conversion
--
-- 'fromList' is the usual checked constructor. 'fromListSafe' additionally
-- accepts rows of differing widths and pads them on the high-order end.

-- | Constructs the identity matrix of the given dimension.
identity :: Int -> F2Mat
identity n = F2Mat n n $ map (\i -> shift (bitVec n 1) i) [0..n-1]

-- | Resizes a matrix, truncating high-index rows or columns and padding new
-- entries with zeroes.
resizeMat :: Int -> Int -> F2Mat -> F2Mat
resizeMat m' n' (F2Mat m n vals) = F2Mat m' n' vals'
  where vals' = (map f $ take m' vals) ++ (replicate (m'-m) $ bitVec n' 0)
        f     = if n' > n
                then zeroExtend (n'-n)
                else (flip (@@)) (n'-1, 0) 

-- | Returns the rows of a matrix.
toList :: F2Mat -> [F2Vec]
toList (F2Mat m n vals) = vals

-- | Constructs a matrix from equally sized row vectors.
--
-- The empty list produces the @0@-by-@0@ matrix. An error is raised when row
-- widths differ.
fromList :: [F2Vec] -> F2Mat
fromList []   = F2Mat 0 0 []
fromList vecs@(x:xs) =
  if all ((n ==) . width) xs
    then F2Mat (length vecs) n vecs
    else error "Vectors have differing lengths"
  where n = width x

-- | Constructs a matrix after zero-extending every row to the width of the
-- widest row.
fromListSafe :: [F2Vec] -> F2Mat
fromListSafe xs = fromList (map go xs) where
  go bv = if width bv < n then zeroExtend (n - width bv) bv else bv
  n     = maximum $ map width xs

-- | Treats a vector as a one-row matrix.
fromVec :: F2Vec -> F2Mat
fromVec x = F2Mat 1 n [x]
  where n = width x

-- ** Indexing
--
-- Rows and columns use zero-based indices. Out-of-range indices result in an
-- error.

-- | Returns a row by its zero-based index.
row :: F2Mat -> Int -> F2Vec
row (F2Mat m n vals) i
  | 0 <= i && i < m = vals !! i
  | otherwise       = error "Row index out of bounds"

-- | Returns the entry at the given zero-based row and column indices.
index :: F2Mat -> Int -> Int -> Bool
index mat@(F2Mat m n vals) i j
  | 0 <= j && j < n = (row mat i) @. j
  | otherwise       = error "Column index out of bounds"

-- ** Basic linear algebra
--
-- Matrices supplied to binary operations must have compatible dimensions;
-- incompatible dimensions result in an error.

-- | Transposes a matrix.
--
-- This operation reconstructs every row of the result and is relatively
-- expensive compared with row-wise operations.
transpose :: F2Mat -> F2Mat
transpose (F2Mat m n vals) = F2Mat n m vals'
  where vals'    = map f [0..n-1]
        f j      = fromBits $ foldl' (g j) [] vals
        g j xs v = (v @. j):xs

-- | Forms a change-of-coordinates matrix by treating the supplied vectors as
-- columns.
coc :: [F2Vec] -> F2Mat
coc = transpose . fromList

-- | Multiplies two row-major matrices.
mult :: F2Mat -> F2Mat -> F2Mat
mult a@(F2Mat am an avals) b@(F2Mat bm bn bvals)
  | an /= bm  = error $ "Incompatible matrix dimensions:\n" ++ show a ++ "\n\n" ++ show b ++ "\n"
  | otherwise = F2Mat am bn $ map multRow avals
    where multRow v       = foldl' (f v) (bitVec bn 0) $ zip bvals [0..]
          f v sum (v', i) = if  v @. i then sum + v' else sum

-- | Multiplies matrices supplied in column-major order.
--
-- This is 'mult' with its arguments reversed: @multT a b = mult b a@.
multT :: F2Mat -> F2Mat -> F2Mat
multT a b = mult b a

-- | Right-multiplies a row vector by a matrix.
multRow :: F2Vec -> F2Mat -> F2Vec
multRow v = head . toList . mult (fromVec v)

-- | Left-multiplies a column vector by a matrix.
multVec :: F2Mat -> F2Vec -> F2Vec
multVec m = head . toList . multT (transpose m) . fromVec

-- | Adds two matrices entrywise.
add :: F2Mat -> F2Mat -> F2Mat
add a@(F2Mat am an avals) b@(F2Mat bm bn bvals)
  | am /= bm || an /= bn = error "Incompatible matrix dimensions"
  | otherwise = F2Mat am an $ zipWith (+) avals bvals

{- ----------------------------------------------------------------------------- -}

-- * Elementary row operations
--
-- Row operations act on zero-based row indices. A list of operations is
-- interpreted from left to right by 'applyROps'. Transposition reverses the
-- list and exchanges the source and target of each row addition.

-- | An elementary row operation.
--
-- @Exchange i j@ swaps rows @i@ and @j@. @Add i j@ adds row @i@ into row
-- @j@ over \(\mathbb{F}_2\).
data ROp = Exchange Int Int | Add Int Int deriving (Eq, Show)

-- | Removes all-zero rows without changing the recorded column count.
removeZeroRows :: F2Mat -> F2Mat
removeZeroRows a@(F2Mat _ n vals) = 
  a { vals = filter (bitVec n 0 /=) vals }

-- | Swaps two rows.
swapRow :: Int -> Int -> F2Mat -> F2Mat
swapRow i j mat@(F2Mat m n vals)
  | i > j           = swapRow j i mat
  | 0 > i || j >= m = error "SwapRow indices out of bounds"
  | i == j          = mat
  | otherwise       =
    let (v1, v') = splitAt i vals
        (v2, v3) = splitAt (j-i) v'
    in
      mat { vals = v1 ++ (head v3):(tail v2) ++ (head v2):(tail v3) }

-- | Adds the first indexed row into the second indexed row.
addRow :: Int -> Int -> F2Mat -> F2Mat
addRow i j mat@(F2Mat m n vals)
  | 0 <= i && 0 <= j && i < m && j < m =
    let (v1, v2) = splitAt j vals
        newV     = (head v2) + (vals !! i)
    in
      mat { vals = v1 ++ newV:(tail v2) }
  | otherwise                          = error "Add indices out of bounds"

-- | Applies one elementary row operation.
applyROp :: ROp -> F2Mat -> F2Mat
applyROp (Exchange i j) = swapRow i j
applyROp (Add  i j) = addRow  i j

-- | Applies elementary row operations from left to right.
applyROps :: F2Mat -> [ROp] -> F2Mat
applyROps = foldl' (flip applyROp) 

-- | Transposes the elementary matrix represented by a row operation.
transposeROp :: ROp -> ROp
transposeROp (Exchange i j) = Exchange j i
transposeROp (Add  i j) = Add  j i

-- | Transposes a sequence of row operations, reversing its order.
transposeROps :: [ROp] -> [ROp]
transposeROps = foldl' (\acc rop -> (transposeROp rop):acc) []

-- | Reorders a sequence so additions are performed before exchanges where
-- possible, adjusting row indices to preserve its action.
moveAddsIn :: [ROp] -> [ROp]
moveAddsIn xs =
  let move sx []     = reverse sx
      move sx (x:xs) = case x of
        Exchange _ _ -> move (x:sx) xs
        Add  _ _ -> move (toLeft x sx) xs
      toLeft y [] = [y]
      toLeft y (x:xs) = case x of
        Exchange _ _ -> x:toLeft (apply x y) xs
        Add  _ _ -> y:x:xs
      apply (Exchange i j) (Add l k) =
        let sw x = if x == i then j else if x == j then i else x in
          Add (sw l) (sw k)
  in
    move [] xs

-- | Reorders a sequence so exchanges are performed before additions where
-- possible, adjusting row indices to preserve its action.
moveSwapsIn :: [ROp] -> [ROp]
moveSwapsIn xs =
  let move sx []     = reverse sx
      move sx (x:xs) = case x of
        Add  _ _ -> move (x:sx) xs
        Exchange _ _ -> move (toLeft x sx) xs
      toLeft y [] = [y]
      toLeft y (x:xs) = case x of
        Add  _ _ -> (apply y x):toLeft y xs
        Exchange _ _ -> y:x:xs
      apply (Exchange i j) (Add l k) =
        let sw x = if x == i then j else if x == j then i else x in
          Add (sw l) (sw k)
  in
    move [] xs

-- | Applies only the exchanges in a sequence of row operations to an index.
permute :: Int -> [ROp] -> Int
permute =
  let permuteROp i (Exchange j k)
        | i == j     = k
        | i == k     = j
      permuteROp i _ = i
  in
    foldl permuteROp 

{- ----------------------------------------------------------------------------- -}

-- * Gaussian elimination
--
-- Elimination routines return their elementary row operations through
-- 'Writer'. Applying the recorded operations to the original matrix, in the
-- order returned, reproduces the resulting echelon form. Zero rows are
-- retained unless a function explicitly states otherwise.

-- ** Standard elimination

{-
toUpperEchelon :: F2Mat -> Writer F2Mat [ROp]
toUpperEchelon mat@(F2Mat m n vals) =
  let returnFirstNonzero i j mat
        | i >= m    = Nothing
        | otherwise =
          if index mat i j
          then Just i
          else returnFirstNonzero (i+1) j mat
      zeroAll i j mat =
        let zeroRow (mat, xs) i' =
              if i /= i' && index mat i' j
              then (\(m, p) -> (m, p:xs)) $ addRow mat i i'
              else (mat, xs)
        in
         foldl zeroRow (mat, []) [0..m-1]
      toUpper i j mat
        | (i >= m) || (j >= n) = return mat
        | otherwise =
          case returnFirstNonzero i j mat of
            Nothing -> toUpper i (j+1) mat
            Just i' -> return mat >>= zeroAll i' j >=> swapRow i i' >=> toUpper i+1 j+1
  in 
    toUpper mat 0 0
-}

-- | Computes reduced row echelon form, discarding the row-operation trace.
rowReduce :: F2Mat -> F2Mat
rowReduce = fst . runWriter . toReducedEchelon

-- | Computes row echelon form and records the row operations performed.
--
-- | Computes reduced row echelon form and records the row operations
-- performed.
toEchelon, toReducedEchelon :: F2Mat -> Writer [ROp] F2Mat
toEchelon mat@(F2Mat m n vals) =
  let isOne j (v,_) = v @. j

      zeroAll j y []     = return []
      zeroAll j y (x:xs) =
        if (fst x) @. j
        then do
          tell [Add (snd y) (snd x)]
          xs' <- zeroAll j y xs
          return $ ((fst y) + (fst x), snd x):xs'
        else do
          xs' <- zeroAll j y xs
          return $ x:xs'

      toUpper j [] = return $ []
      toUpper j xs
        | j >= n    = return $ xs
        | otherwise = case break (isOne j) xs of
            (_, [])      -> toUpper (j+1) xs
            ([], x:xs)   -> do
              xs' <- toUpper (j+1) =<< zeroAll j x xs
              return $ x:xs'
            (x:xs, y:ys) -> do
              let x' = (fst y, snd x)
              let y' = (fst x, snd y)
              tell [Exchange (snd x) (snd y)]
              xs' <- toUpper (j+1) =<< zeroAll j x' (xs ++ y':ys)
              return $ x':xs'
  in
    toUpper 0 (zip vals [0..]) >>= return . F2Mat m n . fst . unzip

toReducedEchelon mat@(F2Mat m n vals) =
  let isOne j (v,_) = v @. j

      zeroAll j y []     = return []
      zeroAll j y (x:xs) =
        if (fst x) @. j
        then do
          tell [Add (snd y) (snd x)]
          xs' <- zeroAll j y xs
          return $ ((fst y) + (fst x), snd x):xs'
        else do
          xs' <- zeroAll j y xs
          return $ x:xs'

      toUpper j sx [] = return $ reverse sx
      toUpper j sx xs
        | j >= n    = return $ (reverse sx) ++ xs
        | otherwise = case break (isOne j) xs of
            (_, [])      -> toUpper (j+1) sx xs
            ([], x:xs)   -> do
              sx' <- zeroAll j x sx
              xs' <- zeroAll j x xs
              toUpper (j+1) (x:sx') xs'
            (x:xs, y:ys) -> do
              let x' = (fst y, snd x)
              let y' = (fst x, snd y)
              tell [Exchange (snd x) (snd y)]
              sx' <- zeroAll j x' sx
              xs' <- zeroAll j x' (xs ++ y':ys)
              toUpper (j+1) (x':sx') xs'
  in
    toUpper 0 [] (zip vals [0..]) >>= return . F2Mat m n . fst . unzip

-- ** Optimized elimination

-- | Computes row echelon form using the Patel--Markov--Hayes block elimination
-- algorithm.
--
-- The first argument is the block width used to eliminate duplicate patterns.
toEchelonPMH :: Int -> F2Mat -> Writer [ROp] F2Mat
toEchelonPMH width mat@(F2Mat m n vals) =
  let isOne j (v,_) = v @. j

      removeDuplicates j (patterns, vals) v@(bv, r) =
        let subbv = bv @@ (min (j+width-1) (n-1), j) in
          if popCount subbv < 1 then return (patterns, v:vals) else
          case Map.lookup subbv patterns of
            Nothing              -> return (Map.insert subbv v patterns, v:vals)
            Just (bv', r') -> do
              tell [Add r' r]
              return (patterns, (bv + bv', r):vals)

      zeroAll j y []     = return []
      zeroAll j y (x:xs) =
        if (fst x) @. j
        then do
          tell [Add (snd y) (snd x)]
          xs' <- zeroAll j y xs
          return $ ((fst y) + (fst x), snd x):xs'
        else do
          xs' <- zeroAll j y xs
          return $ x:xs'

      toUpper j [] = return $ []
      toUpper j xs
        | j >= n             = return $ xs
        | j `mod` width == 0 = do
          (_, xsR) <- foldM (removeDuplicates j) (Map.empty, []) xs
          case break (isOne j) (reverse xsR) of
            (_, [])      -> toUpper (j+1) (reverse xsR)
            ([], x:xs)   -> do
              xs' <- toUpper (j+1) =<< zeroAll j x xs
              return $ x:xs'
            (x:xs, y:ys) -> do
              let x' = (fst y, snd x)
              let y' = (fst x, snd y)
              tell [Exchange (snd x) (snd y)]
              xs' <- toUpper (j+1) =<< zeroAll j x' (xs ++ y':ys)
              return $ x':xs'
        | otherwise =
          case break (isOne j) xs of
            (_, [])      -> toUpper (j+1) xs
            ([], x:xs)   -> do
              xs' <- toUpper (j+1) =<< zeroAll j x xs
              return $ x:xs'
            (x:xs, y:ys) -> do
              let x' = (fst y, snd x)
              let y' = (fst x, snd y)
              tell [Exchange (snd x) (snd y)]
              xs' <- toUpper (j+1) =<< zeroAll j x' (xs ++ y':ys)
              return $ x':xs'
  in
    toUpper 0 (zip vals [0..]) >>= return . F2Mat m n . fst . unzip

-- | Computes row echelon form while heuristically sparsifying pivot rows.
toEchelonA :: F2Mat -> Writer [ROp] F2Mat
toEchelonA mat@(F2Mat m n vals) =
  let isOne j (v,_) = v @. j

      backReduce j x xs =
        let iPop        = wt (fst x)
            f y         = iPop - wt (fst x + fst y)
            g n v y     =
              let r = f y in
                case v of
                  Nothing       -> if r >= n  then Just (r, y) else Nothing
                  Just (r', y') -> if r >= r' then Just (r, y) else Just (r', y')
            maxCutoff n = foldl' (g n) Nothing
        in
          case maxCutoff 2 xs of
            Nothing     -> return x
            Just (_, y) -> do
              tell [Add (snd y) (snd x)]
              backReduce j (fst x + fst y, snd x) xs

      zeroAll j y []     = return []
      zeroAll j y (x:xs) =
        if (fst x) @. j
        then do
          tell [Add (snd y) (snd x)]
          xs' <- zeroAll j y xs
          return $ ((fst y) + (fst x), snd x):xs'
        else do
          xs' <- zeroAll j y xs
          return $ x:xs'

      toUpper j [] = return $ []
      toUpper j xs
        | j >= n    = return $ xs
        | otherwise = case break (isOne j) xs of
            (_, [])      -> toUpper (j+1) xs
            ([], x:xs)   -> do
              xs' <- zeroAll j x xs
              x'  <- backReduce j x xs'
              toUpper (j+1) xs' >>= return . (x':)
            (x:xs, y:ys) -> do
              let x' = (fst y, snd x)
              let y' = (fst x, snd y)
              tell [Exchange (snd x) (snd y)]
              xs' <- zeroAll j x' (xs ++ y':ys)
              x'' <- backReduce j x' xs'
              toUpper (j+1) xs' >>= return . (x'':)
  in
    toUpper 0 (zip vals [0..]) >>= return . F2Mat m n . fst . unzip

-- | Combines Patel--Markov--Hayes block elimination with the sparsifying
-- heuristic of 'toEchelonA'.
toEchelonPMHA :: Int -> F2Mat -> Writer [ROp] F2Mat
toEchelonPMHA width mat@(F2Mat m n vals) =
  let isOne j (v,_) = v @. j

      removeDuplicates j (patterns, vals) v@(bv, r) =
        let subbv = bv @@ (min (j+width-1) (n-1), j) in
          if popCount subbv < 1 then return (patterns, v:vals) else
          case Map.lookup subbv patterns of
            Nothing              -> return (Map.insert subbv v patterns, v:vals)
            Just (bv', r') -> do
              tell [Add r' r]
              return (patterns, (bv + bv', r):vals)

      backReduce j x xs =
        let iPop        = wt (fst x)
            f y         = iPop - wt (fst x + fst y)
            g n v y     =
              let r = f y in
                case v of
                  Nothing       -> if r >= n  then Just (r, y) else Nothing
                  Just (r', y') -> if r >= r' then Just (r, y) else Just (r', y')
            maxCutoff n = foldl' (g n) Nothing
        in
          case maxCutoff 2 xs of
            Nothing     -> return x
            Just (_, y) -> do
              tell [Add (snd y) (snd x)]
              backReduce j (fst x + fst y, snd x) xs

      zeroAll j y []     = return []
      zeroAll j y (x:xs) =
        if (fst x) @. j
        then do
          tell [Add (snd y) (snd x)]
          xs' <- zeroAll j y xs
          return $ ((fst y) + (fst x), snd x):xs'
        else do
          xs' <- zeroAll j y xs
          return $ x:xs'

      toUpper j [] = return $ []
      toUpper j xs
        | j >= n             = return $ xs
        | j `mod` width == 0 = do
          (_, xsR) <- foldM (removeDuplicates j) (Map.empty, []) xs
          case break (isOne j) (reverse xsR) of
            (_, [])      -> toUpper (j+1) (reverse xsR)
            ([], x:xs)   -> do
              xs' <- zeroAll j x xs
              x'  <- backReduce j x xs'
              toUpper (j+1) xs' >>= return . (x':)
            (x:xs, y:ys) -> do
              let x' = (fst y, snd x)
              let y' = (fst x, snd y)
              tell [Exchange (snd x) (snd y)]
              xs' <- zeroAll j x' (xs ++ y':ys)
              x'' <- backReduce j x' xs'
              toUpper (j+1) xs' >>= return . (x'':)
        | otherwise =
          case break (isOne j) xs of
            (_, [])      -> toUpper (j+1) xs
            ([], x:xs)   -> do
              xs' <- zeroAll j x xs
              x'  <- backReduce j x xs'
              toUpper (j+1) xs' >>= return . (x':)
            (x:xs, y:ys) -> do
              let x' = (fst y, snd x)
              let y' = (fst x, snd y)
              tell [Exchange (snd x) (snd y)]
              xs' <- zeroAll j x' (xs ++ y':ys)
              x'' <- backReduce j x' xs'
              toUpper (j+1) xs' >>= return . (x'':)
  in
    toUpper 0 (zip vals [0..]) >>= return . F2Mat m n . fst . unzip

-- | Reduces a square matrix by eliminating rows, transposing, and eliminating
-- again.
toReducedEchelonSqr :: F2Mat -> Writer [ROp] F2Mat
toReducedEchelonSqr mat = censor transposeROps . toEchelon . transpose =<< toEchelon mat

-- | Computes reduced row echelon form with Patel--Markov--Hayes elimination.
--
-- A block width is selected automatically from the number of columns.
toReducedEchelonPMH :: F2Mat -> Writer [ROp] F2Mat
toReducedEchelonPMH mat
  | n mat < 2 = toReducedEchelonSqr mat
  | otherwise =
    let width = (ceiling . (/ 2) . logBase 2.0 . fromIntegral) $ n mat in
      censor transposeROps . (toEchelonPMH width) . transpose =<< (toEchelonPMH width) mat

-- | Computes reduced row echelon form using sparsifying elimination.
toReducedEchelonA :: F2Mat -> Writer [ROp] F2Mat
toReducedEchelonA mat = censor transposeROps . toEchelon . transpose =<< toEchelonA mat

-- | Computes reduced row echelon form using combined block and sparsifying
-- elimination.
toReducedEchelonPMHA :: F2Mat -> Writer [ROp] F2Mat
toReducedEchelonPMHA mat
  | n mat < 2 = toReducedEchelonA mat
  | otherwise =
    let width = (ceiling . (/ 2) . logBase 2.0 . fromIntegral) $ n mat in
      censor transposeROps . (toEchelonPMH width) . transpose =<< toEchelonPMHA width mat

-- ** Rank and generalized inverses

-- | Reduces a vector by the pivot rows of a matrix in echelon form.
reduceVector :: F2Mat -> F2Vec -> F2Vec
reduceVector mat@(F2Mat m n vals) vec = go 0 vals vec where
  go _ []     vec = vec
  go i (x:xs) vec
    | i == n     = vec
    | not (x@.i) = go (i+1) (x:xs) vec
    | otherwise  = go (i+1) xs $ if vec@.i then x + vec else vec

-- | Computes the row rank of a matrix.
rank :: F2Mat -> Int
rank mat =
  let (echelon, _) = runWriter $ toEchelon mat in
    foldr (\v tot -> if popCount v > 0 then tot + 1 else tot) 0 $ vals echelon

-- | Tests whether a matrix is square and has full rank.
fullRank :: F2Mat -> Bool
fullRank mat = m mat == n mat && rank mat == m mat

-- | Determines a sequence of column exchanges that moves independent columns
-- to the left.
--
-- The returned integer is the column rank. Operations are recorded as 'ROp'
-- values because column operations on a matrix correspond to row operations
-- on its transpose.
columnReduceDry :: F2Mat -> Writer [ROp] Int
columnReduceDry mat@(F2Mat m n vals) =
  let isOne v imap j = v @. (imap ! j)

      swapVals i j imap = Map.insert i (imap ! j) $ Map.insert j (imap ! i) imap

      toLeft j imap [] = return j
      toLeft j imap (x:xs) 
        | j >= n    = return j
        | otherwise = case break (isOne x imap) [j..n-1] of
            (_, [])   -> toLeft j imap xs
            ([], _)   -> toLeft (j+1) imap xs
            (_, j':_) -> do
              tell [Exchange j j']
              toLeft (j+1) (swapVals j j' imap) xs
  in
    toLeft 0 (Map.fromList $ zip [0..n-1] [0..]) vals

-- | Computes a transposed generalized inverse.
--
-- | Computes a generalized inverse @A+@ satisfying @A A+ A = A@.
pseudoinverseT, pseudoinverse :: F2Mat -> F2Mat
pseudoinverseT mat@(F2Mat m n vals) =
  let (mat', rops) = runWriter $ toReducedEchelon mat
      (rank, cops) = runWriter $ columnReduceDry mat'
      partialInv   = applyROps (resizeMat n m $ identity rank) $ transposeROps cops
  in
    applyROps (transpose partialInv) $ transposeROps rops

pseudoinverse = transpose . pseudoinverseT

{- ----------------------------------------------------------------------------- -}

-- * Extending vector-space bases
--
-- These routines append rows that are independent of the existing row space.
-- If the ambient space is already spanned, functions that promise additional
-- rank extend the width of every row with zeroes and introduce new standard
-- basis vectors in the added coordinates.

-- | Appends a row independent of the existing rows, adding a column if the
-- row space already spans all current columns.
increaseRank :: F2Mat -> F2Mat
increaseRank mat@(F2Mat m n vals) = 
  let isOne j v = v @. j

      zeroAll j y []     = []
      zeroAll j y (x:xs) =
        let xs' = zeroAll j y xs in
          if x @. j
          then (y + x):xs'
          else x:xs'

      toUpper j xs
        | j >= n    =
          let mat'@(F2Mat _ _ vals') = resizeMat m (n+1) mat
              vec  = shift (bitVec (n+1) 1) j
          in
            mat' { vals = vals' ++ [vec] }
        | otherwise = case break (isOne j) xs of
            (_, [])      -> mat { vals = vals ++ [shift (bitVec n 1) j] }
            ([], x:xs)   -> toUpper (j+1) (zeroAll j x xs)
            (x:xs, y:ys) -> toUpper (j+1) (zeroAll j y (xs ++ x:ys))
  in
    toUpper 0 vals

-- | Appends the requested number of independent rows, adding columns as
-- necessary.
increaseRankN :: F2Mat -> Int -> F2Mat
increaseRankN mat@(F2Mat m n vals) r = 
  let isOne j v = v @. j

      zeroAll j y []     = []
      zeroAll j y (x:xs) =
        let xs' = zeroAll j y xs in
          if x @. j
          then (y + x):xs'
          else x:xs'

      toUpper j xs r vecs
        | r == 0    = mat { vals = vals ++ reverse vecs }
        | j >= n    =
          let mat'@(F2Mat _ _ vals') = resizeMat m (n+r) mat
              vecs' = [shift (bitVec (n+r) 1) i | i <- [n..n+r-1]]
          in
            mat' { vals = vals' ++ reverse vecs ++ vecs' }
        | otherwise = case break (isOne j) xs of
            (_, [])      -> toUpper (j+1) xs (r-1) $ (shift (bitVec n 1) j):vecs
            ([], x:xs)   -> toUpper (j+1) (zeroAll j x xs) r vecs
            (x:xs, y:ys) -> toUpper (j+1) (zeroAll j y (xs ++ x:ys)) r vecs
  in
    toUpper 0 vals r []

-- | Appends one standard-basis row not already represented by a pivot.
--
-- Unlike 'increaseRank', this routine also avoids selecting a pivot already
-- encountered during elimination.
increaseRankInd :: F2Mat -> F2Mat
increaseRankInd mat@(F2Mat m n vals) = 
  let isOne j v = v @. j

      zeroAll j y []     = []
      zeroAll j y (x:xs) =
        let xs' = zeroAll j y xs in
          if x @. j
          then (y + x):xs'
          else x:xs'

      toUpper j xs sx
        | j >= n    =
          let mat'@(F2Mat _ _ vals') = resizeMat m (n+1) mat
              vec  = shift (bitVec (n+1) 1) j
          in
            mat' { vals = vals' ++ [vec] }
        | otherwise = case break (isOne j) xs of
            (_, [])      ->
              if any (isOne j) sx
              then toUpper (j+1) xs sx
              else 
                let vec = shift (bitVec n 1) j in
                  mat { vals = vals ++ [vec] }
            ([], x:xs)   -> toUpper (j+1) (zeroAll j x xs) (x:sx)
            (x:xs, y:ys) -> toUpper (j+1) (zeroAll j y (xs ++ x:ys)) (y:sx)
  in
    toUpper 0 vals []

-- ** Completing a basis

-- | Appends standard-basis rows until the matrix has full column rank.
fillColumnRank :: F2Mat -> F2Mat
fillColumnRank mat@(F2Mat m n vals) = 
  let isOne j v = v @. j

      zeroAll j y []     = []
      zeroAll j y (x:xs) =
        let xs' = zeroAll j y xs in
          if x @. j
          then (y + x):xs'
          else x:xs'

      toUpper j xs vecs
        | j >= n    = mat { vals = vals ++ reverse vecs }
        | otherwise = case break (isOne j) xs of
            (_, [])      -> toUpper (j+1) xs $ (shift (bitVec n 1) j):vecs
            ([], x:xs)   -> toUpper (j+1) (zeroAll j x xs) vecs
            (x:xs, y:ys) -> toUpper (j+1) (zeroAll j y (xs ++ x:ys)) vecs
  in
    toUpper 0 vals []

-- | Extends the row space of the first matrix with as many independent rows of
-- the second matrix as possible.
fillFrom :: F2Mat -> F2Mat -> F2Mat
fillFrom mat@(F2Mat m n vals) fill = 
  let (F2Mat _ _ fillVals) = fst . runWriter . toEchelon $ fill
      isOne j v = v @. j

      findVec j j' xs
        | j < j'    = Nothing
        | otherwise = case break (isOne j') xs of
            (_, [])    -> findVec j (j'+1) xs
            ([], x:xs) -> if j == j' then Just x else findVec j (j'+1) xs
            _          -> error "Fill matrix wasn't in echelon form"

      zeroAll j y []     = []
      zeroAll j y (x:xs) =
        let xs' = zeroAll j y xs in
          if x @. j
          then (y + x):xs'
          else x:xs'

      toUpper j xs vecs
        | j >= n    = mat { vals = vals ++ reverse vecs }
        | otherwise = case break (isOne j) xs of
            (_, [])      -> case findVec j 0 fillVals of
              Nothing -> toUpper (j+1) xs vecs
              Just v  -> toUpper (j+1) xs $ v:vecs
            ([], x:xs)   -> toUpper (j+1) (zeroAll j x xs) vecs
            (x:xs, y:ys) -> toUpper (j+1) (zeroAll j y (xs ++ x:ys)) vecs
  in
    toUpper 0 vals []

-- | Adds an independent vector to a collection, extending every vector when
-- necessary. Returns the resulting width and vectors.
addIndependent :: [F2Vec] -> (Int, [F2Vec])
addIndependent a =
  let (F2Mat m n vals) = increaseRankInd $ fromList a in
    (n, vals)

{- ----------------------------------------------------------------------------- -}

-- * Transformation matrices
--
-- A transformation matrix describes row operations algebraically: left
-- multiplication maps one ordered collection of row vectors to another.

-- | Finds a matrix intended to transform the rows of the first matrix into the
-- rows of the second.
--
-- This general form uses a pseudoinverse. It may not produce the desired
-- transformation when the rows of the second matrix are linearly dependent.
transformMat :: F2Mat -> F2Mat -> F2Mat
transformMat a b = mult b $ pseudoinverse a 

-- | Finds a row-operation matrix transforming the first matrix into the
-- second. The matrices must span the same row space.
transformMatStrict :: F2Mat -> F2Mat -> F2Mat
transformMatStrict a b =
  let (_, aops) = runWriter $ toReducedEchelon a
      (_, bops) = runWriter $ toReducedEchelon b
  in
    applyROps (identity $ m a) $ aops ++ reverse bops

{- ----------------------------------------------------------------------------- -}

-- * Solving linear systems
--
-- The functions in this section solve systems @A x = b@ over
-- \(\mathbb{F}_2\). The solver constructors are designed for partial
-- application: compute the generalized inverse once for a fixed @A@ and reuse
-- it for multiple right-hand sides.

-- | Precomputes a matrix for repeatedly solving systems with the same
-- coefficient matrix.
--
-- | Transposed form of 'solver'.
--
-- | A 'solver' with zero rows removed.
--
solver, solverT, solverReduced :: F2Mat -> F2Mat
solver         = pseudoinverse
solverT        = pseudoinverseT
solverReduced  = removeZeroRows . pseudoinverse

-- | A transposed 'solver' with zero rows removed.
solverTReduced = removeZeroRows . pseudoinverseT

-- | Enumerates every solution to @A x = b@.
--
-- Returns the empty set when the system is inconsistent. This enumeration is
-- exponential in the number of columns of @A@.
allSolutions :: F2Mat -> F2Vec -> Set F2Vec
allSolutions a =
  let !ag = pseudoinverse a in \b ->
    let x        = multVec ag b
        ker      = add (identity $ n a) (mult ag a)
        genSol w = x + (multVec ker w)
    in
      if b == multVec a x
        then foldr (\w -> Set.insert $ genSol w) Set.empty $ allVecs $ n a
        else Set.empty
      
-- | Tests whether @A x = b@ has at least one solution.
existsSolutions :: F2Mat -> F2Vec -> Bool
existsSolutions a =
  let !aag = mult a $ pseudoinverse a in \b ->
    b == (multVec aag b)

-- | Finds one solution to @A x = b@, or 'Nothing' if the system is
-- inconsistent.
oneSolution :: F2Mat -> F2Vec -> Maybe F2Vec
oneSolution a =
  let !ag = pseudoinverse a in \b ->
    let x = multVec ag b in 
      if b == multVec a x then Just x else Nothing

-- | Finds a minimum-Hamming-weight solution to @A x = b@.
--
-- The search enumerates the kernel of @A@ and is exponential in the number of
-- columns.
minSolution :: F2Mat -> F2Vec -> Maybe F2Vec
minSolution a =
  let !ag = pseudoinverse a in \b ->
    let x        = multVec ag b
        ker      = add (identity $ n a) (mult ag a)
        genSol w = x + (multVec ker w)
    in
      if b == multVec a x
        then foldM (\min w -> Just $ minWt min $ genSol w) x $ allVecs $ n a
        else Nothing

{- ----------------------------------------------------------------------------- -}

-- * Vector-space queries
--
-- These convenience functions treat lists of vectors as generating sets for
-- their row spans. Like the solvers above, 'inLinearSpan' is arranged for
-- partial application to a fixed generating set.

-- | Tests whether a vector lies in the span of a collection of row vectors.
--
inLinearSpan :: [F2Vec] -> F2Vec -> Bool
inLinearSpan a =
  let !aT   = fromList a
      !agT  = pseudoinverse aT
      !aagT = mult agT aT
  in
    \b -> b == multRow b aagT

-- | Finds the original index of a linearly dependent vector, if one exists.
findDependent :: [F2Vec] -> Maybe Int
findDependent a =
  let (mat, rops) = runWriter . toEchelon . fromList $ a
      f (i, row)  = if bitVec 0 (n mat) == row
                       then Just $ permute i (reverse rops)
                       else Nothing
  in
    msum $ map f (zip [0..] (vals mat))

-- | Tests whether two collections of vectors span the same space.
sameSpace :: [F2Vec] -> [F2Vec] -> Bool
sameSpace a b =
  let solveA = inLinearSpan a
      solveB = inLinearSpan b
  in
    all solveA b && all solveB a

{- ----------------------------------------------------------------------------- -}

-- * Testing utilities

-- ** Matrix generators

-- | Range of row counts generated by the 'Arbitrary' instance.
rowRange :: (Int, Int)
rowRange = (10, 100)

-- | Range of column counts generated by the 'Arbitrary' instance.
colRange :: (Int, Int)
colRange = (10, 100)

instance Arbitrary F2Mat where
  arbitrary = do
    m <- choose rowRange
    n <- choose colRange
    let genRow = (vector n) >>= return . fromBits
    vals <- sequence $ replicate m genRow
    return $ F2Mat m n vals

-- | Generates a matrix with a fixed number of columns.
--
-- | Generates a matrix with a fixed number of rows.
arbitraryFixedN, arbitraryFixedM :: Int -> Gen F2Mat
arbitraryFixedN n = do
  m <- choose rowRange
  let genRow = (vector n) >>= return . fromBits
  vals <- sequence $ replicate m genRow
  return $ F2Mat m n vals
arbitraryFixedM m = do
  n <- choose colRange
  let genRow = (vector n) >>= return . fromBits
  vals <- sequence $ replicate m genRow
  return $ F2Mat m n vals

-- | Generates a matrix with the given dimensions.
arbitraryFixed :: Int -> Int -> Gen F2Mat
arbitraryFixed m n = do
  let genRow = (vector n) >>= return . fromBits
  vals <- sequence $ replicate m genRow
  return $ F2Mat m n vals

-- | Generates a matrix whose row space is a subspace of that of the argument.
arbitrarySubspace :: F2Mat -> Gen F2Mat
arbitrarySubspace a =
  liftM (multT a) $ arbitraryFixed (m a) (m a)

-- ** Property combinators

-- | Tests whether a unary operation is involutive.
--
-- | Tests whether a unary operation is idempotent.
invol, idemp :: Eq a => (a -> a) -> (a -> Bool)

invol f = \a -> a == (f $ f a)
idemp f = \a -> (f a) == (f $ f a)

-- | Tests whether a value is a left identity for an operation.
--
-- | Tests whether a value is a right identity for an operation.
lid, rid   :: Eq a => (a -> a -> a) -> a -> (a -> Bool)

-- | Tests a proposed left inverse operation.
--
-- | Tests a proposed right inverse operation.
linv, rinv :: Eq a => (a -> a -> a) -> a -> (a -> a) -> (a -> Bool)

-- | Tests associativity of a binary operation at three values.
assoc      :: Eq a => (a -> a -> a) -> (a -> a -> a -> Bool)

-- | Tests commutativity of a binary operation at two values.
commut     :: Eq a => (a -> a -> a) -> (a -> a -> Bool)

lid    f i = \a -> f i a == a
rid    f i = \a -> f a i == a
linv   f i inv = \a -> f (inv a) a == i
rinv   f i inv = \a -> f a (inv a) == i
assoc  f = \a b c -> f a (f b c) == f (f a b) c
commut f = \a b   -> f a b == f b a

-- | Tests whether a matrix is square.
--
-- | Tests whether a matrix is square and invertible.
isSquare, isInvertible :: F2Mat -> Bool

isSquare mat = m mat == n mat
isInvertible mat = isSquare mat && rank mat == m mat

-- ** Matrix properties

-- | Property: transposition is involutive.
prop_TransposeInvolutive = invol transpose

-- | Property: echelon reduction is idempotent.
prop_ToEchelonIdempotent = idemp (fst . runWriter . toEchelon)

-- | Property: reduced-echelon reduction is idempotent.
prop_ToReducedEchelonIdempotent = idemp (fst . runWriter . toReducedEchelon)

-- | Property: matrix multiplication is associative for compatible matrices.
prop_MultAssociative = do
  a <- arbitrary
  b <- arbitraryFixedM $ n a
  c <- arbitraryFixedM $ n b
  return $ assoc mult a b c

-- | Property: the generalized inverse satisfies @A A+ A = A@.
prop_PseudoinverseCorrect = \m -> m == mult (mult m $ pseudoinverse m) m

-- | Property: 'transformMat' maps a matrix to a generated subspace.
prop_TransformMatCorrect = do
  a <- arbitrary
  b <- arbitrarySubspace a
  return $ mult (transformMat a b) a == b

-- | Property: matroid partitioning preserves the input set of nonzero vectors.
prop_MatroidPartition = do
  a <- arbitrary
  let vecs = filter (\bv -> popCount bv /= 0) $ vals a
  return $ (Set.fromList vecs) == (foldr Set.union Set.empty $ partitionAll vecs)

-- | Property: every part produced by matroid partitioning is independent.
prop_MatroidCorrect = do
  a <- arbitrary
  let vecs = filter (\bv -> popCount bv /= 0) $ vals a
  return $ all independent $ partitionAll vecs

-- | Runs the QuickCheck property suite for this module.
tests :: () -> IO ()
tests _ = do
  quickCheck $ prop_TransposeInvolutive
  quickCheck $ prop_ToEchelonIdempotent
  quickCheck $ prop_ToReducedEchelonIdempotent
  quickCheck $ prop_MultAssociative
  quickCheck $ prop_PseudoinverseCorrect
  quickCheck $ prop_TransformMatCorrect
  quickCheck $ prop_MatroidCorrect
