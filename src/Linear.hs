{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE BangPatterns #-}

module Linear where

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

import Matroid

import Test.QuickCheck hiding ((.&.))

{- Finite products of GF(2), convenience type to redefine show & num -}
newtype F2Vec = F2Vec { getBV :: BitVector.BV } deriving (Eq, Ord, Bits)

bitVec :: Integral a => Int -> a -> F2Vec
bitVec n i = coerce $ BitVector.bitVec n i

(@.) :: Integral a => F2Vec -> a -> Bool
(@.) v i = coerce $ (BitVector.@.) (coerce v) i

(@@) :: Integral a => F2Vec -> (a, a) -> F2Vec
(@@) v (i, j) = coerce $ (BitVector.@@) (coerce v) (i, j)

zeroExtend :: Integral a => a -> F2Vec -> F2Vec
zeroExtend i v = coerce $ BitVector.zeroExtend i (coerce v)

size :: F2Vec -> Int
size = coerce BitVector.size

fromBits :: [Bool] -> F2Vec
fromBits = coerce BitVector.fromBits

{- Little-endian -}
instance Show F2Vec where
  show v = map (f . (v @.)) [0..size v - 1]
    where f b = if b then '1' else '0'

{- Num instance coinciding with the vector space GF(2)^n -}
instance Num F2Vec where
  (+)         = xor
  (*)         = (.&.)
  negate      = id
  abs         = id
  signum      = id
  fromInteger = bitVec 32

instance Matroid F2Vec where
  independent s = (Set.size s) == (rank $ fromList $ Set.toList s)

allVecs :: Int -> [F2Vec]
allVecs n = map (bitVec n) [0..2^n-1]

wt :: F2Vec -> Int
wt = popCount

minWt :: F2Vec -> F2Vec -> F2Vec
minWt u v = if wt u < wt v then u else v

{- Matrices over GF(2) -}
data F2Mat = F2Mat {
  m :: Int,
  n :: Int,
  vals :: [F2Vec]
  } deriving (Eq)

instance Show F2Mat where
  show (F2Mat m n vals) = intercalate "\n" $ map show vals

{- Constructors -}
identity :: Int -> F2Mat
identity n = F2Mat n n $ map (\i -> shift (bitVec n 1) i) [0..n-1]

{- Conversions -}
resizeMat :: Int -> Int -> F2Mat -> F2Mat
resizeMat m' n' (F2Mat m n vals) = F2Mat m' n' vals'
  where vals' = (map f $ take m' vals) ++ (replicate (m'-m) $ bitVec n' 0)
        f     = if n' > n
                then zeroExtend (n'-n)
                else (flip (@@)) (n'-1, 0) 

toList :: F2Mat -> [F2Vec]
toList (F2Mat m n vals) = vals

fromList :: [F2Vec] -> F2Mat
fromList []   = F2Mat 0 0 []
fromList vecs@(x:xs) =
  if all ((n ==) . size) xs
    then F2Mat (length vecs) n vecs
    else error "Vectors have differing lengths"
  where n = size x

fromVec :: F2Vec -> F2Mat
fromVec x = F2Mat 1 n [x]
  where n = size x

{- Accessors -}
row :: F2Mat -> Int -> F2Vec
row (F2Mat m n vals) i
  | 0 <= i && i < m = vals !! i
  | otherwise       = error "Row index out of bounds"

index :: F2Mat -> Int -> Int -> Bool
index mat@(F2Mat m n vals) i j
  | 0 <= j && j < n = (row mat i) @. j
  | otherwise       = error "Column index out of bounds"

{- Linear algebra -}

{- Expensive (relatively speaking) -}
transpose :: F2Mat -> F2Mat
transpose (F2Mat m n vals) = F2Mat n m vals'
  where vals'    = map f [0..n-1]
        f j      = fromBits $ foldl' (g j) [] vals
        g j xs v = (v @. j):xs

{- If A is a set of vectors over B, coc A gives the change of coordinates matrix from A to B -}
coc :: [F2Vec] -> F2Mat
coc = transpose . fromList

{- Matrix multiplication -}
mult :: F2Mat -> F2Mat -> F2Mat
mult a@(F2Mat am an avals) b@(F2Mat bm bn bvals)
  | an /= bm  = error $ "Incompatible matrix dimensions:\n" ++ show a ++ "\n\n" ++ show b ++ "\n"
  | otherwise = F2Mat am bn $ map multRow avals
    where multRow v       = foldl' (f v) (bitVec bn 0) $ zip bvals [0..]
          f v sum (v', i) = if  v @. i then sum `xor` v' else sum

{- Swap the arguments of mult. If A and B are stored column-major, multT A B = A * B -}
multT :: F2Mat -> F2Mat -> F2Mat
multT a b = mult b a

{- Right-multiply a row vector by a matrix -}
multRow :: F2Vec -> F2Mat -> F2Vec
multRow v = head . toList . mult (fromVec v)

{- Left-multiply a column vector by a matrix -}
multVec :: F2Mat -> F2Vec -> F2Vec
multVec m = head . toList . multT (transpose m) . fromVec

{- Matrix addition -}
add :: F2Mat -> F2Mat -> F2Mat
add a@(F2Mat am an avals) b@(F2Mat bm bn bvals)
  | am /= bm || an /= bn = error "Incompatible matrix dimensions"
  | otherwise = F2Mat am an $ zipWith xor avals bvals

{- Row operations -}
data ROp = Exchange Int Int | Add Int Int deriving (Eq, Show)

removeZeroRows :: F2Mat -> F2Mat
removeZeroRows a@(F2Mat _ n vals) = 
  a { vals = filter (bitVec n 0 /=) vals }

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

addRow :: Int -> Int -> F2Mat -> F2Mat
addRow i j mat@(F2Mat m n vals)
  | 0 <= i && 0 <= j && i < m && j < m =
    let (v1, v2) = splitAt j vals
        newV     = (head v2) `xor` (vals !! i)
    in
      mat { vals = v1 ++ newV:(tail v2) }
  | otherwise                          = error "Add indices out of bounds"

applyROp :: ROp -> F2Mat -> F2Mat
applyROp (Exchange i j) = swapRow i j
applyROp (Add  i j) = addRow  i j
applyROps = foldl' (flip applyROp) 

transposeROp :: ROp -> ROp
transposeROp (Exchange i j) = Exchange j i
transposeROp (Add  i j) = Add  j i
transposeROps = foldl' (\acc rop -> (transposeROp rop):acc) []

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

{- Gaussian elimination methods -}
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

{- Avoids indexing -}
toEchelon, toReducedEchelon :: F2Mat -> Writer [ROp] F2Mat
toEchelon mat@(F2Mat m n vals) =
  let isOne j (v,_) = v @. j

      zeroAll j y []     = return []
      zeroAll j y (x:xs) =
        if (fst x) @. j
        then do
          tell [Add (snd y) (snd x)]
          xs' <- zeroAll j y xs
          return $ ((fst y) `xor` (fst x), snd x):xs'
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
          return $ ((fst y) `xor` (fst x), snd x):xs'
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

toReducedEchelonSqr :: F2Mat -> Writer [ROp] F2Mat
toReducedEchelonSqr mat = censor transposeROps . toEchelon . transpose =<< toEchelon mat

{- The Patel, Markov & Hayes elimination algorithm for minimizing row operations -}
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
              return (patterns, (bv `xor` bv', r):vals)

      zeroAll j y []     = return []
      zeroAll j y (x:xs) =
        if (fst x) @. j
        then do
          tell [Add (snd y) (snd x)]
          xs' <- zeroAll j y xs
          return $ ((fst y) `xor` (fst x), snd x):xs'
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

toReducedEchelonPMH :: F2Mat -> Writer [ROp] F2Mat
toReducedEchelonPMH mat =
  let width = (ceiling . (/ 2) . logBase 2.0 . fromIntegral) $ n mat in
    censor transposeROps . (toEchelonPMH width) . transpose =<< (toEchelonPMH width) mat

rank :: F2Mat -> Int
rank mat =
  let (echelon, _) = runWriter $ toEchelon mat in
    foldr (\v tot -> if popCount v > 0 then tot + 1 else tot) 0 $ vals echelon

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

pseudoinverseT, pseudoinverse :: F2Mat -> F2Mat
pseudoinverseT mat@(F2Mat m n vals) =
  let (mat', rops) = runWriter $ toReducedEchelon mat
      (rank, cops) = runWriter $ columnReduceDry mat'
      partialInv   = applyROps (resizeMat n m $ identity rank) $ transposeROps cops
  in
    applyROps (transpose partialInv) $ transposeROps rops

pseudoinverse = transpose . pseudoinverseT

increaseRank :: F2Mat -> F2Mat
increaseRank mat@(F2Mat m n vals) = 
  let isOne j v = v @. j

      zeroAll j y []     = []
      zeroAll j y (x:xs) =
        let xs' = zeroAll j y xs in
          if x @. j
          then (y `xor` x):xs'
          else x:xs'

      toUpper j xs
        | j >= n    =
          let mat'@(F2Mat _ _ vals') = resizeMat m (n+1) mat
              vec  = shift (bitVec (n+1) 1) j
          in
            mat' { vals = vals' ++ [vec] }
        | otherwise = case break (isOne j) xs of
            (_, [])      ->
              let vec = shift (bitVec n 1) j in
                mat { vals = vals ++ [vec] }
            ([], x:xs)   -> toUpper (j+1) $ zeroAll j x xs
            (x:xs, y:ys) -> toUpper (j+1) $ zeroAll j y (xs ++ x:ys)
  in
    toUpper 0 vals

increaseRankN :: F2Mat -> Int -> F2Mat
increaseRankN mat@(F2Mat m n vals) r = 
  let isOne j v = v @. j

      zeroAll j y []     = []
      zeroAll j y (x:xs) =
        let xs' = zeroAll j y xs in
          if x @. j
          then (y `xor` x):xs'
          else x:xs'

      toUpper j xs r vecs
        | r == 0    = mat { vals = vals ++ vecs }
        | j >= n    =
          let mat'@(F2Mat _ _ vals') = resizeMat m (n+r) mat
              vecs = [shift (bitVec (n+r) 1) i | i <- [n..n+r-1]]
          in
            mat' { vals = vals' ++ vecs }
        | otherwise = case break (isOne j) xs of
            (_, [])      -> toUpper (j+1) xs (r-1) $ (shift (bitVec n 1) j):vecs
            ([], x:xs)   -> toUpper (j+1) (zeroAll j x xs) r vecs
            (x:xs, y:ys) -> toUpper (j+1) (zeroAll j y (xs ++ x:ys)) r vecs
  in
    toUpper 0 vals r []

{- Transformation matrix from one set of vectors to another -}
transformMat :: F2Mat -> F2Mat -> F2Mat
transformMat a b = mult b $ pseudoinverse a

{- Solving linear systems, optimized for partial evaluation on a matrix -}
solver, solverT, solverReduced :: F2Mat -> F2Mat
solver         = pseudoinverse
solverT        = pseudoinverseT
solverReduced  = removeZeroRows . pseudoinverse
solverTReduced = removeZeroRows . pseudoinverseT

allSolutions :: F2Mat -> F2Vec -> Set F2Vec
allSolutions a =
  let !ag = pseudoinverse a in \b ->
    let x        = multVec ag b
        ker      = add (identity $ n a) (mult ag a)
        genSol w = x `xor` (multVec ker w)
    in
      if b == multVec a x
        then foldr (\w -> Set.insert $ genSol w) Set.empty $ allVecs $ n a
        else Set.empty
      
existsSolutions :: F2Mat -> F2Vec -> Bool
existsSolutions a =
  let !aag = mult a $ pseudoinverse a in \b ->
    b == (multVec aag b)

oneSolution :: F2Mat -> F2Vec -> Maybe F2Vec
oneSolution a =
  let !ag = pseudoinverse a in \b ->
    let x = multVec ag b in 
      if b == multVec a x then Just x else Nothing

minSolution :: F2Mat -> F2Vec -> Maybe F2Vec
minSolution a =
  let !ag = pseudoinverse a in \b ->
    let x        = multVec ag b
        ker      = add (identity $ n a) (mult ag a)
        genSol w = x `xor` (multVec ker w)
    in
      if b == multVec a x
        then foldM (\min w -> Just $ minWt min $ genSol w) x $ allVecs $ n a
        else Nothing

{- Some shortcuts for sets of vectors -}
inLinearSpan :: [F2Vec] -> F2Vec -> Bool
inLinearSpan a =
  let !aT   = fromList a
      !agT  = pseudoinverse aT
      !aagT = mult agT aT
  in
    \b -> b == multRow b aagT

addIndependent :: [F2Vec] -> (Int, [F2Vec])
addIndependent a =
  let (F2Mat m n vals) = increaseRank $ fromList a in
    (n, vals)

{- Testing -}
rowRange = (10, 100)
colRange = (10, 100)

instance Arbitrary F2Mat where
  arbitrary = do
    m <- choose rowRange
    n <- choose colRange
    let genRow = (vector n) >>= return . fromBits
    vals <- sequence $ replicate m genRow
    return $ F2Mat m n vals

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

arbitraryFixed :: Int -> Int -> Gen F2Mat
arbitraryFixed m n = do
  let genRow = (vector n) >>= return . fromBits
  vals <- sequence $ replicate m genRow
  return $ F2Mat m n vals

-- Generate a matrix whose rowspace is a subspace of it's argument's
arbitrarySubspace :: F2Mat -> Gen F2Mat
arbitrarySubspace a =
  liftM (multT a) $ arbitraryFixed (m a) (m a)

{- Properties of unary operators -}
invol, idemp :: Eq a => (a -> a) -> (a -> Bool)

invol f = \a -> a == (f $ f a)
idemp f = \a -> (f a) == (f $ f a)

{- Properties of binary operators -}
lid, rid   :: Eq a => (a -> a -> a) -> a -> (a -> Bool)
linv, rinv :: Eq a => (a -> a -> a) -> a -> (a -> a) -> (a -> Bool)
assoc      :: Eq a => (a -> a -> a) -> (a -> a -> a -> Bool)
commut     :: Eq a => (a -> a -> a) -> (a -> a -> Bool)

lid    f i = \a -> f i a == a
rid    f i = \a -> f a i == a
linv   f i inv = \a -> f (inv a) a == i
rinv   f i inv = \a -> f a (inv a) == i
assoc  f = \a b c -> f a (f b c) == f (f a b) c
commut f = \a b   -> f a b == f b a

{- Matrix properties -}
isSquare, isInvertible :: F2Mat -> Bool

isSquare mat = m mat == n mat
isInvertible mat = isSquare mat && rank mat == m mat

prop_TransposeInvolutive = invol transpose
prop_ToEchelonIdempotent = idemp (fst . runWriter . toEchelon)
prop_ToReducedEchelonIdempotent = idemp (fst . runWriter . toReducedEchelon)
prop_MultAssociative = do
  a <- arbitrary
  b <- arbitraryFixedM $ n a
  c <- arbitraryFixedM $ n b
  return $ assoc mult a b c
prop_PseudoinverseCorrect = \m -> m == mult (mult m $ pseudoinverse m) m
prop_TransformMatCorrect = do
  a <- arbitrary
  b <- arbitrarySubspace a
  return $ mult (transformMat a b) a == b

prop_MatroidPartition = do
  a <- arbitrary
  let vecs = filter (\bv -> popCount bv /= 0) $ vals a
  return $ (Set.fromList vecs) == (foldr Set.union Set.empty $ partitionAll vecs)
prop_MatroidCorrect = do
  a <- arbitrary
  let vecs = filter (\bv -> popCount bv /= 0) $ vals a
  return $ all independent $ partitionAll vecs

tests :: () -> IO ()
tests _ = do
  quickCheck $ prop_TransposeInvolutive
  quickCheck $ prop_ToEchelonIdempotent
  quickCheck $ prop_ToReducedEchelonIdempotent
  quickCheck $ prop_MultAssociative
  quickCheck $ prop_PseudoinverseCorrect
  quickCheck $ prop_TransformMatCorrect
  quickCheck $ prop_MatroidCorrect
