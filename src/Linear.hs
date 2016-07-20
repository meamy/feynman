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

import Data.BitVector (BV, (@.), xor)
import qualified Data.BitVector as BitVector

import Test.QuickCheck

newtype F2Vec = F2Vec { getBV :: BV } deriving (Eq, Ord)

instance Show F2Vec where
  show (F2Vec b) = map (f . (b @.)) [0..BitVector.size b - 1]
    where f b = if b then '1' else '0'

bb :: Int -> Int -> F2Vec
bb i j = F2Vec $ BitVector.bitVec i j

allVecs :: Int -> [F2Vec]
allVecs n = map (bb n) [0..2^n-1]

minWt :: F2Vec -> F2Vec -> F2Vec
minWt u v = if BitVector.popCount (getBV u) < BitVector.popCount (getBV v) then u else v

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
identity n = F2Mat n n $ map (\i -> F2Vec $ BitVector.shift (BitVector.bitVec n 1) i) [0..n-1]

{- Conversions -}
resizeMat :: Int -> Int -> F2Mat -> F2Mat
resizeMat m' n' (F2Mat m n vals) = F2Mat m' n' vals'
  where vals' = (map f $ take m' vals) ++ (replicate (m'-m) $ F2Vec $ BitVector.bitVec n' 0)
        f     = if n' > n
                then F2Vec . (BitVector.zeroExtend (n'-n)) . getBV
                else F2Vec . (BitVector.extract (n'-1) 0) . getBV

toList :: F2Mat -> [F2Vec]
toList (F2Mat m n vals) = vals

fromList :: [F2Vec] -> F2Mat
fromList []   = F2Mat 0 0 []
fromList vecs@(x:xs) =
  if all ((n ==) . BitVector.size . getBV) xs
    then F2Mat (length vecs) n vecs
    else error "Vectors have differing lengths"
  where n = BitVector.size $ getBV x

fromVec :: F2Vec -> F2Mat
fromVec x = F2Mat 1 n [x]
  where n = BitVector.size $ getBV x

{- Accessors -}
row :: F2Mat -> Int -> F2Vec
row (F2Mat m n vals) i
  | 0 <= i && i < m = vals !! i
  | otherwise       = error "Row index out of bounds"

index :: F2Mat -> Int -> Int -> Bool
index mat@(F2Mat m n vals) i j
  | 0 <= j && j < n = getBV (row mat i) @. j
  | otherwise       = error "Column index out of bounds"

{- Linear algebra -}

{- Expensive (relatively speaking) -}
transpose :: F2Mat -> F2Mat
transpose (F2Mat m n vals) = F2Mat n m vals'
  where vals'    = map f [0..n-1]
        f j      = F2Vec $ BitVector.fromBits $ foldl' (g j) [] vals
        g j xs v = (getBV v @. j):xs

{- If A is a set of vectors over B, coc A gives the change of coordinates matrix from A to B -}
coc :: [F2Vec] -> F2Mat
coc = transpose . fromList

{- Matrix multiplication -}
mult :: F2Mat -> F2Mat -> F2Mat
mult a@(F2Mat am an avals) b@(F2Mat bm bn bvals)
  | an /= bm  = error $ "Incompatible matrix dimensions:\n" ++ show a ++ "\n\n" ++ show b ++ "\n"
  | otherwise = F2Mat am bn $ map (F2Vec . multRow) avals
    where multRow v       = foldl' (f v) (BitVector.bitVec bn 0) $ zip bvals [0..]
          f v sum (v', i) = if (getBV v) @. i then sum `xor` (getBV v') else sum

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
  | otherwise = F2Mat am an $ map (\(x,y) -> F2Vec $ getBV x `xor` getBV y) $ zip avals bvals

{- Row operations -}
data ROp = Swap Int Int | Add Int Int deriving (Eq, Show)

removeZeroRows :: F2Mat -> F2Mat
removeZeroRows a@(F2Mat _ n vals) = 
  a { vals = filter (not . (BitVector.zeros n ==) . getBV) vals }

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
        newV     = F2Vec $ getBV (head v2) `xor` getBV (vals !! i)
    in
      mat { vals = v1 ++ newV:(tail v2) }
  | otherwise                          = error "Add indices out of bounds"

applyROp :: ROp -> F2Mat -> F2Mat
applyROp (Swap i j) = swapRow i j
applyROp (Add  i j) = addRow  i j
applyROps = foldl' (flip applyROp) 

transposeROp :: ROp -> ROp
transposeROp (Swap i j) = Swap j i
transposeROp (Add  i j) = Add  j i
transposeROps = foldl' (\acc rop -> (transposeROp rop):acc) []

moveAddsIn :: [ROp] -> [ROp]
moveAddsIn xs =
  let move sx []     = reverse sx
      move sx (x:xs) = case x of
        Swap _ _ -> move (x:sx) xs
        Add  _ _ -> move (toLeft x sx) xs
      toLeft y [] = [y]
      toLeft y (x:xs) = case x of
        Swap _ _ -> x:toLeft (apply x y) xs
        Add  _ _ -> y:x:xs
      apply (Swap i j) (Add l k) =
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
  let isOne j (v,_) = getBV v @. j

      zeroAll j y []     = return []
      zeroAll j y (x:xs) =
        if getBV (fst x) @. j
        then do
          tell [Add (snd y) (snd x)]
          xs' <- zeroAll j y xs
          return $ (F2Vec $ getBV (fst y) `xor` getBV (fst x), snd x):xs'
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
              tell [Swap (snd x) (snd y)]
              xs' <- toUpper (j+1) =<< zeroAll j x' (xs ++ y':ys)
              return $ x':xs'
  in
    toUpper 0 (zip vals [0..]) >>= return . F2Mat m n . fst . unzip

toReducedEchelon mat@(F2Mat m n vals) =
  let isOne j (v,_) = getBV v @. j

      zeroAll j y []     = return []
      zeroAll j y (x:xs) =
        if getBV (fst x) @. j
        then do
          tell [Add (snd y) (snd x)]
          xs' <- zeroAll j y xs
          return $ (F2Vec $ getBV (fst y) `xor` getBV (fst x), snd x):xs'
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
              tell [Swap (snd x) (snd y)]
              sx' <- zeroAll j x' sx
              xs' <- zeroAll j x' (xs ++ y':ys)
              toUpper (j+1) (x':sx') xs'
  in
    toUpper 0 [] (zip vals [0..]) >>= return . F2Mat m n . fst . unzip

rank :: F2Mat -> Int
rank mat =
  let (echelon, _) = runWriter $ toEchelon mat in
    foldr (\v tot -> if BitVector.popCount (getBV v) > 0 then tot + 1 else tot) 0 $ vals echelon

columnReduceDry :: F2Mat -> Writer [ROp] Int
columnReduceDry mat@(F2Mat m n vals) =
  let isOne v imap j = getBV v @. (imap ! j)

      swapVals i j imap = Map.insert i (imap ! j) $ Map.insert j (imap ! i) imap

      toLeft j imap [] = return j
      toLeft j imap (x:xs) 
        | j >= n    = return j
        | otherwise = case break (isOne x imap) [j..n-1] of
            (_, [])   -> toLeft j imap xs
            ([], _)   -> toLeft (j+1) imap xs
            (_, j':_) -> do
              tell [Swap j j']
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
  let isOne j v = getBV v @. j

      zeroAll j y []     = []
      zeroAll j y (x:xs) =
        let xs' = zeroAll j y xs in
          if getBV x @. j
          then (F2Vec $ getBV y `xor` getBV x):xs'
          else x:xs'

      toUpper j xs
        | j >= n    =
          let mat'@(F2Mat _ _ vals') = resizeMat m (n+1) mat
              vec  = F2Vec $ BitVector.shift (BitVector.bitVec (n+1) 1) j
          in
            mat' { vals = vals' ++ [vec] }
        | otherwise = case break (isOne j) xs of
            (_, [])      ->
              let vec = F2Vec $ BitVector.shift (BitVector.bitVec n 1) j in
                mat { vals = vals ++ [vec] }
            ([], x:xs)   -> toUpper (j+1) $ zeroAll j x xs
            (x:xs, y:ys) -> toUpper (j+1) $ zeroAll j y (xs ++ x:ys)
  in
    toUpper 0 vals

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
        genSol w = F2Vec $ (getBV x) `xor` (getBV $ multVec ker w)
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
        genSol w = F2Vec $ (getBV x) `xor` (getBV $ multVec ker w)
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
    let genRow = (vector n) >>= return . F2Vec . BitVector.fromBits
    vals <- sequence $ replicate m genRow
    return $ F2Mat m n vals

arbitraryFixedN, arbitraryFixedM :: Int -> Gen F2Mat
arbitraryFixedN n = do
  m <- choose rowRange
  let genRow = (vector n) >>= return . F2Vec . BitVector.fromBits
  vals <- sequence $ replicate m genRow
  return $ F2Mat m n vals
arbitraryFixedM m = do
  n <- choose colRange
  let genRow = (vector n) >>= return . F2Vec . BitVector.fromBits
  vals <- sequence $ replicate m genRow
  return $ F2Mat m n vals

arbitraryFixed :: Int -> Int -> Gen F2Mat
arbitraryFixed m n = do
  let genRow = (vector n) >>= return . F2Vec . BitVector.fromBits
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

tests :: () -> IO ()
tests _ = do
  quickCheck $ prop_TransposeInvolutive
  quickCheck $ prop_ToEchelonIdempotent
  quickCheck $ prop_ToReducedEchelonIdempotent
  quickCheck $ prop_MultAssociative
  quickCheck $ prop_PseudoinverseCorrect
  quickCheck $ prop_TransformMatCorrect

{-
toBlockSingular :: F2Mat -> (F2Mat, Int, [(Int, Int)])
toBlockSingular mat@(F2Mat m n vals rowIx colIx) =
  let returnFirstNonzero mat i j
        | j >= n    = Nothing
        | otherwise =
          if index mat i j
          then Just j
          else returnFirstNonzero mat i (j+1)
      toLeft (mat, xs) i j
        | (i >= m) || (j >= n) = (mat, j, xs)
        | otherwise =
          case returnFirstNonzero mat i j of
            Nothing -> toLeft (mat, xs) (i+1) j
            Just j' -> toLeft (swapCol mat j j', xs) (i+1) (j+1)
      (mat', xs) = toUpperEchelon mat
  in
    toLeft (mat', xs) 0 0

--removeZeroRows :: F2Mat -> F2Mat
--removeZeroRows mat = mat { filter f $ vals mat }

applyOps :: [F2Vec] -> [(Int, Int)] -> [F2Vec]
applyOps = foldr (\(i, j) vecs -> addTo i (vecs !! j) vecs)
  where addTo i v xs = case (i, xs) of
          (_, []) -> []
          (0, x:xs) -> (F2Vec $ (getBV x) `xor` (getBV v)):xs
          (i, x:xs) -> x:(addTo (i-1) v xs)

permute :: Map Int Int -> [a] -> [a]
permute m xs = snd $ unzip $ Map.toList $ Map.map (xs !!) m

permutePairs :: Map Int Int -> [(Int, Int)] -> [(Int, Int)]
permutePairs m = map (\(i, j) -> (m ! i, m ! j))

extend :: Int -> Map Int Int -> Map Int Int
extend n mp = foldl (\mp i -> Map.alter (f i) i mp) mp [0..n-1]
  where f i val = case val of
          Nothing -> Just i
          Just i' -> Just i'

zeroAfterI :: Int -> Int -> Int -> [F2Vec] -> [F2Vec]
zeroAfterI i m n vecs = take i vecs ++ replicate (n - i) (F2Vec $ BitVector.zeros m)

invertMap :: Ord a => Map k a -> Map a k
invertMap = Map.fromList . map swap . Map.toList

pseudoinverse :: [F2Vec] -> [F2Vec]
pseudoinverse vecs =
  let (mat, rank, xs) = toBlockSingular $ fromVecList vecs -- top left rank x rank submatrix is B
      (F2Mat m n vals rIx cIx) = applyPermutations mat
      vecs' = toVecList $ F2Mat n m (zeroAfterI rank n n vals) (colIx mat) cIx
  in
    permute (rowIx mat) $ applyOps (zeroAfterI rank n m vecs') $ permutePairs (invertMap $ rowIx mat) xs

{- Testing -}
instance Arbitrary F2Mat where
  arbitrary = do
    m <- choose (10, 100)
    n <- choose (10, 100)
    let genRow = (vector n) >>= return . F2Vec . BitVector.fromBits
    vals <- sequence $ replicate m genRow
    return $ F2Mat m n vals

idem :: F2Mat -> Bool
idem mat = mat' == ((\(m, _, _) -> m) $ toBlockSingular mat')
  where (mat', rank, xs) = toBlockSingular mat

correctDim :: F2Mat -> Bool
correctDim mat = (m mat) == length vecs && (n mat) == height
  where vecs   = pseudoinverse (toVecList mat)
        height = minimum $ map (BitVector.size . getBV) vecs

isPseudoinverse :: F2Mat -> Bool
isPseudoinverse mat = a == a ~*~ ag ~*~ a
  where a  = toVecList mat
        ag = pseudoinverse a

{-
toF2Mat :: [F2Vec] -> ST s (F2Mat s)
toF2Mat xs = do
  let rw = length xs
      cl = if rw == 0 then 0 else BitVector.size $ getBV $ head xs
  arr <- newListArray (0, rw-1) xs
  return $ F2Mat rw cl arr

--toVecCol :: ST s (F2Mat s) -> [F2Vec]
--toVecCol st =

toUpperEchelon :: F2Mat s -> ST s (STArray s Int F2Vec)
toUpperEchelon (F2Mat m n arr) =
  let swap r r'
        | r == r' = return ()
        | otherwise = do
          vr  <- readArray arr r
          vr' <- readArray arr r'
          writeArray arr r vr'
          writeArray arr r' vr

      add r r' = do
        vr  <- readArray arr r
        vr' <- readArray arr r'
        writeArray arr r $ F2Vec ((getBV vr) `xor` (getBV vr'))

      returnFirstNonzero r c
        | r >= m = return Nothing
        | otherwise = do
          vr <- readArray arr r
          if (getBV vr) @. c
            then return $ Just r
            else returnFirstNonzero (r+1) c

      zeroBelow r c =
        let zeroRow r' = do
              vr  <- readArray arr r
              vr' <- readArray arr r'
              if (getBV vr') @. c
                then writeArray arr r' $ F2Vec ((getBV vr) `xor` (getBV vr'))
                else return ()
        in
         forM_ [r+1..m-1] zeroRow

      toUpper r c
        | (r >= m) || (c >= n) = return r
        | otherwise = do
          rOp <- returnFirstNonzero r c
          case rOp of
            Nothing -> toUpper r (c+1)
            Just r' -> do
              zeroBelow r' c
              swap r r'
              toUpper (r+1) (c+1)

  in do
    toUpper 0 0
    return arr

{- Efficient pseudoinverse computation over GF(2) -}
{- Compute
 -    A | B      A'| B'
 -    ----- -> R ----- C
 -    C | D      0 | 0
 - where A' is upper triangular (i.e. full rank) and
 - R, C are row and column operations, respectively,
 - then return
 -       A'| 0
 -  C^-1 ----- R^-1
 -       0 | 0 
pseudoinverse :: F2Mat s -> ST s (STArray s Int F2Vec)
pseudoinverse (F2Mat m n arr) =
  let swap perm i j
        | i == j = perm
        | otherwise = Map.insert (perm ! i) $ Map.insert (perm ! j) perm

      returnFirstNonzeroRow rowP r c
        | r >= m = return Nothing
        | otherwise = do
          vr <- readArray arr (rowP ! r)
          if (getBV vr) @. c
            then return $ Just r
            else returnFirstNonzero (r+1) c

      returnFirstNonzeroCow rowP colP r c
        | c >= n = return Nothing
        | otherwise = do
          vr <- readArray arr (rowP ! r)
          if (getBV vr) @. (colP ! c)
            then return $ Just c
            else returnFirstNonzero r (c+1)

      zeroBelow rowP xors r c =
        let zeroRow acc r' = do
              vr  <- readArray arr (rowP ! r)
              vr' <- readArray arr (rowP ! r')
              if (getBV vr') @. c
                then do
                  writeArray arr (rowP ! r') $ F2Vec ((getBV vr) `xor` (getBV vr'))
                  return (rowP ! r, rowP ! r'):acc
                else return acc
        in
         foldM zeroRow xors [r+1..m-1]

      toUpper rowP xors r c
        | (r >= m) || (c >= n) = return (rowP, xors)
        | otherwise = do
          rOp <- returnFirstNonzero rowP r c
          case rOp of
            Nothing -> toUpper rowP xors r (c+1)
            Just r' -> do
              xors' <- zeroBelow r' c
              toUpper (swap rowP r r') xors' (r+1) (c+1)

      toBlockSingular rowP colP r c
        | r >= m || c >= n = return $ (rowP, colP)
        | otherwise = do
            cOp <- returnFirstNonzeroCol rowP colP r c
            case cOp of
              Nothing -> toBlockSingular rowP colP (r+1) c
              Just c' -> toBlockSingular rowP (swap colP c c') (r+1) (c+1)

      generateVector rowP c =
        let f r = do
              vr <- readArray arr (rowP ! r)
              return $ (getBV vr) @. c
        in
          mapM f [0..m-1] >>= return . BitVector.fromBits . List.rev

      generateVectors rowP colP =
        let rowP' = Map.map (colP !) rowP
        mapM (generatVector rowP' . colP !) colP

  in do
    toUpper 0 0
    return arr-}

bb :: Int -> Int -> F2Vec
bb i j = F2Vec $ bitVec i j

test m = runSTArray $ (toF2Mat >=> toUpperEchelon) m

idem :: F2VecCol -> Bool
idem (F2VecCol m) = mG == (elems $ test mG)
  where mG = elems $ test m

-}
-}
