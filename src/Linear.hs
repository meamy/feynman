{-# LANGUAGE FlexibleContexts #-}

module Linear where

import Data.List
import Control.Monad
import qualified Data.Tuple as Tuple

import Data.Map (Map, (!))
import qualified Data.Map as Map

import Data.BitVector (BV, (@.), xor)
import qualified Data.BitVector as BitVector

import Test.QuickCheck

newtype F2Vec = F2Vec { getBV :: BV } deriving (Eq)

instance Show F2Vec where
  show (F2Vec b) = map (f . (b @.)) [0..BitVector.size b - 1]
    where f b = if b then '1' else '0'

bb :: Int -> Int -> F2Vec
bb i j = F2Vec $ BitVector.bitVec i j

{- Matrices over GF(2) -}
data F2Mat = F2Mat {
  m :: Int,
  n :: Int,
  vals :: [F2Vec],
  rowIx :: Map Int Int,
  colIx :: Map Int Int } deriving (Eq)

row :: F2Mat -> Int -> F2Vec
row mat = ((vals mat) !!) . ((rowIx mat) !)

index :: F2Mat -> Int -> Int -> Bool
index mat i j = (getBV $ row mat i) @. ((colIx mat) ! j)

f2Mat :: Int -> Int -> [F2Vec] -> F2Mat
f2Mat m n vals = F2Mat m n vals rowIx colIx
  where rowIx = Map.fromList [(i, i) | i <- [0..m-1]]
        colIx = Map.fromList [(j, j) | j <- [0..n-1]]

instance Show F2Mat where
  show mat@(F2Mat m n vals rowIx colIx) =
    intercalate "\n" $ map (\i -> map (f . (index mat i)) [0..n-1]) [0..m-1]
    where f b = if b then '1' else '0'

instance Arbitrary F2Mat where
  arbitrary = do
    m <- choose (10, 100)
    n <- choose (10, 100)
    let genRow = (vector n) >>= return . F2Vec . BitVector.fromBits
    vals <- sequence $ replicate m genRow
    return $ f2Mat m n vals

{- Converts a list of vectors (column-major) into a matrix (row-major).
   Truncates all vectors to the length of the shortest vector -}
fromVecList :: [F2Vec] -> F2Mat
fromVecList vecs = f2Mat m n vals
  where m = minimum $ map (BitVector.size . getBV) vecs
        n = length vecs
        f i = foldl (\xs v -> (getBV v @. i):xs) [] vecs
        vals = map (F2Vec . BitVector.fromBits . f) [0..m-1]

toVecList :: F2Mat -> [F2Vec]
toVecList (F2Mat m n vals rowIx colIx) = map (F2Vec . f) [colIx ! j | j <- [0..n-1]]
  where f j = BitVector.fromBits $ map (\i -> getBV (vals !! i) @. j) [rowIx ! i | i <- reverse [0..m-1]]

{- Applies the row and column permutations -}
applyPermutations :: F2Mat -> F2Mat
applyPermutations mat@(F2Mat m n vals rowIx colIx) =
  mat { vals = vals', rowIx = rowIx', colIx = colIx' }
  where rowIx' = Map.fromList [(i, i) | i <- [0..m-1]]
        colIx' = Map.fromList [(j, j) | j <- [0..n-1]]
        vals'  = map (F2Vec . vec' . (vals !!)) $ Map.elems rowIx
        vec' v =
          let bits = BitVector.toBits (getBV v)
              f i  = bits !! (n-1-i)
          in
            BitVector.fromBits $ reverse $ map f $ Map.elems colIx

{- Row & column operations -}
swapRow :: F2Mat -> Int -> Int -> F2Mat
swapRow mat i j
  | i == j    = mat
  | otherwise = mat { rowIx = Map.insert i (perm ! j) $ Map.insert j (perm ! i) perm }
  where perm = rowIx mat

swapCol :: F2Mat -> Int -> Int -> F2Mat
swapCol mat i j
  | i == j    = mat
  | otherwise = mat { colIx = Map.insert i (perm ! j) $ Map.insert j (perm ! i) perm }
  where perm = colIx mat

addRow :: F2Mat -> Int -> Int -> (F2Mat, (Int, Int))
addRow mat i j =
  let i' = (rowIx mat) ! i
      j' = (rowIx mat) ! j
      addTo i v xs = case (i, xs) of
        (_, []) -> []
        (0, x:xs) -> (F2Vec $ (getBV x) `xor` (getBV v)):xs
        (i, x:xs) -> x:(addTo (i-1) v xs)
  in
    (mat { vals = addTo j' (vals mat !! i') (vals mat) }, (i', j'))

{- Linear algebra operations -}
(~*) :: [F2Vec] -> F2Vec -> F2Vec
a ~* b = F2Vec $ foldl f (BitVector.bitVec m 0) (zip a [0..])
  where f sum (v, i) = if (getBV b) @. i then sum `xor` (getBV v) else sum
        m = minimum $ map (BitVector.size . getBV) a

(~*~) :: [F2Vec] -> [F2Vec] -> [F2Vec]
a ~*~ b = map (a ~*) b
  
toUpperEchelon :: F2Mat -> (F2Mat, [(Int, Int)])
toUpperEchelon mat@(F2Mat m n vals rowIx colIx) =
  let returnFirstNonzero mat i j
        | i >= m    = Nothing
        | otherwise =
          if index mat i j
          then Just i
          else returnFirstNonzero mat (i+1) j
      zeroAll mat i j =
        let zeroRow (mat, xs) i' =
              if i /= i' && index mat i' j
              then (\(m, p) -> (m, p:xs)) $ addRow mat i i'
              else (mat, xs)
        in
         foldl zeroRow (mat, []) [0..m-1]
      toUpper (mat, xs) i j
        | (i >= m) || (j >= n) = (mat, xs)
        | otherwise =
          case returnFirstNonzero mat i j of
            Nothing -> toUpper (mat, xs) i (j+1)
            Just i' ->
              let (mat', xs') = zeroAll mat i' j in
                toUpper (swapRow mat' i i', xs' ++ xs) (i+1) (j+1)
  in 
    toUpper (mat, []) 0 0

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
invertMap = Map.fromList . map Tuple.swap . Map.toList

pseudoinverse :: [F2Vec] -> [F2Vec]
pseudoinverse vecs =
  let (mat, rank, xs) = toBlockSingular $ fromVecList vecs -- top left rank x rank submatrix is B
      (F2Mat m n vals rIx cIx) = applyPermutations mat
      vecs' = toVecList $ F2Mat n m (zeroAfterI rank n n vals) (colIx mat) cIx
  in
    permute (rowIx mat) $ applyOps (zeroAfterI rank n m vecs') $ permutePairs (invertMap $ rowIx mat) xs

-- Tests
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
