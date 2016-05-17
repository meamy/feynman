{-# LANGUAGE FlexibleContexts #-}

module Linear where

import Control.Monad
import Control.Monad.ST
import Data.Array.ST
import Data.Array (elems)

import Data.BitVector (xor, (@.), bitVec)
import qualified Data.BitVector as BitVector

import Test.QuickCheck

newtype F2Vec    = F2Vec    { getBV  :: BitVector.BV } deriving (Eq)
newtype F2VecCol = F2VecCol { getMat :: [F2Vec] } deriving (Eq,Show)

instance Show F2Vec where
  show (F2Vec b) = BitVector.showBin b

instance Arbitrary F2VecCol where
  arbitrary = do
    rows <- choose (100, 100)
    cols <- choose (100, 100)
    let genRow = (vector cols) >>= return . F2Vec . BitVector.fromBits
    m <- sequence $ replicate rows genRow
    return $ F2VecCol m

data F2Mat s = F2Mat {
  rows :: Int,
  cols :: Int,
  vals :: STArray s Int F2Vec
  }

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
 -       0 | 0 -}
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
    return arr

bb :: Int -> Int -> F2Vec
bb i j = F2Vec $ bitVec i j

test m = runSTArray $ (toF2Mat >=> pseudoinverse) m

idem :: F2VecCol -> Bool
idem (F2VecCol m) = mG == (elems $ test mG)
  where mG = elems $ test m
