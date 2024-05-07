{-|
Module      : ARD
Description : Affine relation domain
Copyright   : (c) Matthew Amy, 2024
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Feynman.Algebra.AffineDomain where

import Feynman.Algebra.Linear

import Debug.Trace as Trace

{-
-- | Affine relation domain
data AffineRelation = ARD {
  vars :: Int,
  rels :: Int,
  pre  :: F2Mat,
  post :: F2Mat,
  soln :: F2Mat
  } 

instance Show AffineRelation where
  show ar = foldl (++) "" $ map go [0..(rels ar)-1] where
    go i = "[" ++ show (row (pre ar) i) ++
           "|" ++ show (row (post ar) i) ++
           "|" ++ show (row (soln ar) i) ++ "]\n"

{---------------------------
 Utilities
 ----------------------------}

-- | Stacks two matrices on top of one another
stack :: F2Mat -> F2Mat -> F2Mat
stack (F2Mat m1 n1 vals1) (F2Mat m2 n2 vals2)
  | n1 /= n2 = error "Matrix dimensions don't line up"
  | otherwise = F2Mat (m1+m2) n1 (vals1 ++ vals2)

{---------------------------
 Constructors
 ----------------------------}

-- | The top element. Corresponds to the empty relation.
top :: Int -> AffineRelation
top n = ARD n 0 (F2Mat 0 n []) (F2Mat 0 n []) (F2Mat 0 1 [])

-- | The bottom element. Corresponds to complete relation.
bot :: Int -> AffineRelation
bot n = ARD n 1 (F2Mat 1 n [bitVec n 0]) (F2Mat 1 n [bitVec n 0]) (F2Mat 1 1 [bitVec 1 1])

-- | The identity relation.
eye :: Int -> AffineRelation
eye n = ARD n n (identity n) (identity n) (coc [bitVec n 0])


{--------------------------
 Operations
 --------------------------}

-- | Intersection
meet :: AffineRelation -> AffineRelation -> AffineRelation
meet (ARD n m pr po so) (ARD n' m' pr' po' so') =
  ARD n (m+m') (stack pr pr') (stack po po') (stack so so')

-- | Union
join :: AffineRelation -> AffineRelation -> AffineRelation
join 

-- | Sequential composition
compose :: AffineRelation -> AffineRelation -> AffineRelation
compose 
-}

-- | Affine relation domain
data AffineRelation = ARD {
  vars :: Int,
  mat  :: F2Mat
  } 

instance Show AffineRelation where
  show ar = foldl (++) "" $ map go (vals $ mat ar) where
    n      = vars ar
    go row = "[" ++ show (row@@(n-1,0)) ++
             "|" ++ show (row@@(2*n-1,n)) ++
             "|" ++ show (row@.(2*n)) ++ "]\n"

{---------------------------
 Utilities
 ----------------------------}

-- | Stacks two matrices on top of one another
stack :: F2Mat -> F2Mat -> F2Mat
stack (F2Mat m1 n1 vals1) (F2Mat m2 n2 vals2)
  | n1 /= n2 = error "Matrix dimensions don't line up"
  | otherwise = F2Mat (m1+m2) n1 (vals1 ++ vals2)

-- | Inserts /num/ columns at index /i/
insert :: Int -> Int -> F2Mat -> F2Mat
insert num i (F2Mat m n vals) = F2Mat m (n+num) vals' where
  vals'  = map go vals
  go row = appends [row@@(i-1,0), bitVec num 0, row@@(n-i-1,i)]

{---------------------------
 Constructors
 ----------------------------}

-- | The top element. Corresponds to the empty relation.
top :: Int -> AffineRelation
top n = ARD n (F2Mat 0 (2*n+1) [])

-- | The bottom element. Corresponds to complete relation.
bot :: Int -> AffineRelation
bot n = ARD n (F2Mat 1 (2*n+1) [bitI (2*n+1) (2*n)])

-- | The identity relation.
eye :: Int -> AffineRelation
eye n = ARD n (F2Mat n (2*n+1) xs) where
  xs = [appends [bitVec 1 0, bitI n i, bitI n i] | i <- [0..n-1]]


{--------------------------
 Operations
 --------------------------}

-- | Project out a range
project :: (Int,Int) -> F2Mat -> F2Mat
project (j,i) mat = fromList $ foldMap go (vals $ rowReduce mat) where
  go row = let (a,b,c) = (if i == 0 then bitVec 0 0 else row@@(i-1,0),
                          row@@(j-1,i),
                          row@@(n mat,j)) in
    if b /= 0 then [] else [append c a]

-- | Intersection
meet :: AffineRelation -> AffineRelation -> AffineRelation
meet (ARD n mat) (ARD n' mat')
  | n /= n'   = error "Can't meet relations on different sets of variables"
  | otherwise = ARD n (stack mat mat')

-- | Union
join :: AffineRelation -> AffineRelation -> AffineRelation
join (ARD n mat) (ARD n' mat')
  | n /= n'   = error "Can't join relations on different sets of variables"
  | otherwise = ARD n (project (2*n+1,0) $ fromList mat'') where
      mat'' = [append r r | r <- vals mat] ++ [append (bitVec (2*n+1) 0) r | r <- vals mat']

-- | Sequential composition
compose :: AffineRelation -> AffineRelation -> AffineRelation
compose (ARD n mat) (ARD n' mat')
  | n /= n'   = error "Can't join relations on different sets of variables"
  | otherwise = ARD n (project (2*n,n) $ fromList mat'') where
      mat'' = [append (bitVec n 0) r | r <- vals mat] ++ [append r (bitVec n 0) | r <- vals mat']
