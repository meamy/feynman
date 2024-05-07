{-|
Module      : AffineRel
Description : Affine relation domain
Copyright   : (c) Matthew Amy, 2024
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Feynman.Algebra.AffineRel(
  AffineRelation(..),
  top,
  bot,
  eye,
  assign,
  plusEquals,
  disconnect,
  constant,
  meet,
  meets,
  join,
  compose,
  star,
  addPost,
  negatePost,
  addVars,
  mix) where

import Data.Bits
import Feynman.Algebra.Linear

{- | The Affine relation domain is based on [Karr 76] and [Elder et al. 2014].
     An element of the Affine Relation Domain represents a set of constraints
     on the pre- and post- states of a set of /n/ binary variables as the kernel of
     a /2n+1/-column matrix, corresponding to an affine subspace of /F2^(2n)/.
     Meet and Join are the intersection and (smallest enclosing subspace of the)
     union. Elements are kept in reduced echelon form with the left-most bits
     corresponding to the pre-state -}

-- | Affine relation domain
data AffineRelation = ARD {
  vars :: Int,
  mat  :: F2Mat
  } deriving (Eq)

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

-- | Decomposes a bit vector according to the encoding of the ARD
decompose :: Int -> F2Vec -> (F2Vec, F2Vec, F2Vec)
decompose n row = (row@@(n-1,0), row@@(2*n-1,n), row@@(2*n,2*n))

-- | Project out a range
project :: (Int,Int) -> F2Mat -> F2Mat
project (j,i) mat = fromList $ foldMap go (vals $ rowReduce mat) where
  go row = let (a,b,c) = (if i == 0 then bitVec 0 0 else row@@(i-1,0),
                          row@@(j-1,i),
                          row@@(n mat-1,j)) in
    if b /= 0 then [] else [append c a]

-- | Canonicalize a relation
canonicalize :: AffineRelation -> AffineRelation
canonicalize (ARD n a) = checkUnsat (ARD n $ rowReduce a) where
  checkUnsat ar = if (bitI (2*n+1) (2*n) `elem` (vals $ mat ar))
                  then bot n
                  else ar

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

-- | The relation with a single non-identity relation
assign :: Int -> Int -> F2Vec -> AffineRelation
assign n j rel = ARD n (F2Mat n (2*n+1) xs) where
  xs = map go [0..n-1]
  go i
    | i == j    = rel
    | otherwise = appends [bitVec 1 0, bitI n i, bitI n i]

-- | The relation with the single non-identity relation /j'/ = /j/ + /k/
plusEquals :: Int -> Int -> Int -> AffineRelation
plusEquals n j k = ARD n (F2Mat n (2*n+1) xs) where
  xs = map go [0..n-1]
  go i
    | i == j    = appends [bitVec 1 0, bitI n i + bitI n k, bitI n i]
    | otherwise = appends [bitVec 1 0, bitI n i, bitI n i]

-- | The relation which is identity everywhere except /j/
disconnect :: Int -> Int -> AffineRelation
disconnect n j = ARD n (F2Mat n (2*n+1) xs) where
  xs   = map go . filter (/= j) $ [0..n-1]
  go i = appends [bitVec 1 0, bitI n i, bitI n i]

-- | The singleton relation corresponding to a constant variable
constant :: Int -> Int -> Bool -> AffineRelation
constant n j val = ARD n (F2Mat 1 (2*n+1) xs) where
  xs = [appends [bitVec 1 (if val then 1 else 0), bitI n j, bitVec n 0]]

{--------------------------
 Lattice operations
 --------------------------}

-- | Intersection
meet :: AffineRelation -> AffineRelation -> AffineRelation
meet (ARD n mat) (ARD n' mat')
  | n /= n'   = error "Can't meet relations on different sets of variables"
  | otherwise = canonicalize $ ARD n (stack mat mat')

-- | More efficient meet for many constraint sets
meets :: [AffineRelation] -> AffineRelation
meets []     = top 0
meets (x:xs) = canonicalize $ ARD n rel where
  n   = vars x
  rel = foldl (\rel ar -> stack rel (mat ar)) (mat x) xs

-- | Union
join :: AffineRelation -> AffineRelation -> AffineRelation
join (ARD n mat) (ARD n' mat')
  | n /= n'   = error "Can't join relations on different sets of variables"
  | otherwise = ARD n (project (2*n+1,0) $ fromList mat'') where
      mat'' = [append r r | r <- vals mat] ++
              [append (bitVec (2*n+1) 0) r | r <- vals mat']

-- | Sequential composition
compose :: AffineRelation -> AffineRelation -> AffineRelation
compose (ARD n mat) (ARD n' mat')
  | n /= n'   = error "Can't join relations on different sets of variables"
  | otherwise = ARD n (project (2*n,n) $ fromList mat'') where
      mat'' = [append (bitVec n 0) r | r <- vals mat] ++
              [append r (bitVec n 0) | r <- vals mat']

-- | Kleene star (iteration)
star :: AffineRelation -> AffineRelation
star ar = if ar' /= ar then star ar' else ar where
  ar' = join ar (compose ar ar)

{---------------------------
 Ad hoc operations
 ----------------------------}

-- | Directly sets /j'/ = /j'/ + /k'/. Any equation involving /j'/ is
--   now satisfied by /j'/ + /k'/
addPost :: Int -> Int -> AffineRelation -> AffineRelation
addPost j k (ARD v (F2Mat n m vals)) = ARD v (F2Mat n m (map go vals)) where
  go row = if row@.(v+j) then complementBit row (v+k) else row

-- | Directly sets /j'/ = /j'/ + 1. Any equation involving /j'/ is
--   now satisfied by /j'/ + 1
negatePost :: Int -> Int -> AffineRelation -> AffineRelation
negatePost j k (ARD v (F2Mat n m vals)) = ARD v (F2Mat n m (map go vals)) where
  go row = if row@.(v+j) then complementBit row (2*v) else row

-- | Extends the variable set
addVars :: Int -> AffineRelation -> AffineRelation
addVars num (ARD v (F2Mat n m vals)) = ARD v' (F2Mat n m vals') where
  v'     = v + num
  vals'  = map go vals ++ [appends [bitVec 1 0, bitI v' i, bitI v' i] | i <- [v..v'-1]]
  go row =
    let (a,b,c) = decompose v row in
      appends [c, zeroExtend num a, zeroExtend num b]

-- | Directly sets /j'/ to Top
mix :: Int -> AffineRelation -> AffineRelation
mix j (ARD v (F2Mat n m vals)) = ARD v (F2Mat n m (filter go vals)) where
  go row = not $ row@.j
