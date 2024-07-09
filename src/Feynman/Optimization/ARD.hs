{-|
Module      : ARD
Description : Affine relation domain
Copyright   : (c) Matthew Amy, 2024
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Feynman.Optimization.ARD(
  AffineRelation(..),
  top,
  bot,
  eye,
  addPost,
  negatePost,
  clearPost,
  addVars,
  makeExplicit,
  projectTemporaries,
  meet,
  meets,
  join,
  compose,
  star,
  makeExplicitFF,
  composeFF,
  joinFF,
  starFF,
  cOp,
  projectVector,
  compose'
  ) where

import Data.Bits
import Data.Coerce (coerce)

import Feynman.Algebra.Linear

{-| The Affine relation domain is based on [Karr 76] and [Elder et al. 2014].
    An element of the Affine Relation Domain represents a set of constraints
    on a set of /n/ + /m/ binary variables, where the constraints are stored in
    an /m/ by /n+1/ matrix /(A,c)/. The interpretation of such an element is the
    set of constraints /x' = Ax + c/.

    Note when /n/=/m/, this set of constraints has the representation [I|A|c] in
    the KS domain of Elder et al., stored in post-major order. More generally, we
    can think of our domain as the KS domain with 3 vocabularies: X', X, and
    temporaries Y. We arrive at our representation from the KS domain representation
    of these vocabularies [X'|X|Y|c] and drop X' from the representation as
    we maintain that X' always has full rank throughout our analysis.
-}

-- | Affine relation domain

newtype AffineRelation = ARD { unARD :: F2Mat } deriving (Eq)

instance Show AffineRelation where
  show ar = foldl (++) "" $ map go (rows ar) where
    n      = vars ar
    go row = "[" ++ show (row@@(n-1,0)) ++ "|" ++ show (row@.(n)) ++ "]\n"

{---------------------------
 Accessors
 ----------------------------}

-- | Returns the number of vars tracked
vars :: AffineRelation -> Int
vars = (+ (-1)) . n . unARD

-- | Returns the rows or constraints of the matrix
rows :: AffineRelation -> [F2Vec]
rows = vals . unARD

-- | Gets the postcondition of a particular variable
getPost :: Int -> AffineRelation -> F2Vec
getPost i = (!!i).rows

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

-- | Project out a range
project :: (Int,Int) -> F2Mat -> F2Mat
project (j,i) mat = fromList $ foldMap go (vals $ rowReduce mat) where
  go row = let (a,b,c) = (if i == 0 then bitVec 0 0 else row@@(i-1,0),
                          row@@(j-1,i),
                          row@@(n mat-1,j)) in
    if b /= 0 then [] else [append c a]

-- | Canonicalize a relation
canonicalize :: AffineRelation -> AffineRelation
canonicalize = checkUnsat . (coerce rowReduce) where
  checkUnsat ar =
    let n = vars ar in
      if (bitI (n+1) n) `elem` (rows ar)
      then bot n
      else ar

{---------------------------
 Constructors
 ----------------------------}

-- | The top element. Corresponds to the empty relation.
top :: Int -> AffineRelation
top n = ARD (F2Mat 0 (n+1) [])

-- | The bottom element. Corresponds to complete relation.
bot :: Int -> AffineRelation
bot n = ARD (F2Mat 1 (n+1) [bitI (n+1) (n)])

-- | The identity relation.
eye :: Int -> AffineRelation
eye n = ARD (F2Mat n (n+1) xs) where
  xs = [bitI (n+1) i | i <- [0..n-1]]

{---------------------------
 Operations
 ----------------------------}

-- | Extends the variable set
addVars :: Int -> AffineRelation -> AffineRelation
addVars num (ARD (F2Mat m n vals)) = ARD (F2Mat (m+num) n' vals') where
  n'     = n + num
  vals'  = map go vals ++ [bitI n' (i-1) | i <- [n..n'-1]]
  go row = appends [row@@(n-1,n-1), bitVec num 0, row@@(n-2,0)]

-- | Negates the postcondition associated to row /j/ (/j'/ <- /j'/ + 1)
negatePost :: Int -> AffineRelation -> AffineRelation
negatePost j (ARD (F2Mat m n vals)) = ARD (F2Mat m n (map go $ zip vals [0..])) where
  go (row,i) = if i == j then complementBit row (n-1) else row

-- | Adds /k/ to /j/ (corresp. to the relation /j'/ <- /j'/ + /k'/)
addPost :: Int -> Int -> AffineRelation -> AffineRelation
addPost j k (ARD (F2Mat m n vals)) = ARD (F2Mat m n (map go $ zip vals [0..])) where
  go (row,i) = if i == j then row + vals!!k else row

-- | Swaps /j/ and /k/ in the postcondition (/j'/ <- /k'/, /k'/ <- /j'/)
swapPost :: Int -> Int -> AffineRelation -> AffineRelation
swapPost j k (ARD (F2Mat m n vals)) = ARD (F2Mat m n (map go $ zip vals [0..])) where
  go (row,i)
    | i == j    = vals!!k
    | i == k    = vals!!j
    | otherwise = row

-- | Resets a variable to 0 (/j'/ <- /0/)
clearPost :: Int -> AffineRelation -> AffineRelation
clearPost j (ARD (F2Mat m n vals)) = ARD (F2Mat m n (map go $ zip vals [0..])) where
  go (row,i) = if i == j then bitVec n 0 else row

-- | Converts an (implicit) two-vocabulary relation to an explicit one
makeExplicit :: AffineRelation -> AffineRelation
makeExplicit (ARD (F2Mat m n vals)) = ARD (F2Mat m (n+m) vals') where
  vals' = [append r (bitI m i) | (r,i) <- zip vals [0..]]

-- | Sets /j/ to a fresh variable (/j'/ <- /x/)
setFresh :: Int -> AffineRelation -> AffineRelation
setFresh j (ARD (F2Mat m n vals)) = ARD (F2Mat m n' (map go $ zip vals [0..])) where
  n'         = n + 1
  go (row,i) = if i == j
               then bitI n' (n-1)
               else (appends [row@@(n-1,n-1), bitVec 1 0, row@@(n-2,0)])

-- | Projects out temporary variables, needed for loop summarization
projectTemporaries :: AffineRelation -> AffineRelation
projectTemporaries ar@(ARD (F2Mat m n vals))
  | n == 2*m + 1 = ar
  | otherwise    = ARD $ project (n-m-1,m) (F2Mat m n vals)

{--------------------------
 Lattice operations
 --------------------------}

-- | Intersection
meet :: AffineRelation -> AffineRelation -> AffineRelation
meet (ARD mat) (ARD mat')
  | n mat /= n mat' = error "Can't meet relations on different sets of variables"
  | otherwise       = canonicalize $ ARD (stack mat mat')

-- | More efficient meet for many constraint sets
meets :: [AffineRelation] -> AffineRelation
meets []     = top 0
meets (x:xs) = canonicalize $ ARD rel where
  n   = vars x
  rel = foldl (\rel ar -> stack rel (unARD ar)) (unARD x) xs

-- | Sequential composition
compose :: AffineRelation -> AffineRelation -> AffineRelation
compose ar1 ar2
  | vars ar1 /= vars ar2 = error $ "Can't compose relations on different sets of variables:\nRel1: " ++ show ar1 ++ "\nRel2: " ++ show ar2
  | otherwise            = ARD (project (2*v,v) $ fromList mat'') where
      v = (vars ar1) `div` 2
      mat'' = [appends [r@@(2*v,2*v), bitVec v 0, r@@(2*v-1,0)] | r <- rows ar2] ++
              [append r (bitVec v 0) | r <- rows ar1]

-- | Union
join :: AffineRelation -> AffineRelation -> AffineRelation
join ar1 ar2
  | vars ar1 /= vars ar2 = error $ "Can't join relations on different sets of variables:\nRel1: " ++ show ar1 ++ "\nRel2: " ++ show ar2
  | otherwise            = ARD (project (v+1,0) $ fromList constraints) where
      v = vars ar1
      constraints = [append r r | r <- rows ar1] ++ [append (bitVec (v+1) 0) r | r <- rows ar2]

-- | Kleene star (iteration)
star :: AffineRelation -> AffineRelation
star ar = if ar' /= ar then star ar' else ar where
  ar' = join ar (compose ar ar)

{--------------------------
 Fast-forward operators
 --------------------------}

-- | Converts a relation [X|Y|c] to forward-canonicalization [X|X']
--   projecting out any temporaries Y
makeExplicitFF :: AffineRelation -> AffineRelation
makeExplicitFF (ARD (F2Mat m n vals))
  | m == n-1 =
    let vals' = [appends [r@@(n-1,n-1), bitI m i, r@@(m-1,0)] | (r,i) <- zip vals [0..]] in
      canonicalize $ ARD $ fromList vals'
  | otherwise =
    let t = n - 1 - m
        vals' = [appends [r@@(n-1,n-1), bitI m i, r@@(m-1,0), r@@(n-2,m)] | (r,i) <- zip vals [0..]]
    in
      ARD $ project (t,0) $ fromList vals' where

-- | Sequential composition in the [X|X'] order
composeFF :: AffineRelation -> AffineRelation -> AffineRelation
composeFF ar1 ar2
  | vars ar1 /= vars ar2 = error $ "Can't compose relations on different sets of variables:\nRel1: " ++ show ar1 ++ "\nRel2: " ++ show ar2
  | otherwise            = ARD (project (2*v,v) $ fromList mat'') where
      v = (vars ar1) `div` 2
      mat'' = [appends [r@@(2*v,2*v), bitVec v 0, r@@(2*v-1,0)] | r <- rows ar1] ++
              [append r (bitVec v 0) | r <- rows ar2]

-- | Union in the [X|X'] order
joinFF :: AffineRelation -> AffineRelation -> AffineRelation
joinFF ar1 ar2
  | vars ar1 /= vars ar2 = error "Can't join relations on different sets of variables"
  | otherwise            = ARD (project (v+1,0) $ fromList constraints) where
      v = vars ar1
      constraints = [append r r | r <- rows ar1] ++ [append (bitVec (v+1) 0) r | r <- rows ar2]

-- | Kleene star (iteration) in the [X|X'] order
starFF :: AffineRelation -> AffineRelation
starFF ar = if ar' /= ar then star ar' else ar where
  ar' = joinFF ar (composeFF ar ar)


-- | Forward-Backward canonicalization operator. Given two domain elements with schemes
--
--   A1: X' | Y  | X | a (backward)
--   A2: Z  | Z' | b     (forward)
--
--   we generate the forward constraint system
--
--   A2.A1 = X' | Y | X | 0  | a
--           Z  | 0 | 0 | Z' | b
--
--   Projecting onto Z' existentially quantifies X, Y, X'=Z and gives a representation,
--   if it exists, over the variables of Z'
cOp :: AffineRelation -> AffineRelation -> AffineRelation
cOp (ARD (F2Mat m n vals)) (ARD (F2Mat m' n' vals')) = ARD (project (vFin,0) $fromList vals'') where
  vFin = (n' - 1) `div` 2
  vals'' = [appends [r@@(n-1,n-1), bitVec vFin 0, r@@(n-2,0)] | r <- vals] ++
           [appends [r@@(n'-1,vFin), bitVec (n - 1 - vFin) 0, r@@(vFin-1,0)] | r <- vals']

-- | Fast-forward a vector over the pre-conditions to a vector over the postconditions, if such
--   a vector exists
projectVector :: AffineRelation -> F2Vec -> Maybe F2Vec
projectVector (ARD mat) vec = if vec'@@(v-2,0) /= 0
                              then Nothing
                              else Just (vec'@@(v'+v-1,v-1))
  where v    = width vec
        v'   = (n mat) - v
        vec' = reduceVector mat $ appends [vec@@(v-1,v-1), bitVec v' 0, vec@@(v-2,0)]
  

-- | Full-rank composition. Assures that every variable in X' has a representation.
--
--   Given the (full-rank) relation
--
--   A1: X' | Y  | X | a (backward)
--
--   And the not necessarily full-rank relation
--
--   A2: X'' | X' | b
--
--   we generate the constraint system
--
--   A2.A1 = I | I  | 0 | 0 | 0 | 0
--           0 | X''| X'| 0 | 0 | b
--           0 | 0  | X'| Y | X | a
--
--   Projecting away X' canonicalizes X'' over the relations between X'' Y and X,
--   eliminating X'' first
--
compose' :: AffineRelation -> AffineRelation -> F2Mat
compose' (ARD (F2Mat m n mat)) (ARD (F2Mat m' n' mat')) = fromList vals'' where
  -- The number of program variables
  v = m

  -- The initial constraint system
  cons = [appends [bitVec n 0, bitI v i, bitI v i] | i <- [0..v-1]] ++
         [appends [r@@(n'-1,n'-1), bitVec (n-v-1) 0, r@@(n'-2,0), bitVec v 0] | r <- mat'] ++
         [appends [r, bitVec (2*v) 0] | r <- mat]

  -- The reduced relation
  cons' = rowReduce $ fromList cons

  -- The final matrix
  vals'' = [r@@(width r - 1, v) | r <- take v $ vals cons']
