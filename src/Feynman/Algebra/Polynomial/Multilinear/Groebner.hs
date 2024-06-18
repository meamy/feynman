{-|
Module      : Multilinear Groebner Bases
Description : Tools for Groebner basis calculations over multilinear polynomials
Copyright   : (c) Matthew Amy
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Feynman.Algebra.Polynomial.Multilinear.Groebner(
  mvd,
  buchberger,
  addToBasis,
  reduceBasis,
  rbuchberger,
  eliminateVars,
  eliminateAll,
  idealPlus,
  idealTimes,
  idealIntersection
  ) where

import Data.List
import Data.Maybe

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Map (Map)
import qualified Data.Map as Map

import Data.String (IsString(..))

import Feynman.Algebra.Base
import Feynman.Algebra.Polynomial.Multilinear
import qualified Feynman.Util.Unicode as Unicode

import qualified Debug.Trace as Trace

{-------------------------------
 Utilities
 -------------------------------}

-- | Retrieve the leading term
leadingTerm :: (Ord v, Ord (PowerProduct v), Eq r, Num r) => PseudoBoolean v r -> (r, PowerProduct v)
leadingTerm 0 = (0, Monomial Set.empty)
leadingTerm p = head . reverse . toTermList $ p

-- | Retrieve the leading monomial
leadingMonomial :: (Ord v, Ord (PowerProduct v), Eq r, Num r) => PseudoBoolean v r -> (PowerProduct v)
leadingMonomial = snd . leadingTerm

-- | Retrieve the leading coefficient
leadingCoefficient :: (Ord v, Ord (PowerProduct v), Eq r, Num r) => PseudoBoolean v r -> r
leadingCoefficient = fst . leadingTerm

-- | Decompose into the leading term and the remainder
decomposeLeading :: (Ord v, Ord (PowerProduct v), Eq r, Fractional r) => PseudoBoolean v r -> (PseudoBoolean v r, PseudoBoolean v r)
decomposeLeading p = (ofTerm lt, p - ofTerm lt)
  where lt = leadingTerm p

-- | Divide one monomial by another. /m/ must be divisible by /n/
coprime :: (Ord v, Ord (PowerProduct v)) => PowerProduct v -> PowerProduct v -> Bool
coprime m n = Set.intersection (vars m) (vars n) == Set.empty

-- | Determines whether one monomial is divisible by another
divides :: (Ord v, Ord (PowerProduct v)) => PowerProduct v -> PowerProduct v -> Bool
divides m n = vars m `Set.isSubsetOf` vars n

-- | Divide one monomial by another. /m/ must be divisible by /n/
divide :: (Ord v, Ord (PowerProduct v)) => PowerProduct v -> PowerProduct v -> PowerProduct v
divide m n = Monomial $ Set.difference (vars m) (vars n)

{-------------------------------
 Polynomial reduction over Fields
 -------------------------------}

-- | S-polynomial
sPoly :: (Ord v, Ord (PowerProduct v), Eq r, Fractional r) => PseudoBoolean v r -> PseudoBoolean v r -> PseudoBoolean v r
sPoly p q = ofTerm (recip a, divide lc m) * p - ofTerm (recip b, divide lc n) * q
  where (a, m) = leadingTerm p
        (b, n) = leadingTerm q
        lc     = m <> n

-- | Retrieve the first reducible monomial in f with respect to a monomial
reducible :: (Ord v, Ord (PowerProduct v), Eq r, Fractional r) => (r, PowerProduct v) -> PseudoBoolean v r -> Maybe (r, PowerProduct v)
reducible (c, m) = find (\(_d, n) -> m `divides` n) . toTermList

-- | Retrieve the 
leadReducible :: (Ord v, Ord (PowerProduct v), Eq r, Fractional r) => (r, PowerProduct v) -> PseudoBoolean v r -> Maybe (r, PowerProduct v)
leadReducible (c, m) = find (\(_d, n) -> m `divides` n) . take 1 . toTermList

-- | Reduce a polynomial with respect to another
reduce :: (Ord v, Ord (PowerProduct v), Eq r, Fractional r) => PseudoBoolean v r -> PseudoBoolean v r -> PseudoBoolean v r
reduce 0 _ = 0
reduce f g = fromMaybe f $ go f g where
  go f g = do
    let (c, m) = leadingTerm g
    (d, n) <- reducible (c, m) f
    return $ f - (ofTerm (d/c, divide n m)) * g

-- | Reduce a polynomial with respect to another's leading term
leadReduce :: (Ord v, Ord (PowerProduct v), Eq r, Fractional r) => PseudoBoolean v r -> PseudoBoolean v r -> PseudoBoolean v r
leadReduce f g
  | f == 0        = 0
  | m `divides` n = f - (ofTerm (d/c, divide n m)) * g
  | otherwise     = f
  where (c, m) = leadingTerm g
        (d, n) = leadingTerm f

-- | Compute the fixpoint of a reduction
mvd :: (Ord v, Ord (PowerProduct v), Eq r, Fractional r) => PseudoBoolean v r -> [PseudoBoolean v r] -> PseudoBoolean v r
mvd f xs = go f xs where
  go 0 _  = 0
  go f xs =
    let f' = foldl' leadReduce f xs in
      if f == f' then (\(r,p) -> r + go p xs) $ decomposeLeading f
      else go f' xs

-- | Buchberger's iterative algorithm for multilinear polynomial rings
--
--   Rather than include the quadratic polynomials x^2 - x in the basis, we include them implicitly
--   and add the implicit (multilinear) S-polynomials they generate, (p - LT(p))*v - LT(p)
addToBasis :: (Ord v, Ord (PowerProduct v), Eq r, Fractional r) => [PseudoBoolean v r] -> PseudoBoolean v r -> [PseudoBoolean v r]
addToBasis xs p = go (xs ++ [p]) (sPolys p xs) where
  nonzero p q = not $ coprime (leadingMonomial p) (leadingMonomial q)
  sPolys p xs = qfPolys p ++ [sPoly p q | q <- xs, nonzero p q]
  qfPolys     = map (\v -> ofVar v * p) . Set.toList . vars . leadingMonomial
  go basis []     = basis
  go basis (s:xs) = case mvd s basis of
    0  -> go basis xs
    s' -> go (basis ++ [s']) (xs ++ (sPolys s' basis))

-- | Buchberger's algorithm
buchberger :: (Ord v, Ord (PowerProduct v), Eq r, Fractional r) => [PseudoBoolean v r] -> [PseudoBoolean v r]
buchberger = foldl' addToBasis []

-- | Reduces an existing Groebner basis
reduceBasis :: (Ord v, Ord (PowerProduct v), Eq r, Fractional r) => [PseudoBoolean v r] -> [PseudoBoolean v r]
reduceBasis gbasis = go [] gbasis where
  squashCoeff p         = scale (recip $ leadingCoefficient p) p
  go gbasis' []         = gbasis'
  go gbasis' (p:gbasis) = case squashCoeff $ mvd p (gbasis' ++ gbasis) of
    0  -> go gbasis' gbasis
    p' -> go (p':gbasis') gbasis

-- | Buchberger's algorithm, modified to return a reduced Groebner basis
rbuchberger :: (Ord v, Ord (PowerProduct v), Eq r, Fractional r) => [PseudoBoolean v r] -> [PseudoBoolean v r]
rbuchberger = foldl' (\x -> reduceBasis . addToBasis x) []

{-------------------------------
 Elimination theory
 -------------------------------}

-- | Data constructor for elimination contexts
data EVar v = XVar v | YVar v deriving (Eq)

-- | Project a variable out of an elimination context
toVar :: EVar v -> v
toVar (XVar x) = x
toVar (YVar x) = x

instance Ord v => Ord (EVar v) where
  compare s t = compare (toVar s) (toVar t)

instance Show v => Show (EVar v) where
  show = show . toVar

instance Ord v => Elim (EVar v) where
  eliminate (XVar x) = False
  eliminate (YVar x) = True

instance (IsString v) => IsString (EVar v) where
  fromString = YVar . fromString

instance Ord v => Ord (PowerProduct (EVar v)) where
  compare = lexdegOrd

-- | Re-orders according to elimination order
reorder :: (Ord v, Ord (PowerProduct v), Eq r, Fractional r) => [v] -> [PseudoBoolean v r] -> [PseudoBoolean v r]
reorder elim ideal = ideal'' where
  ideal'  = map (rename (\v -> if v `elem` elim then YVar v else XVar v)) $ ideal
  basis   = rbuchberger ideal'
  ideal'' = map (rename toVar) $ basis

-- | Eliminate a set of variables from an ideal
eliminateVars :: (Ord v, Ord (PowerProduct v), Eq r, Fractional r) => [v] -> [PseudoBoolean v r] -> [PseudoBoolean v r]
eliminateVars elim ideal = ideal'' where
  ideal'  = map (rename (\v -> if v `elem` elim then YVar v else XVar v)) $ ideal
  basis   = rbuchberger ideal'
  ideal'' = map (rename (\(XVar v) -> v)) $ project basis
  project = filter (not . any eliminate . vars)

-- | Eliminates all variables mark as elimination from an ideal
eliminateAll :: (Elim v, Ord (PowerProduct v), Eq r, Fractional r) => [PseudoBoolean v r] -> [PseudoBoolean v r]
eliminateAll = filter (not . any eliminate . vars) . rbuchberger

{-------------------------------
 Operations on ideals
 -------------------------------}

-- | Constructs a Groebner basis for the sum of two ideals
idealPlus :: (Ord v, Ord (PowerProduct v), Eq r, Fractional r) => [PseudoBoolean v r] -> [PseudoBoolean v r] -> [PseudoBoolean v r]
idealPlus i j = rbuchberger $ i++j

-- | Constructs a Groebner basis for the product of two ideals
idealTimes :: (Ord v, Ord (PowerProduct v), Eq r, Fractional r) => [PseudoBoolean v r] -> [PseudoBoolean v r] -> [PseudoBoolean v r]
idealTimes i j = rbuchberger $ [p * q | p <- i, q <- j]

-- | Constructs a Groebner basis for the intersection of two ideals
idealIntersection :: (Ord v, Ord (PowerProduct v), Eq r, Fractional r, IsString v) => [PseudoBoolean v r] -> [PseudoBoolean v r] -> [PseudoBoolean v r]
idealIntersection i j = eliminateVars [fromString "_t"] $ ti ++ tj where
  ti = map ((fromString "_t")*) i
  tj = map (((fromString "_t") - 1)*) j

-- Testing

newtype IVar = IVar (String, Integer) deriving (Eq, Ord)

instance Elim IVar where
  eliminate (IVar (a,_)) = a == "t"

instance Show IVar where
  show (IVar (x, i)) = Unicode.sub x i

instance IsString IVar where
  fromString s = IVar (s,0)

instance Ord (PowerProduct IVar) where
  compare = lexdegOrd

x0 = ofVar (IVar ("x",0)) :: SBool IVar
x1 = ofVar (IVar ("x",1)) :: SBool IVar
x2 = ofVar (IVar ("x",2)) :: SBool IVar
x3 = ofVar (IVar ("x",3)) :: SBool IVar
x4 = ofVar (IVar ("x",4)) :: SBool IVar
x5 = ofVar (IVar ("x",5)) :: SBool IVar
x6 = ofVar (IVar ("x",6)) :: SBool IVar
x7 = ofVar (IVar ("x",7)) :: SBool IVar
x8 = ofVar (IVar ("x",8)) :: SBool IVar
x9 = ofVar (IVar ("x",9)) :: SBool IVar

i1 = [x0*x1 + x0 + x1 + 1,
      x2*x3 + x2 + x3 + 1,
      x0*x3,
      x0*x2,
      x1*x3,
      x1*x2 + 1]

y0 = ofVar (IVar ("y",0)) :: PseudoBoolean IVar Double
y1 = ofVar (IVar ("y",1)) :: PseudoBoolean IVar Double
y2 = ofVar (IVar ("y",2)) :: PseudoBoolean IVar Double
y3 = ofVar (IVar ("y",3)) :: PseudoBoolean IVar Double
y4 = ofVar (IVar ("y",4)) :: PseudoBoolean IVar Double
y5 = ofVar (IVar ("y",5)) :: PseudoBoolean IVar Double
y6 = ofVar (IVar ("y",6)) :: PseudoBoolean IVar Double
y7 = ofVar (IVar ("y",7)) :: PseudoBoolean IVar Double
y8 = ofVar (IVar ("y",8)) :: PseudoBoolean IVar Double
y9 = ofVar (IVar ("y",9)) :: PseudoBoolean IVar Double

i2 = [y0*y1 + y0 + y1 + 1,
      y2*y3 + y2 + y3 + 1,
      y0*y3,
      y0*y2,
      y1*y3,
      y1*y2 + 1]

-- Hoare ex testing
idealinit = [x0*x1 + x3 + x5,
             x0*x1 + x5 + x7,
             x0*x1 + x7 + x9]

idealpart = [x0*x1 + x3 + x5,
             x0*x1 + x5 + x7,
             x0*x1 + x7 + x9,
             x5 + x9,
             x0*x1 + x3 + x9]

idealfull = [x0*x1 + x3 + x5,
             x0*x1 + x5 + x7,
             x0*x1 + x7 + x9,
             x3 + x7,
             x4 + x8,
             x0*x1 + x3 + x9]
  
idealunion = [x0*x1 + x3 + x5,
              x0*x1 + x5 + x7,
              x0*x1 + x7 + x9,
              x0*x1 + x3 + x9]

parities = [x0, x1, x4, x0+x1, x0+x4, x1+x4, x0+x1+x4,
            x0, x1, x6, x0+x1, x0+x6, x1+x6, x0+x1+x6,
            x0, x1, x8, x0+x1, x0+x8, x1+x8, x0+x1+x8]

poly = x0*x1*x4 + x3*x4 + x4*x5 + x0*x1*x6 + x5*x6 + x6*x7 + x0*x1*x8 + x7*x8 + x8*x9
poly' = x0*x1*x4 + x3*x4 + x4*x5 + x4*x7 + x0*x1*x6 + x5*x6 + x6*x7 + x6*x7 + x0*x1*x8 + x7*x8 + x8*x9

numOccurrence :: Ord a => [a] -> Map a Int
numOccurrence = foldr go Map.empty where
  go a = Map.insertWith (+) a 1


-- Elimination tests
idealElim = [x0 + x1, x1 + x2, x2 + x0]

-- Sum and product tests
t1 = [x0 + x1, x2 + x3]
t2 = [x0 + x3, x1 + x2]
