{-# LANGUAGE ViewPatterns #-}

{-|
Module      : Concrete
Description : A concrete path sum for Clifford+Rz circuits
Copyright   : (c) Matthew Amy, 2020
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Feynman.Algebra.Pathsum.Concrete where

import qualified Feynman.Util.Unicode as U
import Feynman.Algebra.Base
import Feynman.Algebra.Polynomial.Multilinear

{-----------------------------------
 Variables
 -----------------------------------}

-- | Variables are either input variables or path variables. The distinction
--   is due to the binding structure of our pathsum representation, and moreover
--   improves readability
data Var = IVar !Integer | PVar !Integer deriving (Eq, Ord)

instance Show Var where
  show (IVar i) = U.sub "x" i
  show (PVar i) = U.sub "y" i

-- | Convenience function for the string representation of the 'i'th input variable
ivar :: Integer -> String
ivar = show . IVar

-- | Convenience function for the string representation of the 'i'th path variable
pvar :: Integer -> String
pvar = show . PVar

-- | Construct an integer shift for input variables
shiftI :: Integer -> (Var -> Var)
shiftI i = shiftAll i 0

-- | Construct an integer shift for path variables
shiftP :: Integer -> (Var -> Var)
shiftP j = shiftAll 0 j

-- | General shift. Constructs a substitution from shift values for I and P
shiftAll :: Integer -> Integer -> (Var -> Var)
shiftAll i j = go
  where go (IVar i') = IVar (i + i')
        go (PVar j') = PVar (j + j')

-- | Path sums of the form
--   \(\frac{1}{\sqrt{2}^k}\sum_{y\in\mathbb{Z}_2^m}e^{i\pi P(x, y)}|f(x, y)\rangle\)
data Pathsum g = Pathsum {
  sde       :: !Integer,
  inDeg     :: !Integer,
  outDeg    :: !Integer,
  pathVars  :: !Integer,
  phasePoly :: !PhasePolynomial Var g,
  outVals   :: ![SBool Var]
  } deriving (Eq)

instance (Show g, Eq g, Periodic g) => Show (Pathsum a) where
  show sop = inputstr ++ scalarstr ++ sumstr ++ amplitudestr ++ statestr
    where inputstr = case inDeg sop of
            0 -> ""
            1 -> U.ket (ivar 0) ++ " " ++ U.mapsto ++ " "
            2 -> U.ket (ivar 0 ++ ivar 1) ++ " " ++ U.mapsto ++ " "
            j -> U.ket (ivar 0 ++ U.dots ++ ivar (j-1)) ++ " " ++ U.mapsto ++ " "
          scalarstr = case sde sop of
            0 -> ""
            k -> U.sup ("1/(" ++ U.rttwo ++ ")") k
          sumstr = case pathVars sop of
            0 -> ""
            1 -> U.sum ++ "[" ++ pvar 0 ++ "]"
            2 -> U.sum ++ "[" ++ pvar 0 ++ pvar 1 ++ "]"
            j -> U.sum ++ "[" ++ pvar 0 ++ U.dots ++ pvar (j-1) ++ "]"
          amplitudestr = case order (phasePoly sop) of
            0 -> U.e ++ "^" ++ U.i ++ U.pi ++ "{" ++ show (phasePoly sop) ++ "}"
            1 -> ""
            2 -> "(-1)^{" ++ show (power 2 $ phasePoly sop) ++ "}"
            4 -> U.i ++ "^{" ++ show (power 4 $ phasePoly sop) ++ "}"
            8 -> U.omega ++ "^{" ++ show (
                                          

      is = concatMap (\(v, b) -> if b then v else "0") . Map.toList $ inVals sop
          sc = case sde sop of
                 0 -> ""
                 i -> "1/sqrt(2)^" ++ show i ++ " "
          sm = case pathVars sop of
                 [] -> ""
                 xs -> "Sum[" ++ (intercalate "," . map (\i -> pathVar i) $ xs) ++ "] "
          ph = case poly sop == zero of
                 True  -> ""
                 False -> "e^i*pi*" ++ showPoly (poly sop)
          os = concatMap showPoly $ Map.elems $ outVals sop
          showPoly p
            | isMono (simplify p)  = show p
            | otherwise = "(" ++ show p ++ ")"

pathVar :: Int -> ID
pathVar i = "p" ++ show i

internalPaths :: Pathsum a -> [Int]
internalPaths sop = filter f $ pathVars sop
  where f i = all (not . (appearsIn $ pathVar i)) . Map.elems $ outVals sop

{- Constructors -}

identity0 :: Pathsum a
identity0 = Pathsum 0 Map.empty [] zero Map.empty

identity :: [ID] -> Pathsum a
identity vars = Pathsum {
  sde      = 0,
  inVals   = Map.fromList $ zip vars [True | v <- vars],
  pathVars = [],
  poly     = zero,
  outVals  = Map.fromList $ zip vars [ofVar v | v <- vars]
  }

identityTrans :: Map ID Bool -> Pathsum a
identityTrans inp = Pathsum {
  sde      = 0,
  inVals   = inp,
  pathVars = [],
  poly     = zero,
  outVals  =
      let f v False = zero
          f v True  = ofVar v
      in
        Map.mapWithKey f inp
  }

blank :: [ID] -> Pathsum a
blank vars = Pathsum {
  sde      = 0,
  inVals   = Map.fromList $ zip vars [False | i <- vars],
  pathVars = [],
  poly     = zero,
  outVals  = Map.fromList $ zip vars [zero | i <- vars]
  }

ofKet :: Map ID Bool -> Pathsum a
ofKet ket = Pathsum {
  sde      = 0,
  inVals   = Map.map (\_ -> False) ket,
  pathVars = [],
  poly     = zero,
  outVals  = Map.map constant ket
  }


{- Operators -}
compose :: (Eq a, Num a) => Pathsum a -> Pathsum a -> Pathsum a
compose u v
  | u == mempty = v
  | v == mempty = u
  | otherwise   =
    let varShift = case null (pathVars v) of
          True  -> 0
          False -> maximum ([-1] ++ pathVars u) - minimum (pathVars v) + 1
        sub =
          let f v True  = Map.insert v $ Map.findWithDefault (ofVar v) v (outVals u)
              f v False = error $ "Composing " ++ v ++ " with |0> on the right"
              initMap = Map.fromList [(pathVar i, ofVar $ pathVar $ i + varShift) | i <- pathVars v]
          in
            Map.foldrWithKey f initMap (inVals v)
    in Pathsum {
      sde      = sde u + sde v,
      inVals   = Map.union (inVals u) (inVals v),
      pathVars = pathVars u ++ map (+ varShift) (pathVars v),
      poly     = poly u + substMany sub (poly v),
      outVals  = Map.union (Map.map (simplify . substMany sub) $ outVals v) (outVals u)
      }

restrict :: (Eq a, Num a) => Pathsum a -> Map ID Bool -> Pathsum a
restrict sop bra = foldl' f sop $ Map.keys bra
  where f sop x =
          let x' = (outVals sop)!x in
            if degree x' < 1
            then
              if (simplify x') == (simplify $ constant (bra!x))
              then sop
              else error "Zero amplitude on target state" --Pathsum 0 Map.empty [] zero Map.empty
            else
              case find ((`elem` (map pathVar $ pathVars sop)) . fst) $ solveForX (constant (bra!x) + x') of
                Nothing        -> error $ "Can't reify " ++ (show $ constant (bra!x) + x') ++ " = 0"
                Just (y, psub) -> sop { pathVars = pathVars sop \\ [read $ tail y],
                                  poly     = simplify . subst y psub $ poly sop,
                                  outVals  = Map.map (simplify . subst y psub) $ outVals sop }

tryRestrict :: (Eq a, Num a) => Pathsum a -> Map ID Bool -> Pathsum a
tryRestrict sop bra = foldl' f sop $ Map.keys bra
  where f sop x =
          let x' = (outVals sop)!x in
            if degree x' < 1
            then
              if x' == constant (bra!x)
              then sop
              else Pathsum 0 Map.empty [] zero Map.empty
            else
              case find ((`elem` (map pathVar $ pathVars sop)) . fst) $ solveForX (constant (bra!x) + x') of
                Nothing        -> sop
                Just (y, psub) -> sop { pathVars = pathVars sop \\ [read $ tail y],
                                  poly     = simplify . subst y psub $ poly sop,
                                  outVals  = Map.map (simplify . subst y psub) $ outVals sop }

restrictGeneral :: (Eq a, Num a) => Pathsum a -> Map ID (Multilinear Bool) -> Pathsum a
restrictGeneral sop bra = foldl' f sop $ Map.keys bra
  where f sop x =
          let x' = (outVals sop)!x in
            if (simplify x') == (simplify $ bra!x)
            then sop
            else
              case find ((`elem` (map pathVar $ pathVars sop)) . fst) $ solveForX (bra!x + x') of
                Nothing        -> error $ "Can't reify " ++ (show $ bra!x + x') ++ " = 0"
                Just (y, psub) -> sop { pathVars = pathVars sop \\ [read $ tail y],
                                  poly     = simplify . subst y psub $ poly sop,
                                  outVals  = Map.map (simplify . subst y psub) $ outVals sop }
      
instance (Eq a, Num a) => Semigroup (Pathsum a) where
  a <> b = compose a b

instance (Eq a, Num a) => Monoid (Pathsum a) where
  mempty  = identity0
  mappend = compose

{- Implementations -}

newtype Z8 = Z8 { inject :: Int } deriving (Eq)

instance Show Z8 where
  show (Z8 x) = show x

instance Num Z8 where
  (Z8 x) + (Z8 y) = Z8 $ (x + y) `mod` 8
  (Z8 x) * (Z8 y) = Z8 $ (x * y) `mod` 8
  negate (Z8 x)   = Z8 $ 8 - x
  abs (Z8 x)      = Z8 $ x `mod` 8
  signum (Z8 x)   = Z8 $ signum x
  fromInteger i   = Z8 $ fromIntegral $ i `mod` 8

toPathsumWithHints :: [ID] -> Primitive -> Pathsum Z8
toPathsumWithHints vars gate = case gate of
  H x      -> init { pathVars = [0],
                     sde = s + 1,
                     poly = p + ofTerm (fromInteger 4) [x, "p0"],
                     outVals = Map.insert x (ofVar "p0") outv }
  X x      -> init { outVals = Map.adjust (+ one) x outv }
  Y x      -> init { poly = p + (constant $ fromInteger 2) + (ofTerm (fromInteger 4) [x]),
                     outVals = Map.adjust (+ one) x outv }
  Z x      -> init { poly = p + (ofTerm (fromInteger 4) [x]) }
  CNOT x y -> init { outVals = Map.adjust (+ (ofVar x)) y outv }
  S x      -> init { poly = p + (ofTerm (fromInteger 2) [x]) }
  Sinv x   -> init { poly = p + (ofTerm (fromInteger 6) [x]) }
  T x      -> init { poly = p + (ofTerm (fromInteger 1) [x]) }
  Tinv x   -> init { poly = p + (ofTerm (fromInteger 7) [x]) }
  Swap x y -> init { outVals = Map.insert x (outv!y) $ Map.insert y (outv!x) outv }
  where init@(Pathsum s inv pathv p outv) = identity vars

toPathsum :: Primitive -> Pathsum Z8
toPathsum gate = case gate of
  H x      -> toPathsumWithHints [x] gate
  X x      -> toPathsumWithHints [x] gate
  Y x      -> toPathsumWithHints [x] gate
  Z x      -> toPathsumWithHints [x] gate
  CNOT x y -> toPathsumWithHints [x,y] gate
  S x      -> toPathsumWithHints [x] gate
  Sinv x   -> toPathsumWithHints [x] gate
  T x      -> toPathsumWithHints [x] gate
  Tinv x   -> toPathsumWithHints [x] gate
  Swap x y -> toPathsumWithHints [x,y] gate


circuitPathsumWithHints :: [ID] -> [Primitive] -> Pathsum Z8
circuitPathsumWithHints vars circuit = foldMap (toPathsumWithHints vars) circuit

circuitPathsum :: [Primitive] -> Pathsum Z8
circuitPathsum circuit = foldMap toPathsum circuit

{- Simulation -}

newtype DyadicInt = D (Int, Int) deriving (Eq) -- NOTE: must be in lowest form
newtype DOmega    = DOmega (DyadicInt, DyadicInt, DyadicInt, DyadicInt) deriving (Eq)

instance Show DyadicInt where
  show (D (a,n)) = show a ++ "/2^" ++ show n

instance Num DyadicInt where
  (D (a,n)) + (D (b,m))
    | a == 0 = D (b,m)
    | b == 0 = D (a,n)
    | n == m = canonicalize $ D ((a + b) `div` 2, n-1)
    | otherwise =
      let n' = max n m in
        canonicalize $ D (a * 2^(n' - n) + b * 2^(n' - m), n')
  (D (a,n)) * (D (b,m)) = canonicalize $ D (a * b, n + m)
  negate (D (a,n)) = D (-a, n)
  abs (D (a,n))    = D (abs a, n)
  signum (D (a,n)) = D (signum a, 0)
  fromInteger i    = D (fromInteger i, 0)

canonicalize :: DyadicInt -> DyadicInt
canonicalize (D (a,n))
  | a == 0                  = D (0,0)
  | a `mod` 2 == 0 && n > 0 = canonicalize $ D (a `div` 2, n-1)
  | otherwise               = D (a,n)

instance Show DOmega where
  show (DOmega (a,b,c,d)) =
    show a ++ " + " ++
    show b ++ "*w + " ++
    show c ++ "*w^2 + " ++
    show d ++ "*w^3"

instance Num DOmega where
  DOmega (a,b,c,d) + DOmega (a',b',c',d') = DOmega (a+a',b+b',c+c',d+d')
  DOmega (a,b,c,d) * DOmega (a',b',c',d') = DOmega (a'',b'',c'',d'')
    where a'' = a*a' - b*d' - c*c' - d*b'
          b'' = a*b' + b*a' - c*d' - d*c'
          c'' = a*c' + b*b' + c*a' - d*d'
          d'' = a*d' + b*c' + c*b' + d*a'
  negate (DOmega (a,b,c,d)) = DOmega (-a,-b,-c,-d)
  abs    x = x -- N/A
  signum x = x -- N/A
  fromInteger i = DOmega (fromInteger i, D (0,0), D (0,0), D (0,0))

-- w^x
expZ8 :: Z8 -> DOmega
expZ8 (Z8 x) = case x `mod` 4 of
  0 -> DOmega (D (y,0), D (0,0), D (0,0), D (0,0))
  1 -> DOmega (D (0,0), D (y,0), D (0,0), D (0,0))
  2 -> DOmega (D (0,0), D (0,0), D (y,0), D (0,0))
  3 -> DOmega (D (0,0), D (0,0), D (0,0), D (y,0))
  where y = (-1)^(x `div` 4)

scaleD :: DyadicInt -> DOmega -> DOmega
scaleD x (DOmega (a,b,c,d)) = DOmega (x*a,x*b,x*c,x*d)

-- 1/sqrt(2)^i * w^x
scaledExp :: Int -> Z8 -> DOmega
scaledExp i (Z8 x)
  | i `mod` 2 == 0 = scaleD (D (1,i `div` 2)) (expZ8 $ Z8 x)
  | otherwise      = scaledExp (i+1) (Z8 $ mod (x-1) 8) + scaledExp (i+1) (Z8 $ mod (x+1) 8)

isClosed :: (Eq a, Num a) => Pathsum a -> Bool
isClosed = (< 1) . degree . poly

{- Folds over paths -}

foldPaths :: (Eq a, Num a) => (Pathsum a -> b) -> (b -> b -> b) -> Pathsum a -> b
foldPaths f g sop = case pathVars sop of
      []   -> f sop
      x:xs ->
        let sop0 = sop { pathVars = xs,
                         poly = simplify . subst (pathVar x) zero $ poly sop,
                         outVals = Map.map (simplify . subst (pathVar x) zero) $ outVals sop }
            sop1 = sop { pathVars = xs,
                         poly = simplify . subst (pathVar x) one $ poly sop,
                         outVals = Map.map (simplify . subst (pathVar x) one) $ outVals sop }
        in
          g (foldPaths f g sop0) (foldPaths f g sop1)

foldReduce :: (Eq a, Fin a) => (Pathsum a -> b) -> (b -> b -> b) -> Pathsum a -> b
foldReduce f g sop = case pathVars sop of
      []   -> f sop
      x:xs ->
        let sop0 = sop { pathVars = xs,
                         poly = simplify . subst (pathVar x) zero $ poly sop,
                         outVals = Map.map (simplify . subst (pathVar x) zero) $ outVals sop }
            sop1 = sop { pathVars = xs,
                         poly = simplify . subst (pathVar x) one $ poly sop,
                         outVals = Map.map (simplify . subst (pathVar x) one) $ outVals sop }
        in
          g (foldReduce f g . snd . reduce $ sop0) (foldReduce f g . snd . reduce $ sop1)

foldReduceFull :: (Show a, Eq a, Fin a) => (Pathsum a -> b) -> (b -> b -> b) -> Pathsum a -> b
foldReduceFull f g sop = case (pathVars sop, inputVars) of
      ([], []) -> f sop
      ([], x:xs) ->
        let sop0 = sop { poly = simplify . subst x zero $ poly sop,
                         outVals = Map.map (simplify . subst x zero) $ outVals sop }
            sop1 = sop { poly = simplify . subst x one $ poly sop,
                         outVals = Map.map (simplify . subst x one) $ outVals sop }
        in
          g (foldReduceFull f g . snd . reduce $ sop0) (foldReduceFull f g . snd . reduce $ sop1)
      (x:xs, _) ->
        let sop0 = sop { pathVars = xs,
                         poly = simplify . subst (pathVar x) zero $ poly sop,
                         outVals = Map.map (simplify . subst (pathVar x) zero) $ outVals sop }
            sop1 = sop { pathVars = xs,
                         poly = simplify . subst (pathVar x) one $ poly sop,
                         outVals = Map.map (simplify . subst (pathVar x) one) $ outVals sop }
        in
          g (foldReduceFull f g . snd . reduce $ sop0) (foldReduceFull f g . snd . reduce $ sop1)
  where inputVars = foldr (\poly -> union (vars poly)) (vars $ poly sop) (Map.elems $ outVals sop)

expandPaths :: (Eq a, Num a) => Pathsum a -> [Pathsum a]
expandPaths = foldPaths (\x -> [x]) (++)

amplitudesMaybe :: Pathsum Z8 -> Maybe (Map (Map ID (Multilinear Bool)) DOmega)
amplitudesMaybe sop = foldReduce f g sop
  where f sop = if isClosed sop then
                    Just $ Map.fromList [(outVals sop, scaledExp (sde sop) . getConstant . poly $ sop)]
                  else
                    Nothing
        g = liftM2 (Map.unionWith (+))

amplitudes :: Pathsum Z8 -> Map (Map ID (Multilinear Bool)) DOmega
amplitudes sop = foldReduceFull f g sop
  where f sop = Map.fromList [(outVals sop, scaledExp (sde sop) . getConstant . poly $ sop)]
        g = Map.unionWith (+)

{- Reduction -}

data Rule =
    Elim String
  | Omega String (Multilinear Bool)
  | HH String String (Multilinear Bool)
  | Case String String (Multilinear Bool) String (Multilinear Bool)

instance Show Rule where
  show (Elim x)         = "[Elim] " ++ x
  show (Omega x p)      = "[Omega] " ++ x ++ ", remainder: " ++ show p
  show (HH x y p)       = "[HH] " ++ x ++ ", " ++ y ++ " <- "  ++ show p
  show (Case x y p z q) = "[Case] " ++ x ++ ", " ++ y ++ " <- " ++ show p
                                         ++ ", " ++ z ++ " <- " ++ show q

class Num a => Fin a where
  order :: a -> Int

instance Fin Z8 where
  order (Z8 x) = (lcm x 8) `div` x

injectZ2 :: Fin a => a -> Maybe Bool
injectZ2 a = case order a of
  0 -> Just False
  2 -> Just True
  _ -> Nothing

toBooleanPoly :: (Eq a, Fin a) => Multilinear a -> Maybe (Multilinear Bool)
toBooleanPoly = convertMaybe injectZ2 . simplify

axiomSimplify :: (Eq a, Fin a) => Pathsum a -> Maybe Int
axiomSimplify sop = msum . (map f) $ internalPaths sop
  where f i = if (pathVar i) `appearsIn` (poly sop) then Nothing else Just i

axiomHHStrict :: (Eq a, Fin a) => Pathsum a -> Maybe (Int, Int, Multilinear Bool)
axiomHHStrict sop = msum . (map f) $ internalPaths sop
  where g (x, p) = x `elem` (map pathVar $ pathVars sop)
        f i      = do
          p'        <- return $ factorOut (pathVar i) $ poly sop
          p''       <- toBooleanPoly p'
          (j, psub) <- find g $ solveForX p''
          return (i, read $ tail j, psub)

axiomHHOutputRestricted :: (Eq a, Fin a) => Pathsum a -> Maybe (Int, Int, Multilinear Bool)
axiomHHOutputRestricted sop = msum . (map f) $ internalPaths sop
  where g (x, p) = x `elem` (map pathVar $ pathVars sop) && degree p <= 1
        f i      = do
          p'        <- return $ factorOut (pathVar i) $ poly sop
          p''       <- toBooleanPoly p'
          (j, psub) <- find g $ solveForX p''
          return (i, read $ tail j, psub)

axiomSH3Strict :: (Eq a, Fin a) => Pathsum a -> Maybe (Int, Multilinear Bool)
axiomSH3Strict sop = msum . (map f) $ internalPaths sop
  where f i =
          let p' = factorOut (pathVar i) $ (poly sop) - (ofTerm 2 [pathVar i]) in
            toBooleanPoly p' >>= \q -> Just (i, q)

axiomUnify :: (Eq a, Fin a) => Pathsum a -> Maybe (ID, Int, Multilinear Bool, Int, Multilinear Bool)
axiomUnify sop = msum . (map f) $ internal
  where internal   = internalPaths sop
        findSoln i = find (\(x, _) -> x == pathVar i) . solveForX
        f i        = do
          p'      <- return $ factorOut (pathVar i) $ poly sop
          (m, _)  <- find (\(m, a) -> monomialDegree m == 1 && order a == 4) . Map.toList . terms $ p'
          x       <- find (\v -> not (v == pathVar i)) $ monomialVars m
          p1      <- toBooleanPoly (p' - (ofTerm 2 [x]))
          msum . (map $ g p' i x p1) $ internal \\ [i]
        g p' i x p1 j = do
          p''       <- return $ factorOut (pathVar j) $ poly sop
          p2        <- toBooleanPoly (p'' - (constant (fromInteger 2)) - (ofTerm 6 [x]))
          (_, jsub) <- findSoln j (subst x zero p1)
          (_, isub) <- findSoln i (subst x one p2)
          return (x, i, isub, j, jsub)

axiomKill :: (Eq a, Fin a) => Pathsum a -> Maybe Int
axiomKill sop = msum . (map f) $ internalPaths sop
  where f i      = do
          p'        <- return $ factorOut (pathVar i) $ poly sop
          p''       <- toBooleanPoly p'
          if intersect (vars p'') (map pathVar $ pathVars sop) == []
            then Just i
            else Nothing

-- Single application of an axiom
applyRule :: (Eq a, Fin a) => Pathsum a -> Maybe (Rule, Pathsum a)
applyRule sop = case sop of
  (axiomSimplify -> Just rem) ->
    let sop' = sop { sde      = sde sop - 2,
                     pathVars = pathVars sop \\ [rem] }
    in
      Just (Elim $ pathVar rem, sop')
  (axiomHHStrict -> Just (rem, sub, eq)) ->
    let sop' = sop { sde      = sde sop - 2,
                     pathVars = pathVars sop \\ [rem, sub],
                     poly     = simplify . subst (pathVar sub) eq . removeVar (pathVar rem) $ poly sop,
                     outVals  = Map.map (simplify . subst (pathVar sub) eq) $ outVals sop }
    in
      Just (HH (pathVar rem) (pathVar sub) eq, sop')
  (axiomSH3Strict -> Just (rem, eq)) ->
    let sop' = sop { sde      = sde sop - 1,
                     pathVars = pathVars sop \\ [rem],
                     poly     = simplify $ one + distribute 6 eq + removeVar (pathVar rem) (poly sop) }
    in
      Just (Omega (pathVar rem) eq, sop')
  (axiomUnify     -> Just (x, i, isub, j, jsub)) ->
    let sop' = sop { sde      = sde sop - 2,
                     pathVars = pathVars sop \\ [i, j],
                     poly     =
                       let xp = ofVar x
                           pi = subst (pathVar j) jsub . subst x zero . removeVar (pathVar i) $ poly sop
                           pj = subst (pathVar i) isub . subst x one  . removeVar (pathVar j) $ poly sop
                       in
                         simplify $ xp*pj + pi - xp*pi
                   }
    in
      Just (Case x (pathVar i) isub (pathVar j) jsub, sop')
  _ -> Nothing

-- Only performs linear substitutions. Useful for simplifying without increasing complexity
applyRuleOutputRestricted :: (Eq a, Fin a) => Pathsum a -> Maybe (Rule, Pathsum a)
applyRuleOutputRestricted sop = case sop of
  (axiomSimplify -> Just rem) ->
    let sop' = sop { sde      = sde sop - 2,
                     pathVars = pathVars sop \\ [rem] }
    in
      Just (Elim $ pathVar rem, sop')
  (axiomHHOutputRestricted -> Just (rem, sub, eq)) ->
    let sop' = sop { sde      = sde sop - 2,
                     pathVars = pathVars sop \\ [rem, sub],
                     poly     = simplify . subst (pathVar sub) eq . removeVar (pathVar rem) $ poly sop,
                     outVals  = Map.map (simplify . subst (pathVar sub) eq) $ outVals sop }
    in
      Just (HH (pathVar rem) (pathVar sub) eq, sop')
  (axiomSH3Strict -> Just (rem, eq)) ->
    let sop' = sop { sde      = sde sop - 1,
                     pathVars = pathVars sop \\ [rem],
                     poly     = simplify $ one + distribute 6 eq + removeVar (pathVar rem) (poly sop) }
    in
      Just (Omega (pathVar rem) eq, sop')
  _ -> Nothing

{- Strategies -}

-- Applies reductions until a fixpoint is reached
reduce :: (Eq a, Fin a) => Pathsum a -> ([Rule], Pathsum a)
reduce sop = go ([], sop)
  where go (applied, sop) = case applyRule sop of
          Nothing           -> (reverse applied, sop)
          Just (rule, sop') -> go (rule:applied, sop')

-- Fully reduces a path sum for a given input and output state
evaluate :: (Eq a, Fin a) => Pathsum a -> Map ID Bool -> Map ID Bool -> ([Rule], Pathsum a)
evaluate sop ket bra = reduce $ restrict (ofKet ket <> sop) bra
