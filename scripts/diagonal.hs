{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

{-|
Module      : Main
Description : Diagonal synthesis tests
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Main where

import Data.List

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Map (Map,(!))
import qualified Data.Map as Map

import Control.Monad.Writer.Lazy (Writer, tell, runWriter, execWriter)
import Control.Monad.State.Strict (StateT, modify, get, gets, put, runState, evalState, evalStateT)

import Feynman.Core
import Feynman.Circuits
import Feynman.Control
import Feynman.Algebra.Base
import Feynman.Algebra.Polynomial hiding (Var)
import Feynman.Algebra.Polynomial.Multilinear
import Feynman.Algebra.Pathsum.Balanced hiding (dagger)

import Feynman.Synthesis.Pathsum.Util (ExtractionGates)
import Feynman.Synthesis.Pathsum.Unitary

import Feynman.Verification.Channel

import qualified Debug.Trace as Trace

import Test.QuickCheck

instance Arbitrary (SBool String) where
  arbitrary = sized $ \n -> do
    let genMon = resize n $ listOf (elements ["x" ++ show i | i <- [0..n-1]])
    terms <- resize (2^n) $ listOf genMon
    return $ ofTermList [(1, monomial xs) | xs <- terms]

instance Arbitrary (PseudoBoolean String DMod2) where
  arbitrary = sized $ \n -> do
    let genMon = resize n $ listOf (elements ["x" ++ show i | i <- [0..n-1]])
    let genTerm = do
          m <- genMon
          a <- chooseInt (0,7)
          return (dMod2 (toInteger a) 2, m)
    terms <- resize (2^n) $ listOf genTerm
    return $ ofTermList [(a, monomial xs) | (a,xs) <- terms]

-- | Random phase polynomial on a specific number of bits
randomBool :: Int -> Gen (SBool String)
randomBool n = resize n arbitrary

-- | Random phase polynomial on a specific number of bits
randomPP :: Int -> Gen (PseudoBoolean String DMod2)
randomPP n = resize n arbitrary

-- | Maps a polynomial over strings to one over Vars
conv :: PseudoBoolean String r -> PseudoBoolean Var r
conv p = rename (mp!) p where mp = Map.fromList $ zip (Set.toList $ vars p) [(IVar i) | i <- [0..]]

-- | Generates a path sum from a phase polynomial
phaseOracle :: Int -> SBool String -> Pathsum DMod2
phaseOracle n f = Pathsum 0 n n 0 (lift.conv $ f) [ofVar (IVar i) | i <- [0..n-1]]

-- | Generates a path sum from a phase polynomial
diag :: Int -> PseudoBoolean String DMod2 -> Pathsum DMod2
diag n f = Pathsum 0 n n 0 (conv f) [ofVar (IVar i) | i <- [0..n-1]]
  
-- | Computes the inner extension of a phase polynomial by merging pairs of monomials
innerExt :: (Eq r, Abelian r, Dyadic r, Show r) => Int -> PseudoBoolean String r -> (PseudoBoolean String r, Map ID (String, String))
innerExt deg = go Map.empty where
  go tms p | degree p <= deg = (p, tms)
  go tms p | otherwise       =
             let v        = "(" ++ show (length tms) ++ ")"
                 (x,y,p') = chooseMerge tms v p
             in
               go (Map.insert v (x,y) tms) p'

  -- | Chooses which two variables to merge by minimizing high degree terms
  chooseMerge tms v p =
    let vlst = Set.toList (vars p)
        f (_,_,p) (_,_,q) = compare (totdeg p) (totdeg q)
    in
      minimumBy f $ map (merge tms p v) [(x,y) | x <- vlst, y <- vlst, x /= y]

  -- | Calculates the sum of the degrees
  totdeg = sum . map (\(_,m) -> max 0 (degree m - deg)) . toTermList

  -- | Merges two variables into a new variable v
  merge tms p v (x,y) = (x,y,substMonomial [x,y] (ofVar v) p)

  -- | Maps combined variables into a set of variables
  expand tms x = case Map.lookup x tms of
    Nothing    -> Set.singleton x
    Just (y,z) -> Set.union (expand tms y) (expand tms z)
  
-- | Computes the outer extension of a phase polynomial by taking derivatives
outerExt :: (Ord r, Eq r, Abelian r, Dyadic r) => Int -> PseudoBoolean String r -> (PseudoBoolean String r, Map ID ([String], PseudoBoolean String r))
outerExt deg f = (ofTermList f0 + f1', ext) where
  
  (f0,f1) = partition (\(_,m) -> degree m <= deg) $ toTermList f

  (f1',ext) = runState (go 0 [(ofTermList f1, [])]) Map.empty

  go i []             = return 0
  go i ((0,_):xs)     = go i xs
  go i ((f,vs):xs)    = case length vs == deg - 1 of
    True  -> do
      modify $ Map.insert ("(" ++ show i ++ ")") (vs, f)
      f' <- go (i+1) xs
      return $ f' + ofMonomial (monomial $ ("(" ++ show i ++ ")"):vs)
    False ->
      let (f0, v, f1) = chooseDeriv f in
        go i $ (f0,vs):(f1,v:vs):xs

  chooseDeriv f = maximumBy cmp $ [(remVar v f, v, quotVar v f) | v <- Set.toList (vars f)]

  cmp (f0,v,f1) (g0,u,g1) = compare (length $ toTermList f1) (length $ toTermList g1)

-- | Synthesize a diagonal gate
synthDiag :: PseudoBoolean String DMod2 -> [ExtractionGates]
synthDiag p = snd $ runWriter $ evalStateT go ctx where
  n   = Set.size $ vars p
  ctx = mkctx $ Map.fromList [("x" ++ show i, i) | i <- [0..n-1]]
  go  = let ?feynmanControl=defaultControl in phaseSimplificationsXAGRz (diag n p)

-- | Synthesizes a CNOT-dihedral circuit
synthFourier :: PhasePolynomial String DMod2 -> [Primitive]
synthFourier = concat . map go . toTermList where
  go (a,m) = case Set.toList $ vars m of
    []     -> []
    (x:xs) -> let comp = map (\y -> CNOT y x) xs in
      comp ++ [Rz (Discrete a) x] ++ reverse comp

-- | Synthesizes an oracle
synthOracle :: SBool String -> [Primitive]
synthOracle f =
  let (fext, g) = innerExt 2 $ (lift $ (ofVar "y")*f) + distribute (dMod2 (-1) 1) f
      comp      = foldr (\(z, (x,y)) -> (tAND x y z ++)) [] $ Map.toList g
      uncomp    = foldr (\(z, (x,y)) -> (++ tinvAND x y z)) [] $ Map.toList g
      ff        = fourier fext
        --let filt (a,m) = Set.member "y" (vars m) in
        --  ofTermList . filter filt . toTermList $ fourier fext
  in
    [H "y"] ++ comp ++ synthFourier ff ++ uncomp ++ [H "y", S "y"]

-- | Synthesizes an uncomputation
synthUncompute :: ID -> SBool String -> [Primitive]
synthUncompute y f =
  let (fext,g) = innerExt 2 $ lift f
      comp     = foldr (\(z, (x,y)) -> (tAND x y z ++)) [] $ Map.toList g
      uncomp   = foldr (\(z, (x,y)) -> (++ tinvAND x y z)) [] $ Map.toList g
      ff       = fourier fext
      fcomp    = comp ++ synthFourier ff ++ uncomp
  in
    [H y, Measure y] ++ map (Ctrl y) fcomp

{-------------------------------------
 Testing
 -------------------------------------}

x1,x2,x3,x4,x5,x6,x7,x8,x9 :: PseudoBoolean String DMod2
x1 = ofVar "x1"
x2 = ofVar "x2"
x3 = ofVar "x3"
x4 = ofVar "x4"
x5 = ofVar "x5"
x6 = ofVar "x6"
x7 = ofVar "x7"
x8 = ofVar "x8"
x9 = ofVar "x9"

q = x1*x2*x3 + x2*x3*x4 + x4*x5*x6 + x2*x3*x4*x5*x6

p = x1*x2*x3*x4 + x2*x3*x4*x5 + x4*x5*x6*x7 + x2*x3*x4*x5*x6*x8

w = x1*x2*x3*x4 + x1*x5*x6*x7

-- | Main script
main :: IO ()
main = do
  putStrLn "There's nothing here!"
