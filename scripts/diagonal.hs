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

import Data.Foldable (foldl')

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
import Feynman.Algebra.Polynomial.Multilinear hiding (subst)
import Feynman.Algebra.Pathsum.Balanced hiding (dagger)

import Feynman.Synthesis.Phase
import Feynman.Synthesis.Pathsum.Util (ExtractionGates(..))
import Feynman.Synthesis.Pathsum.Unitary
import Feynman.Synthesis.Reversible.XAG (minimizeXAG, inputSavingXAGSynth)
import Feynman.Synthesis.XAG.Util (fromSBools)

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
outerExt :: (Ord r, Eq r, Abelian r) => Int -> PseudoBoolean String r -> (PseudoBoolean String r, Map ID ([String], PseudoBoolean String r))
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

control = defaultControl {
            fcfTrace_Synthesis_Pathsum_Unitary = True,
            fcfTrace_Synthesis_XAG = True,
            fcfTrace_Graph = True
          }

-- | Expands extraction gates out as Clifford+T
lowerExtraction :: [ExtractionGates] -> [Primitive]
lowerExtraction = concatMap go where
  go (MCT [] x)        = [X x]
  go (MCT [x] y)       = [CNOT x y]
  go (MCT [x,y] z)     = tAND x y z
  go (Phase theta [x]) = synthesizePhase x (Discrete theta)
  go (Hadamard x)      = [H x]
  go (Swapper x y)     = [Swap x y]

-- | Expands extraction gates out as Clifford+T
lowerExtractionInv :: [ExtractionGates] -> [Primitive]
lowerExtractionInv = concatMap go . reverse where
  go (MCT [] x)        = [X x]
  go (MCT [x] y)       = [CNOT x y]
  go (MCT [x,y] z)     = tinvAND x y z
  go (Phase theta [x]) = synthesizePhase x (Discrete (-theta))
  go (Hadamard x)      = [H x]
  go (Swapper x y)     = [Swap x y]

-- |
synthDiag :: PseudoBoolean String DMod2 -> [ExtractionGates]
synthDiag p = snd $ runWriter $ evalStateT go ctx where
  n   = Set.size $ vars p
  ctx = mkctx $ Map.fromList [("x" ++ show (i + 1), i) | i <- [0..n-1]]
  go  = let ?feynmanControl=control in phaseSimplificationsXAGRz (diag n p)


-- foldl' (\(m, ids@(i : remainIDs)) s -> maybe (Map.insert i s, remainIDs) (\_ -> (m, ids)) (lookup s m)) (Map.empty, [0..]) sbools


-- |
synthBools :: [SBool String] -> [ExtractionGates]
synthBools sbools = xagGates where
  !allVars       = Set.toList (foldl' Set.union Set.empty (map vars sbools))
  !idToIndex     = Map.fromList (zip allVars [0..])
  !indexToID     = Map.fromList (zip [0..] allVars)
  !idxSBools     = map (rename (IVar . (idToIndex !))) sbools
  !xag           = let ?feynmanControl=control in minimizeXAG (fromSBools (length allVars) idxSBools)
  !outputNames   = ["y" ++ show i | i <- [1..length sbools]]
  ancillaNames   = ["A" ++ show i | i <- [1..]]
  (xagGates, _)  = let ?feynmanControl=control in inputSavingXAGSynth xag allVars outputNames ancillaNames

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

-- | Synthesizes an oracle using an inner extension
synthOracleInner :: Int -> SBool String -> [Primitive]
synthOracleInner k f =
  let (fext, g) = innerExt k $ (lift $ (ofVar "y")*f) + distribute (dMod2 (-1) 1) f
      comp      = foldr (\(z, (x,y)) -> (tAND x y z ++)) [] $ Map.toList g
      uncomp    = foldr (\(z, (x,y)) -> (++ tinvAND x y z)) [] $ Map.toList g
      ff        = fourier fext
        --let filt (a,m) = Set.member "y" (vars m) in
        --  ofTermList . filter filt . toTermList $ fourier fext
  in
    [H "y"] ++ comp ++ synthFourier ff ++ uncomp ++ [H "y", S "y"]

-- | Synthesizes an oracle using an outer extension
synthOracleOuter :: Int -> SBool String -> [Primitive]
synthOracleOuter k f =
  let (fext, g) = outerExt k $ (ofVar "y")*f
      xagsynth  = synthBools . snd . unzip . Map.elems $ g
      comp      = lowerExtraction xagsynth
      uncomp    = lowerExtractionInv xagsynth
      ff        = --fourier (lift fext :: PseudoBoolean String DMod2)
        let filt (a,m) = Set.member "y" (vars m) in
          ofTermList . filter filt . toTermList $ fourier (lift fext :: PseudoBoolean String DMod2)
      names     = Map.fromList $ zip (Map.keys $ g) ["y" ++ show i | i <- [1..]]
      sub str   = case Map.lookup str names of
        Nothing   -> str
        Just str' -> str'
  in
    [H "y"] ++ comp ++ subst sub (synthFourier ff) ++ uncomp ++ [H "y", S "y"]

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

-- | Computes the reduced sop of a circuit
checkSOP :: [Primitive] -> Pathsum DMod2
checkSOP circ = grind sop where
  sop = sopOfCircuit (ids circ) inp circ
  inp = filter (\str -> not (str == "") && head str == 'x') $ ids circ

x1,x2,x3,x4,x5,x6,x7,x8,x9 :: PseudoBoolean String DMod2
[x1,x2,x3,x4,x5,x6,x7,x8,x9] = [ofVar ("x" ++ show i) | i <- [1..9]]

q = x1*x2*x3 + x2*x3*x4 + x4*x5*x6 + x2*x3*x4*x5*x6

x1b,x2b,x3b,x4b,x5b,x6b,x7b,x8b,x9b :: SBool String
[x1b,x2b,x3b,x4b,x5b,x6b,x7b,x8b,x9b] = [ofVar ("x" ++ show i) | i <- [1..9]]

p = x1*x2*x3*x4 + x2*x3*x4*x5 + x4*x5*x6*x7 + x2*x3*x4*x5*x6*x8

w = x1*x2*x3*x4 + x1*x5*x6*x7

-- | Main script
main :: IO ()
main = do
  putStrLn (show (synthDiag $ x1*x2*x3*x4 + x2*x3*x4*x5 + x4*x5*x6*x7 + x2*x3*x4*x5*x6*x8))
  putStrLn (show (synthBools $ [x1b*x2b*x3b + x1b*x2b*x3b*x5b, x1b*x2b*x3b + x1b*x2b*x3b*x5b]))

