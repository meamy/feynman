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
import Feynman.Control
import Feynman.Algebra.Base
import Feynman.Algebra.Polynomial hiding (Var)
import Feynman.Algebra.Polynomial.Multilinear
import Feynman.Algebra.Pathsum.Balanced

import Feynman.Synthesis.Pathsum.Util (ExtractionGates)
import Feynman.Synthesis.Reversible.Young

import Test.QuickCheck

instance Arbitrary (SBool Var) where
  arbitrary = sized $ \n -> do
    let genMon = resize n $ listOf (elements [IVar i | i <- [0..n-1]])
    terms <- resize (2^n) $ listOf genMon
    return $ ofTermList [(1, monomial xs) | xs <- terms]


control = defaultControl

-- |
synthBools :: [SBool Var] -> Maybe [ExtractionGates]
synthBools sbools = gates where
  !allVars  = Set.toList (foldl' Set.union Set.empty (map vars sbools))
  allVarIDs = ["x" ++ show i | (IVar i) <- allVars]
  gates     = let ?feynmanControl=control in youngDecompositionSynth (zip3 allVarIDs allVars sbools)


{-------------------------------------
 Testing
 -------------------------------------}

x0b,x1b,x2b,x3b,x4b,x5b,x6b,x7b,x8b,x9b :: SBool Var
[x0b,x1b,x2b,x3b,x4b,x5b,x6b,x7b,x8b,x9b] = [ofVar (IVar i) | i <- [0..9]]

-- | Main script
main :: IO ()
main = do
  putStrLn (show (synthBools $ [x1b*x2b + x1b*x3b + x2b*x3b,
                                x1b + x2b,
                                x1b + x3b]))
  -- putStrLn (show (synthBools $ [x1b*x2b*x3b + x1b*x2b*x3b*x5b, x1b*x2b*x3b + x1b*x2b*x3b*x5b]))

