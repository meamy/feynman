module Feynman.Optimization.Gadgetize where

import Control.Monad
import Control.Monad.State.Lazy

import Feynman.Core

{-- Hadamard gadgets -}
{- Provides hadamard gadgets & transformations -}

-- Fresh ancillas
type Fresh a = State (String, Integer) a

fresh :: Fresh String
fresh = do
  (s, i) <- get
  put (s, i+1)
  return $ s ++ show i

withFresh :: String -> Fresh a -> a
withFresh s f = evalState f (s,0)

-- Gadgetization methods
gadgetizeH :: ID -> Fresh [Primitive]
gadgetizeH x = do
  y <- fresh
  return [H y, S x, S y, CNOT x y, Sinv y, CNOT y x, CNOT x y, H y, CNOT y x]

gadgetizeHPost :: ID -> Fresh [Primitive]
gadgetizeHPost x = do
  y <- fresh
  return [H y, S x, S y, CNOT x y, Sinv y, CNOT y x, CNOT x y]

-- Generic application of H gadgets
gadgetizeAll :: [Primitive] -> [Primitive]
gadgetizeAll = withFresh "_H" . liftM concat . mapM go where
  go (H x) = gadgetizeH x
  go gate  = return [gate]

postselectAll :: [Primitive] -> [Primitive]
postselectAll = withFresh "_H" . liftM concat . mapM go where
  go (H x) = gadgetizeHPost x
  go gate  = return [gate]
