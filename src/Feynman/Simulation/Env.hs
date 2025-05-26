module Feynman.Simulation.Env where

import Feynman.Algebra.Base (DMod2)
import Feynman.Algebra.Pathsum.Balanced hiding (Var, Zero)
import Feynman.Core (ID)
import Feynman.Frontend.OpenQASM.Syntax

import Control.Monad.State.Strict
import Data.Map (Map)
import qualified Data.Map as Map


data Env = Env {
  pathsum :: Pathsum DMod2,
  binds :: [Map ID Binding],
  density :: Bool,
  uninitialized :: [TypedID]
} deriving (Show)

data Binding =
    QReg { size :: Int,
           offset :: Int }
  | CReg { size :: Int,
           offset :: Int }
  | QVar { offset :: Int }
  | CVar { value :: Double }
  | Gate { cparams :: [ID],
           qparams :: [ID],
           body :: [UExp] }
  | SumGate { bodySum :: Pathsum DMod2}
  deriving (Show)

initEnv :: Env
initEnv = Env (ket []) [Map.empty] False []

isDensity :: State Env Bool
isDensity = gets $ density

densifyEnv :: State Env ()
densifyEnv = modify $ \env ->
  if density env then
    env
  else
    env { pathsum = vectorize . densify $ pathsum env, density = True }

getBinding :: ID -> State Env Binding
getBinding id = gets $ search id . binds
  where
    search id (b:bs) = case Map.lookup id b of
      Just bind -> bind
      Nothing -> search id bs

searchBinding :: ID -> State Env (Maybe Binding)
searchBinding id = gets $ search id . binds
  where
    search id []     = Nothing
    search id (b:bs) = case Map.lookup id b of
      Just bind -> Just bind
      Nothing   -> search id bs

psSize :: Env -> Int
psSize (Env ps _ False _) = outDeg ps
psSize (Env ps _ True _)  = outDeg ps `div` 2

getPSSize :: State Env Int
getPSSize = gets psSize
