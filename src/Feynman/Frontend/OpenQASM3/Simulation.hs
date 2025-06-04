module Feynman.Frontend.OpenQASM3.Simulation where

import Control.Monad
import Data.Map (Map)
import Feynman.Algebra.Pathsum.Balanced
import Feynman.Frontend.OpenQASM3.Core


data Env a = Env {
  pathsum :: Pathsum DMod2,
  binds :: [Map ID (Binding a)],
  density :: Bool
} deriving (Show)

data Binding a =
  | Gate { cparams :: [ID],
           qparams :: [ID],
           body :: [UExp] }
  | Symbolic { type :: Type a, size :: Int, offset :: Int }
  | Value { type :: Type a, value :: Expr a}
  | SumGate { bodySum :: Pathsum DMod2 }
  deriving (Show)

evalExpr :: Expr a -> Maybe Int
evalExpr e = case e of
  EInt n -> Just n
  _ -> None

initEnv :: Env a
initEnv = Env (ket []) [Map.empty] False

simBool :: Expr a -> State Env (Maybe Bool)

simStmt :: Stmt a -> State Env ()
simStmt stmt = case stmt of
  SInclude _ _           -> return ()
  SSkip _                -> return ()
  SBarrier _ _           -> return ()
  SBlock _ stmts         -> mapM_ simStmt stmts
  SWhile _ cond stmt     -> simWhile cond stmt
  SIf _ cond stmtT stmtE -> simIf cond stmtT stmtE
  _ -> return ()

simWhile :: Expr a -> Stmt a -> State Env ()
simWhile cond stmt = do
  cond' <- simBool cond
  case cond' of
    Just True  -> do
      simStmt stmt
      simWhile cond stmt
    Just False -> return ()
    None       -> failwith $ "non bool value in while predicate: " ++ show cond

simIf :: Expr a -> Stmt a -> Stmt a -> State Env ()
simIf cond stmtT stmtE = do
  cond' <- simBool cond
  case cond' of
    Just True  -> simStmt stmtT
    Just False -> simStmt stmtE
    None       -> failwith $ "non bool value in if predicate: " ++ show cond

simStmts :: [Stmt a] -> State Env ()
simStmts = mapM_ simStmt

simProg :: Prog a -> State Env ()
simProg (Prog _ stmts) = execState (simStmts stmts) initEnv
