module Feynman.Frontend.OpenQASM3.Simulation where

import Control.Monad.State.Strict
import Data.Map (Map)
import qualified Data.Map as Map
import Feynman.Algebra.Base (DMod2)
import Feynman.Algebra.Pathsum.Balanced
import Feynman.Core (ID)
import Feynman.Frontend.OpenQASM3.Core
import Feynman.Algebra.Polynomial.Multilinear (SBool)
import Data.Bits (testBit)

data Env a = Env {
  pathsum :: Pathsum DMod2,
  binds :: [Map ID (Binding a)],
  density :: Bool
} deriving (Show)

data Binding a =
    Gate { cparams :: [ID],
           qparams :: [ID],
           body    :: [Stmt a] }
  | Symbolic { typ :: Type a, size :: Int, offset :: Int }
  | Value { typ :: Type a, value :: Expr a }
  | SumGate { bodySum :: Pathsum DMod2 }
  deriving (Show)

getEnvSize :: State (Env a) Int
getEnvSize = gets go
  where
    go (Env ps _ False) = outDeg ps 
    go (Env ps _ True)  = outDeg ps `div` 2

searchBinding :: ID -> State (Env a) (Maybe (Binding a))
searchBinding id = gets $ search . binds
  where
    search []     = Nothing
    search (b:bs) = case Map.lookup id b of
      Just bind -> Just bind
      Nothing   -> search bs

addBinding :: ID -> Binding a -> State (Env a) ()
addBinding id bind = do
  env <- get
  let ~(b:bs) = binds env
  put $ env { binds = Map.insert id bind b : bs }

-- action returns offset of allocated register
allocatePathsum :: ID -> Int -> Maybe [SBool String] -> State (Env a) Int
allocatePathsum v size init = do
  offset <- getEnvSize
  modify $ allocate offset
  return offset
  where
    qbits = case init of
      Nothing   -> replicate size 0
      Just list -> list
    allocate _ env@(Env ps _ False) = env { pathsum = ps <> ket qbits }
    allocate j env@(Env ps _ True)  = env { pathsum = newps }
      where
        embedded = embed ps (size * 2) (\i -> i) (\i -> if i < j then i else i + size)
        newps    = ket (qbits ++ qbits) .> embedded
    

evalExpr :: Expr a -> Maybe Int
evalExpr e = case e of
  EInt n -> Just n
  _ -> Nothing

evalBool :: Expr a -> Maybe Bool
evalBool = error "TODO"

evalInt :: Expr a -> Maybe Int
evalInt = error "TODO"

initEnv :: Env a
initEnv = Env (ket []) [Map.empty] False

simBool :: Expr a -> State (Env a) (Maybe Bool)
simBool = error "TODO"

simInt :: Expr a -> State (Env a) (Maybe Int)
simInt = error "TODO"

simStmt :: Stmt a -> State (Env a) ()
simStmt stmt = case stmt of
  SInclude _ _           -> return ()
  SSkip _                -> return ()
  SBarrier _ _           -> return ()
  SPragma _ _            -> return ()
  SBlock _ stmts         -> mapM_ simStmt stmts
  SWhile _ cond stmt     -> simWhile cond stmt
  SIf _ cond stmtT stmtE -> simIf cond stmtT stmtE
  
  SReset _ expr          -> simReset expr
  SDeclare _ decl        -> simDeclare decl
  SAssign _ p bop expr   -> simAssign p bop expr

  SAnnotated _ _ stmt    -> simStmt stmt
  SFor _ _ _ _           -> return ()
  SReturn _ _            -> return ()
  SExpr _ expr           -> simExpr expr 

simWhile :: Expr a -> Stmt a -> State (Env a) ()
simWhile cond stmt = do
  cond' <- simBool cond
  case cond' of
    Just True  -> do
      simStmt stmt
      simWhile cond stmt
    Just False -> return ()
    Nothing    -> error $ "non bool value in while predicate"

simIf :: Expr a -> Stmt a -> Stmt a -> State (Env a) ()
simIf cond stmtT stmtE = do
  cond' <- simBool cond
  case cond' of
    Just True  -> simStmt stmtT
    Just False -> simStmt stmtE
    Nothing    -> error $ "non bool value in if predicate"

simAssign :: AccessPath a -> Maybe BinOp -> Expr a -> State (Env a) ()
simAssign path Nothing expr = case path of
  AVar id -> error "TODO"
  AIndex id i -> error "TODO"

allocateSymbolic :: Type a -> ID -> Int -> Maybe [SBool String] -> State (Env a) ()
allocateSymbolic typ id size init = do
  offset <- allocatePathsum id size init
  addBinding id (Symbolic typ size offset)

simDeclare :: Decl a -> State (Env a) ()
simDeclare decl = case decl of
  DVar vid typ val -> case typ of
    TCBit   -> case val of
      Nothing -> allocateSymbolic TCBit vid 1 Nothing
      Just v  -> case evalBool v of
        Just False -> allocateSymbolic TCBit vid 1 (Just [0])
        Just True  -> allocateSymbolic TCBit vid 1 (Just [1])
        Nothing    -> error $ "invalid value in declaration"
    TCReg n -> case evalInt n of
      Nothing   -> error $ "invalid register size"
      Just size -> case val of
        Nothing -> allocateSymbolic (TCReg n) vid size Nothing
        Just _  -> error $ "invalid array value"
    TQBit   -> case val of
      Nothing -> allocateSymbolic TQBit vid 1 Nothing
      Just v  -> case evalBool v of
        Just False -> allocateSymbolic TQBit vid 1 (Just [0])
        Just True  -> allocateSymbolic TQBit vid 1 (Just [1])
        Nothing    -> error $ "invalid value in declaration"
    TQReg n -> case evalInt n of
      Nothing   -> error $ "invalid register size"
      Just size -> case val of
        Nothing -> allocateSymbolic (TQReg n) vid size Nothing
        Just _  -> error $ "invalid array value"
    TUInt n -> case evalInt n of
      Nothing   -> error $ "invalid register size"
      Just size -> case val of
        Nothing -> allocateSymbolic (TUInt n) vid size Nothing
        Just i  -> case evalInt i of
          Nothing -> error $ "invalid uint value"
          Just j  -> allocateSymbolic (TUInt n) vid size (Just $ bitVec j size)

bitVec :: Int -> Int -> [SBool String]
bitVec n size = map f [0..size-1]
  where
    f i = if testBit n i then 1 else 0

simExpr :: Expr a -> State (Env a) ()
simExpr = error "TODO"

simReset :: Expr a -> State (Env a) ()
simReset = error "TODO"

simStmts :: [Stmt a] -> State (Env a) ()
simStmts = mapM_ simStmt

simProg :: Prog a -> Env a
simProg (Prog _ stmts) = execState (simStmts stmts) initEnv
