module Feynman.Simulation.Pathsum where

import Feynman.Core hiding (Stmt,Gate)
import Feynman.Frontend.OpenQASM.Syntax
import Feynman.Algebra.Pathsum.Balanced hiding (Var)
import Feynman.Algebra.Base (DMod2)

import qualified Data.List as List
import Data.Map (Map, (!))
import qualified Data.Map as Map
import Data.Traversable (for)

import Control.Monad.State.Strict

data Env = Env {
  pathsum :: Pathsum DMod2,
  binds :: [Map ID Binding]
} deriving (Show)

data Binding =
    QReg { size :: Int,
           offset :: Int }
  | CReg { size :: Int,
           stored :: Int }
  | QVar { offset :: Int }
  | CVar { value :: Double }
  | Gate { cparams :: [ID],
           qparams :: [ID],
           body :: [UExp] }
  deriving (Show)

initEnv :: Env
initEnv = Env (ket []) [Map.empty]

readGateDef :: ID -> State Env Binding
readGateDef id = gets $ search id . binds
  where
    search id (b:bs) = case Map.lookup id b of
      Just gateDef -> gateDef
      Nothing -> search id bs 

-- get value of a classical register
getValue :: ID -> State Env Int
getValue id = gets $ search id . binds
  where 
    search id (b:bs) = case Map.lookup id b of
      Just (CReg _ value) -> value
      Nothing -> search id bs

getBinding :: ID -> State Env Binding 
getBinding id = gets $ search id . binds
  where
    search id (b:bs) = case Map.lookup id b of
      Just bind -> bind
      Nothing -> search id bs 

-- action returns offset of allocated register
allocatePathsum :: Int -> State Env Int
allocatePathsum size = do
  env <- get
  let ps = pathsum env
  let offset = outDeg ps
  put env { pathsum = ps <> (ket $ replicate size 0) }
  return offset

addBind :: ID -> Binding -> State Env ()
addBind id binding = do
  env <- get
  let ~(b:bs) = binds env
  put $ env {binds = Map.insert id binding b : bs}

getOffset :: Arg -> State Env Int
getOffset arg = case arg of
  Var id -> do 
    ~(QVar offset) <- getBinding id
    return offset
  Offset id index -> do 
    ~(QReg _ offset) <- getBinding id
    return $ offset + index

simExp :: Exp -> State Env Double
simExp e = case e of
  FloatExp f -> return f
  IntExp i -> return $ fromIntegral i
  PiExp -> return pi
  VarExp id -> do 
    ~(CVar value) <- getBinding id
    return value
  UOpExp op e' -> liftM (evalUOp op) $ simExp e'
  BOpExp e1 op e2 -> do
    e1' <- simExp e1
    e2' <- simExp e1
    return $ (evalBOp op) e1' e2'

pushEnv :: [ID] -> [Exp] -> [ID] -> [Arg] -> State Env ()
pushEnv cparams exps qparams args = do
  cbindings <- liftM (map CVar) $ mapM simExp exps
  qbindings <- liftM (map QVar) $ mapM getOffset args
  env <- get
  let newbinds = Map.fromList $ List.zip cparams cbindings ++ List.zip qparams qbindings
  put $ env {binds = newbinds : binds env}

popEnv :: State Env ()
popEnv = do
  env <- get
  let b:bs = binds env
  put $ env {binds = bs}

simDeclare :: Dec -> State Env ()
simDeclare dec = case dec of
  VarDec id (Qreg size)           -> do
                                      offset <- allocatePathsum size
                                      addBind id (QReg size offset)
  VarDec id (Creg size)           -> addBind id (CReg size 0)
  GateDec id cparams qparams body -> addBind id (Gate cparams qparams body)
  UIntDec _ _ _                   -> return ()

simGate :: UExp -> State Env ()
simGate uexp = case uexp of
  CallGate id exps args -> do
    argslist <- expandArgs args
    forM_ argslist (\args' -> simGate' $ CallGate id exps args')
  CXGate arg1 arg2 -> do
    argslist <- expandArgs [arg1, arg2]
    forM_ argslist callCX
  BarrierGate _ -> return ()

  where
    callCX :: [Arg] -> State Env ()
    callCX (a1:a2:_) =
      simGate' $ CXGate a1 a2

    -- expand args (consisting of registers and indexed registers)
    -- into lists of args only with indexed registers
    expandArgs :: [Arg] -> State Env [[Arg]]
    expandArgs args = do
      -- fold over args to see if any are registers
      -- if so, what size
      iters <- foldM ( \n arg -> case arg of
          Var id -> do
            x <- getBinding id
            case x of
              QReg size offset -> return size
              _ -> return n
          Offset _ _ -> return n ) 0 args
      case iters of
        0 -> return [args]
        _ -> forM [0..iters-1] $ \n ->
          forM args $ \arg ->
            case arg of
              Var id -> return $ Offset id n
              Offset _ _ -> return arg
    
    -- assumes that no args are registers
    simGate' :: UExp -> State Env ()
    simGate' uexp = case uexp of
      CallGate id exps args -> do
        ~(Gate cparams qparams body) <- getBinding id
        pushEnv cparams exps qparams args
        mapM_ simGate' body
        popEnv
      CXGate arg1 arg2 -> do
        offset1 <- getOffset arg1
        offset2 <- getOffset arg2
        env <- get
        put env { pathsum = applyCX offset1 offset2 $ pathsum env }


simReset :: Arg -> State Env ()
simReset arg = return ()

simQExp :: QExp -> State Env ()
simQExp qexp = case qexp of
  GateExp exp -> simGate exp
  ResetExp arg -> simReset arg
  MeasureExp _ _ -> return ()


simStmt :: Stmt -> State Env ()
simStmt stmt = case stmt of
  IncStmt _ -> return ()
  DecStmt dec -> simDeclare dec
  QStmt qexp -> simQExp qexp
  IfStmt x n qexp -> do
    c <- getValue x
    if c == n then
      simQExp qexp
    else
      return ()

simQASM :: QASM -> Env
simQASM (QASM _ stmts) =
  execState (mapM_ simStmt stmts) initEnv
