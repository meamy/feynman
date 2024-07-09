module Feynman.Simulation.Pathsum where

import Feynman.Core hiding (Stmt,Gate)
import Feynman.Frontend.OpenQASM.Syntax
import Feynman.Algebra.Pathsum.Balanced hiding (Var)
import Feynman.Algebra.Base (DMod2, fromDyadic)

import qualified Data.List as List
import Data.Map (Map, (!))
import qualified Data.Map as Map
import Data.Traversable (for)
import Data.Bits (testBit)

import Control.Monad.State.Strict

data Env = Env {
  pathsum :: Pathsum DMod2,
  binds :: [Map ID Binding],
  density :: Bool
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
  deriving (Show)

initEnv :: Env
initEnv = Env (ket []) [Map.empty] False

isDensity :: State Env Bool
isDensity = gets $ density

densifyEnv :: State Env ()
densifyEnv = modify $ \env -> 
  if density env then
    env 
  else
    env { pathsum = vectorize . densify $ pathsum env, density = True }

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

getPSSize :: State Env Int
getPSSize = do
  density <- isDensity
  if density then
    gets $ (`div` 2) . outDeg . pathsum
  else
    gets $ outDeg . pathsum

-- action returns offset of allocated register
allocatePathsum :: Int -> State Env Int
allocatePathsum size = do
  offset <- getPSSize
  modify allocate
  return offset
  where
    allocate env@(Env ps _ False) = env { pathsum = ps <> (ket $ replicate size 0) }
    allocate env@(Env ps _ True)  = env { pathsum = newps }
      where
        oldsize  = outDeg ps `div` 2
        embedded = embed ps (size * 2) (\i -> i) (\i -> if i < oldsize then i else i + size)
        newps = (ket $ replicate (size*2) 0) .> embedded

addBind :: ID -> Binding -> State Env ()
addBind id binding = do
  env <- get
  let ~(b:bs) = binds env
  put $ env { binds = Map.insert id binding b : bs }

getOffset :: Arg -> State Env Int
getOffset arg = case arg of
  Var id -> liftM offset $ getBinding id
  Offset id index -> liftM ((+)index . offset) $ getBinding id

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
    e2' <- simExp e2
    return $ (evalBOp op) e1' e2'

pushEmptyEnv :: State Env ()
pushEmptyEnv =
  modify $ \env -> env { binds = Map.empty : binds env }

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
  let _:bs = binds env
  put $ env {binds = bs}

simDeclare :: Dec -> State Env ()
simDeclare dec = case dec of
  VarDec id (Qreg size)           -> do
                                      offset <- allocatePathsum size
                                      addBind id (QReg size offset)
  VarDec id (Creg size)           -> do
                                      offset <- allocatePathsum size
                                      addBind id (CReg size offset)
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
  UGate theta phi lambda arg -> do
    arglist <- expandArgs [arg]
    forM_ arglist $ callU theta phi lambda 
  BarrierGate _ -> return ()

  where
    callCX :: [Arg] -> State Env ()
    callCX (a1:a2:_) =
      simGate' $ CXGate a1 a2

    callU :: Exp -> Exp -> Exp -> [Arg] -> State Env ()
    callU theta phi lambda (arg:_) =
      simGate' $ UGate theta phi lambda arg

    -- expand args (which could be a mixed list 
    -- of registers and indexed registers)
    -- into lists of only indexed registers
    expandArgs :: [Arg] -> State Env [[Arg]]
    expandArgs args = do
      -- fold over args to see if any are registers
      -- if so, what size
      iters <- foldM ( \n arg -> case arg of
          Var id -> do
            x <- getBinding id
            case x of
              QReg size offset | size > n -> return size
              _ -> return n
          Offset _ _ -> return n ) 0 args
      case iters of
        0 -> return [args]
        _ -> forM [0..iters-1] $ \n ->
          forM args $ \arg ->
            case arg of
              Var id -> return $ Offset id n
              Offset _ _ -> return arg
    
    -- assumes that no args are registers, i.e. all args are Offset id j
    simGate' :: UExp -> State Env ()
    simGate' uexp = do
      n <- getPSSize
      density <- isDensity
      case uexp of
        CallGate "cx" [] [arg1, arg2] -> simGate' $ CXGate arg1 arg2
        CallGate "id" [] [arg] -> return ()
        CallGate "x" [] [arg] -> do
          offset <- getOffset arg
          if density then
            modify $ \env -> env { pathsum = applyX offset . applyX (offset + n) $ pathsum env }
          else
            modify $ \env -> env { pathsum = applyX offset $ pathsum env }
        CallGate "y" [] [arg] -> do
          offset <- getOffset arg
          if density then
            modify $ \env -> env { pathsum = negate . applyY offset . applyY (offset + n) $ pathsum env }
          else
            modify $ \env -> env { pathsum = applyY offset $ pathsum env }
        CallGate "z" [] [arg] -> do
          offset <- getOffset arg
          if density then
            modify $ \env -> env { pathsum = applyZ offset . applyZ (offset + n) $ pathsum env }
          else
            modify $ \env -> env { pathsum = applyZ offset $ pathsum env }
        CallGate "h" [] [arg] -> do
          offset <- getOffset arg
          if density then
            modify $ \env -> env { pathsum = applyH offset . applyH (offset + n) $ pathsum env }
          else
            modify $ \env -> env { pathsum = applyH offset $ pathsum env }
        CallGate "s" [] [arg] -> do
          offset <- getOffset arg
          if density then
            modify $ \env -> env { pathsum = applySdg offset . applyS (offset + n) $ pathsum env}
          else
            modify $ \env -> env { pathsum = applyS offset $ pathsum env }
        CallGate "sdg" [] [arg] -> do
          offset <- getOffset arg
          if density then
            modify $ \env -> env { pathsum = applyS offset . applySdg (offset + n) $ pathsum env}
          else
            modify $ \env -> env { pathsum = applySdg offset $ pathsum env }
        CallGate "t" [] [arg] -> do
          offset <- getOffset arg
          if density then
            modify $ \env -> env { pathsum = applyTdg offset . applyT (offset + n) $ pathsum env}
          else
            modify $ \env -> env { pathsum = applyT offset $ pathsum env }
        CallGate "tdg" [] [arg] -> do
          offset <- getOffset arg
          if density then
            modify $ \env -> env { pathsum = applyT offset . applyTdg (offset + n) $ pathsum env}
          else
            modify $ \env -> env { pathsum = applyTdg offset $ pathsum env }
        CallGate "rz" [exp] [arg] -> do
          offset <- getOffset arg
          phi <- simExp exp
          let phi' = fromDyadic $ discretize $ Continuous phi
          if density then
            modify $ \env -> env { pathsum = applyRz (-phi') offset . applyRz phi' (offset + n) $ pathsum env}
          else
            modify $ \env -> env { pathsum = applyRz phi' offset $ pathsum env }
        CallGate "rx" [exp] [arg] ->
          mapM_ simGate' [ CallGate "h" [] [arg],
                           CallGate "rz" [exp] [arg],
                           CallGate "h" [] [arg] ]
        CallGate "ry" [exp] [arg] ->
          mapM_ simGate' [ CallGate "rz" [exp] [arg],
                           CallGate "h" [] [arg],
                           CallGate "rz" [exp] [arg],
                           CallGate "h" [] [arg] ]
        CallGate "cz" [] [arg1, arg2] -> do
          offset1 <- getOffset arg1
          offset2 <- getOffset arg2
          if density then
            modify $ \env -> env { pathsum = applyCZ offset1 offset2 . applyCZ (offset1 + n) (offset2 + n) $ pathsum env}
          else
            modify $ \env -> env { pathsum = applyCZ offset1 offset2 $ pathsum env }
        CallGate "cy" [] [arg1, arg2] -> 
          mapM_ simGate' [ CallGate "sdg" [] [arg2],
                           CallGate "cx" [] [arg1, arg2],
                           CallGate "s" [] [arg2] ]
        CallGate "ch" [] [arg1, arg2] -> 
          mapM_ simGate' [ CallGate "h" [] [arg2],
                           CallGate "sdg" [] [arg2],
                           CallGate "cx" [] [arg1, arg2],
                           CallGate "h" [] [arg2],
                           CallGate "t" [] [arg2],
                           CallGate "cx" [] [arg1, arg2],
                           CallGate "t" [] [arg2],
                           CallGate "h" [] [arg2],
                           CallGate "s" [] [arg2],
                           CallGate "x" [] [arg2],
                           CallGate "s" [] [arg1] ]
        CallGate "ccx" [] [arg1, arg2, arg3] -> do
          offset1 <- getOffset arg1
          offset2 <- getOffset arg2
          offset3 <- getOffset arg3
          if density then
            modify $ \env -> 
              env { pathsum = applyCCX offset1 offset2 offset3 
                            . applyCCX (offset1+n) (offset2+n) (offset3+n) 
                            $ pathsum env }
          else
            modify $ \env -> env { pathsum = applyCCX offset1 offset2 offset3 $ pathsum env }
        CallGate "crz" [exp] args -> do
          offsets <- mapM getOffset args
          lambda <- simExp exp
          let lambda' = fromDyadic $ discretize $ Continuous lambda
          if density then
            modify $ \env -> 
              env { pathsum = applyMCRz (-lambda') offsets 
                            . applyMCRz lambda' (map (+n) offsets)
                            $ pathsum env}
          else
            modify $ \env -> env { pathsum = applyMCRz lambda' offsets $ pathsum env }
        CallGate "u3" [theta, phi, lambda] [arg] -> 
          simGate' $ UGate theta phi lambda arg
        CallGate "u2" [phi, lambda] [arg] -> do
          simGate' $ UGate (BOpExp PiExp DivOp $ IntExp 2) phi lambda arg
          if not density then
            modify $ \env -> env { pathsum = pathsum env <> omegabar }
          else
            return ()
        CallGate "u1" [lambda] [arg] ->
          simGate' $ UGate (IntExp 0) (IntExp 0) lambda arg
        CallGate "cu1" [lambda] [arg1, arg2] -> let
          halfLambda = BOpExp lambda DivOp (IntExp 2)
          minusHalfLambda = BOpExp lambda TimesOp (IntExp $ -1) in
            mapM_ simGate' [ CallGate "u1" [halfLambda] [arg1],
                             CallGate "cx" [] [arg1, arg2],
                             CallGate "u1" [minusHalfLambda] [arg2],
                             CallGate "cx" [] [arg1, arg2],
                             CallGate "u1" [halfLambda] [arg2] ]
        CallGate "cu3" [theta, phi, lambda] [arg1, arg2] -> let
          e1 = BOpExp (BOpExp lambda MinusOp phi) DivOp (IntExp 2)
          e2 = BOpExp theta DivOp (IntExp $ -2)
          e3 = BOpExp (BOpExp phi PlusOp lambda) DivOp (IntExp $ -2)
          e4 = BOpExp theta DivOp (IntExp 2) in
            mapM_ simGate' [ CallGate "u1" [e1] [arg2],
                             CallGate "cx" [] [arg1, arg2],
                             CallGate "u3" [e2, IntExp 0, e3] [arg2],
                             CallGate "cx" [] [arg1, arg2],
                             CallGate "u3" [e4, phi, IntExp 0] [arg2] ]
        CallGate "mct" [] args -> do
          offsets <- mapM getOffset args
          if density then
            modify $ \env -> env { pathsum = applyMCT (init offsets) (last offsets) . applyMCT (map (+n) $ init offsets) ((+n) $ last offsets) $ pathsum env }
          else
            modify $ \env -> env { pathsum = applyMCT (init offsets) (last offsets) $ pathsum env }
        CallGate "mcz" [] args -> do
          offsets <- mapM getOffset args
          if density then
            modify $ \env -> env { pathsum = applyMCZ offsets . applyMCZ (map (+n) offsets) $ pathsum env }
          else
            modify $ \env -> env { pathsum = applyMCZ offsets $ pathsum env }
        CallGate id exps args -> do
          ~(Gate cparams qparams body) <- getBinding id
          pushEnv cparams exps qparams args
          mapM_ simGate' body
          popEnv
        UGate theta phi lambda arg ->
          let thetaPlusPi = BOpExp theta PlusOp PiExp
              phiPlusThreePi = BOpExp phi PlusOp $ 
                              BOpExp PiExp TimesOp $ IntExp 3 in do
            mapM_ simGate' [
              CallGate "rz" [lambda] [arg],
              CallGate "h" [] [arg],
              CallGate "s" [] [arg],
              CallGate "h" [] [arg],
              CallGate "rz" [thetaPlusPi] [arg],
              CallGate "h" [] [arg],
              CallGate "s" [] [arg],
              CallGate "h" [] [arg],
              CallGate "rz" [phiPlusThreePi] [arg] ]
            if not density then
              modify $ \env -> env { pathsum = pathsum env <> minusi }
            else
              return ()
        CXGate arg1 arg2 -> do
          offset1 <- getOffset arg1
          offset2 <- getOffset arg2
          if density then
            modify $ \env -> env { pathsum = applyCX offset1 offset2 . applyCX (offset1+n) (offset2+n) $ pathsum env }
          else
            modify $ \env -> env { pathsum = applyCX offset1 offset2 $ pathsum env }

simReset :: Arg -> State Env ()
simReset arg = case arg of
  Offset id index -> do
    pushEmptyEnv
    simDeclare $ VarDec tempid $ Qreg 1
    simGate $ CXGate arg (Offset tempid 0)
    simGate $ CXGate (Offset tempid 0) arg
    popEnv
  Var id -> do
    size <- liftM size $ getBinding id
    pushEmptyEnv
    simDeclare $ VarDec tempid $ Qreg size
    simGate $ CXGate arg (Var tempid)
    simGate $ CXGate (Var tempid) arg
    popEnv
  where
    tempid = case arg of
      Offset id _ -> id ++ "_temp"
      Var id      -> id ++ "_temp"

simMeasure :: Arg -> Arg -> State Env ()
simMeasure arg1 arg2 = densifyEnv >> case (arg1, arg2) of
  (Var id1, Var id2) -> do
    ~(QReg size _) <- getBinding id1
    forM_ [0..size-1] (\i -> simMeasure' (Offset id1 i) (Offset id2 i))
  (Offset _ _, Offset _ _) -> simMeasure' arg1 arg2
  where
    simMeasure' arg1 arg2 = do
      offset <- getOffset arg1
      n <- getPSSize
      modify $ \env -> env { pathsum =  applyMeasure offset (offset + n) $ pathsum env }
      simGate $ CXGate arg1 arg2

simQExp :: QExp -> State Env ()
simQExp qexp = case qexp of
  GateExp exp -> simGate exp
  ResetExp arg -> simReset arg
  MeasureExp arg1 arg2 -> simMeasure arg1 arg2

simStmt :: Stmt -> State Env ()
simStmt stmt = case stmt of
  IncStmt _ -> return ()
  DecStmt dec -> simDeclare dec
  QStmt qexp -> simQExp qexp
  IfStmt c n qexp -> do
    ~(CReg size _) <- getBinding c
    let controls = map (\i -> Offset c i) . filter (testBit n) $ [0..size-1]
    simControlled controls qexp

simControlled :: [Arg] -> QExp -> State Env ()
simControlled controls qexp = case qexp of
  GateExp exp -> simControlledGate controls exp
  MeasureExp _ _ -> undefined
  ResetExp _ -> undefined
  
simControlledGate :: [Arg] -> UExp -> State Env ()
simControlledGate controls uexp = case uexp of
  CXGate arg1 arg2 -> simGate $ CallGate "mct" [] (controls ++ [arg1, arg2])
  CallGate "cx" [] [arg1, arg2] -> simGate $ CallGate "mct" [] (controls ++ [arg1, arg2])
  CallGate "id" _ _ -> return ()
  CallGate "x" [] [arg] -> simGate $ CallGate "mct" [] (controls ++ [arg])
  CallGate "z" [] [arg] -> simGate $ CallGate "mcz" [] (controls ++ [arg])
  CallGate "y" [] [arg] -> undefined --TODO--

simQASM :: QASM -> Env
simQASM (QASM _ stmts) =
  execState (mapM_ simStmt stmts) initEnv
