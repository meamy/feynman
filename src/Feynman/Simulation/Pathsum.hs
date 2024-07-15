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

psSize :: Env -> Int
psSize (Env ps _ False) = outDeg ps
psSize (Env ps _ True)  = outDeg ps `div` 2

getPSSize :: State Env Int
getPSSize = gets psSize

-- FUNCTIONS TO WORK WITH EMBED --

{-
-- takes as input pathsum of gate and indices to apply to
applyMask :: [Int] -> Pathsum DMod2 -> State Env ()
applyMask indices gate@(Pathsum a b c d e f)
  | length indices == b = modify applyMask'
  where
    applyMask' env@(Env ps _ density)
    | not density = env { pathsum = ps .> embed gate (size - b) f f }
    | density     = env { pathsum = ps .> (channelize gate) (2 * (size - b)) g g }
    where 
      size = psSize env
      f = (!!) indices
      g = (!!) (indices ++ map (+psSize) indices)
-}

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

evalGate :: UExp -> State Env (Pathsum DMod2)
evalGate uexp = case uexp of
  CallGate "cx" _ _ -> return cxgate
  CallGate "id" _ _ -> return $ identity 1
  CallGate "x" _ _ -> return xgate
  CallGate "y" _ _ -> return ygate
  CallGate "z" _ _ -> return zgate
  CallGate "h" _ _ -> return hgate
  CallGate "s" _ _ -> return sgate
  CallGate "sdg" _ _ -> return sdggate
  CallGate "t" _ _ -> return tgate
  CallGate "tdg" _ _ -> return tdggate
  CallGate "rz" [exp] _ -> liftM (rzgate . fromDyadic . discretize . Continuous) $ simExp exp
  CallGate "rx" [exp] [arg] -> 
    evalGateList 
      [ CallGate "h" [] [arg], 
        CallGate "rz" [exp] [arg], 
        CallGate "h" [] [arg] ]
  CallGate "ry" [exp] [arg] -> 
    evalGateList
      [ CallGate "rz" [exp] [arg],
        CallGate "h" [] [arg],
        CallGate "rz" [exp] [arg],
        CallGate "h" [] [arg] ]
  CallGate "cz" _ _ -> return czgate
  CallGate "cy" _ _ -> return $ controlled ygate
  CallGate "ch" _ _ -> return chgate
  CallGate "ccx" _ _ -> return ccxgate
  CallGate "crz" [exp] args -> do
    lambda <- simExp exp
    let lambda' = fromDyadic . discretize . Continuous $ lambda
    return $ rzNgate lambda' (length args)
  CallGate "u3" [theta, phi, lambda] [arg] -> evalGate $ UGate theta phi lambda arg
  CallGate "u2" [phi, lambda] [arg] ->
    let halfPi = BOpExp PiExp DivOp $ IntExp 2 in
      liftM (<>omegabar) . evalGate $ UGate halfPi phi lambda arg
  CallGate "u1" [lambda] [arg] -> evalGate $ UGate (IntExp 0) (IntExp 0) lambda arg
  CallGate "cu1" [lambda] [arg1, arg2] ->
    liftM controlled . evalGate $ CallGate "u1" [lambda] [arg2]
  CallGate "cu3" [theta, phi, lambda] [arg1, arg2] ->
    liftM controlled . evalGate $ CallGate "u3" [theta, phi, lambda] [arg2]
  CXGate _ _ -> return cxgate
  UGate theta phi lambda arg ->
    let thetaPlusPi = BOpExp theta PlusOp PiExp
        phiPlusThreePi = BOpExp phi PlusOp $ 
                         BOpExp PiExp TimesOp $ IntExp 3 in
      liftM (<>minusi) . evalGateList $
        [ CallGate "rz" [lambda] [arg],
          CallGate "h" [] [arg],
          CallGate "s" [] [arg],
          CallGate "h" [] [arg],
          CallGate "rz" [thetaPlusPi] [arg],
          CallGate "h" [] [arg],
          CallGate "s" [] [arg],
          CallGate "h" [] [arg],
          CallGate "rz" [phiPlusThreePi] [arg] ]

evalGateList :: [UExp] -> State Env (Pathsum DMod2)
evalGateList uexps = foldM (\g h -> return $ g .> h) (identity 1) =<< mapM evalGate uexps

applyGate :: [Arg] -> Pathsum DMod2 -> [Arg] -> State Env ()
applyGate controls gate@(Pathsum _ b _ _ _ _) args
  | not $ null controls = applyGate [] (controlledN (length controls) gate) (controls ++ args)
  | length args == b = do
      offsets <- mapM getOffset args
      controlOffsets <- mapM getOffset controls
      modify $ applyGate' controlOffsets offsets
  where
    applyGate' [] offsets env@(Env ps _ density)
      | not density = env { pathsum = ps .> embed gate (outDeg ps - b) f f }
      | density     = env { pathsum = ps .> embed (channelize gate) (outDeg ps - 2*b) g g }
      where
        f, g :: Int -> Int
        f = (!!) offsets
        g = (!!) (offsets ++ map (+psSize env) offsets)

stdlib = ["x", "y", "z", "h", "cx", "cy", "cz", "ch", "id", "s", "sdg", "t", "tdg", "rz", "rx", "ry", "ccx", "crz", "u3", "u2", "u1", "cu1", "cu3"]

simGate :: [Arg] -> UExp -> State Env ()
simGate controls uexp = case uexp of
  CallGate id exps args | not (id `elem` stdlib) -> do
    ~(Gate cparams qparams body) <- getBinding id
    args' <- expandArgs args
    forM_ args' $ \arglist -> do
      pushEnv cparams exps qparams arglist
      mapM_ (simGate controls) body
      popEnv
  _ -> do
    gatePS <- evalGate uexp
    expandArgs args >>= mapM_ (applyGate controls gatePS)
  where
    args = case uexp of
      CallGate    _ _ as  -> as
      CXGate      a1 a2   -> [a1, a2]
      UGate       _ _ _ a -> [a]
      BarrierGate _       -> []

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

{-
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
-}

simReset :: [Arg] -> Arg -> State Env ()
simReset controls arg = case arg of
  Offset id index -> do
    pushEmptyEnv
    simDeclare $ VarDec tempid $ Qreg 1
    simGate controls $ CXGate arg (Offset tempid 0)
    simGate controls $ CXGate (Offset tempid 0) arg
    popEnv
  Var id -> do
    size <- liftM size $ getBinding id
    pushEmptyEnv
    simDeclare $ VarDec tempid $ Qreg size
    simGate controls $ CXGate arg (Var tempid)
    simGate controls $ CXGate (Var tempid) arg
    popEnv
  where
    tempid = case arg of
      Offset id _ -> id ++ "_temp"
      Var id      -> id ++ "_temp"

simMeasure :: [Arg] -> Arg -> Arg -> State Env ()
simMeasure controls arg1 arg2 = densifyEnv >> case (arg1, arg2) of
  (Var id1, Var id2) -> do
    ~(QReg size _) <- getBinding id1
    forM_ [0..size-1] (\i -> simMeasure' (Offset id1 i) (Offset id2 i))
  (Offset _ _, Offset _ _) -> simMeasure' arg1 arg2
  where
    simMeasure' arg1 arg2 = do
      offset <- getOffset arg1
      controlOffsets <- mapM getOffset controls
      modify $ applyMeasurement controlOffsets offset
      simGate controls $ CXGate arg1 arg2

    applyMeasurement controlOffsets offset env@(Env ps _ _) =
      env { pathsum = ps .> embed (controlledN m measureGate) (2*n - 2 - m) f f }
      where
        m = length controlOffsets
        n = psSize env
        f i
          | i < m = controlOffsets !! i
          | i == m = offset
          | i == m+1 = offset + psSize env

simQExp :: QExp -> State Env ()
simQExp qexp = case qexp of
  GateExp exp -> simGate [] exp
  ResetExp arg -> simReset [] arg
  MeasureExp arg1 arg2 -> simMeasure [] arg1 arg2

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
  GateExp exp -> simGate controls exp
  MeasureExp arg1 arg2 -> simMeasure controls arg1 arg2
  ResetExp arg -> simReset controls arg

simQASM :: QASM -> Env
simQASM (QASM _ stmts) =
  execState (mapM_ simStmt stmts) initEnv
