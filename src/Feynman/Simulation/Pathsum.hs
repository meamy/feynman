module Feynman.Simulation.Pathsum where

import Feynman.Core hiding (Stmt,Gate)
import Feynman.Frontend.OpenQASM.Syntax
import Feynman.Algebra.Pathsum.Balanced hiding (Var, Zero)
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
  | SumGate { bodySum :: Pathsum DMod2 }
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
  VarExp id -> liftM value $ getBinding id
  UOpExp op e' -> liftM (evalUOp op) $ simExp e'
  BOpExp e1 op e2 -> do
    e1' <- simExp e1
    e2' <- simExp e2
    return $ (evalBOp op) e1' e2'

pushEmptyEnv :: State Env ()
pushEmptyEnv =
  modify $ \env -> env { binds = Map.empty : binds env }

pushp :: [ID] -> State Env ()
pushp qparams = do
  let qbindings = map QVar [0..(length qparams - 1)]
  let newbinds = Map.fromList $ List.zip qparams qbindings
  modify $ \env -> env { binds = newbinds : binds env}

pushEnv :: [ID] -> [Exp] -> [ID] -> [Arg] -> State Env ()
pushEnv cparams exps qparams args = do
  cbindings <- liftM (map CVar) $ mapM simExp exps
  qbindings <- liftM (map QVar) $ mapM getOffset args
  let newbinds = Map.fromList $ List.zip cparams cbindings ++ List.zip qparams qbindings
  modify $ \env -> env {binds = newbinds : binds env}

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
  GateDec id []      qparams body -> do
                                      summary <- summarizeGate qparams body
                                      addBind id (SumGate summary)
  GateDec id cparams qparams body -> addBind id (Gate cparams qparams body)
  UIntDec _ _ _                   -> return ()

summarizeGate :: [ID] -> [UExp] -> State Env (Pathsum DMod2)
summarizeGate qparams body = do
  let init = identity (length qparams)
  pushp qparams
  summary <- foldM (\p uexp -> simGate False p [] uexp) init body
  popEnv
  return summary

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
-- case for SumGate? --

evalGateList :: [UExp] -> State Env (Pathsum DMod2)
evalGateList uexps = foldM (\g h -> return $ g .> h) (identity 1) =<< mapM evalGate uexps

applyGate :: Bool -> Pathsum DMod2 -> [Arg] -> Pathsum DMod2 -> [Arg] -> State Env (Pathsum DMod2)
applyGate density ps controls gate@(Pathsum _ b _ _ _ _) args
  | not $ null controls = applyGate density ps [] (controlledN (length controls) gate) (controls ++ args)
  | length args == b = do
      offsets <- mapM getOffset args
      controlOffsets <- mapM getOffset controls
      return $ applyGate' ps offsets
  where
    applyGate' :: Pathsum DMod2 -> [Int] -> Pathsum DMod2
    applyGate' ps@(Pathsum _ _ c _ _ _) offsets
      | not density = ps .> embed gate (c - b) f f
      | density     = ps .> embed (channelize gate) (c - 2*b) g g
      where
        f, g :: Int -> Int
        f = (!!) offsets
        g = (!!) (offsets ++ map (+c) offsets)

stdlib = ["x", "y", "z", "h", "cx", "cy", "cz", "ch", "id", "s", "sdg", "t", "tdg", "rz", "rx", "ry", "ccx", "crz", "u3", "u2", "u1", "cu1", "cu3"]

simGateExp :: [Arg] -> UExp -> State Env ()
simGateExp controls uexp = do
  env <- get
  ps <- simGate (density env) (pathsum env) controls uexp
  modify $ \env -> env { pathsum = ps }

simGate :: Bool -> Pathsum DMod2 -> [Arg] -> UExp -> State Env (Pathsum DMod2)
simGate density ps controls uexp = case uexp of
  CallGate id exps args | not (id `elem` stdlib) -> do
    args' <- expandArgs args
    gateBinding <- getBinding id
    case gateBinding of
      Gate cparams qparams body ->
        foldM ( \p arglist -> do
          pushEnv cparams exps qparams arglist
          ps' <- foldM (\q -> simGate density q controls) p body
          popEnv
          return ps' )
          ps
          args'
      SumGate gatePS ->
        foldM (\p a -> applyGate density p controls gatePS a) ps args'
  _ -> do
    gatePS <- evalGate uexp
    expandArgs args >>= (foldM (\p a -> applyGate density p controls gatePS a) ps)
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

simReset :: [Arg] -> Arg -> State Env ()
simReset controls arg = case arg of
  Offset id index -> do
    pushEmptyEnv
    simDeclare $ VarDec tempid $ Qreg 1
    simGateExp controls $ CXGate arg (Offset tempid 0)
    simGateExp controls $ CXGate (Offset tempid 0) arg
    popEnv
  Var id -> do
    size <- liftM size $ getBinding id
    pushEmptyEnv
    simDeclare $ VarDec tempid $ Qreg size
    simGateExp controls $ CXGate arg (Var tempid)
    simGateExp controls $ CXGate (Var tempid) arg
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
      simGateExp controls $ CXGate arg1 arg2

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
  GateExp exp -> simGateExp [] exp
  ResetExp arg -> simReset [] arg
  MeasureExp arg1 arg2 -> simMeasure [] arg1 arg2

checkAssertion :: Assertion -> State Env Bool
checkAssertion assert = case assert of
  AssertAnd a1 a2 -> (liftM2 (&&)) (checkAssertion a1) (checkAssertion a2)
  AssertOr  a1 a2 -> (liftM2 (||)) (checkAssertion a1) (checkAssertion a2)
  AssertNot a     -> (liftM not) (checkAssertion a)
  AssertProj arg@(Offset id i) state -> do
    offset <- getOffset arg
    gets $ assertState offset state
  AssertProj arg@(Var id) state -> do
    regsize <- liftM size $ getBinding id
    liftM and . mapM checkAssertion . map (\a -> AssertProj a state) $ [ Offset id i | i <- [0..regsize-1] ]
      
  where
    assertState offset state env@(Env ps _ density) = 
      let statePs = evalStatePs state
          projector = embed (densify statePs) (psSize env - 1) f f
          projector' = if density then channelize projector else projector
      in
        grind ps == (grind $ ps .> projector')
      where
        f i = if i == 0 then offset else 0

evalStatePs :: QState -> Pathsum DMod2
evalStatePs q = case q of
  Zero -> fresh
  One -> fresh .> xgate
  Plus -> fresh .> hgate
  Minus -> fresh .> xgate .> hgate

simStmt :: Stmt -> State Env ()
simStmt stmt = case stmt of
  IncStmt _ -> return ()
  DecStmt dec -> simDeclare dec
  QStmt qexp -> simQExp qexp
  IfStmt c n qexp -> do
    size <- liftM size $ getBinding c
    let nc = map (\i -> Offset c i) . filter (not . testBit n) $ [0..size-1]
    flipNegativeControls nc
    simControlled [ Offset c i | i <- [0..size-1] ] qexp
    flipNegativeControls nc
  AssertStmt assert -> do
    b <- checkAssertion assert
    if b then
      return ()
    else error "assertion failed!" --add more details to printout?

  where
    flipNegativeControls :: [Arg] -> State Env ()
    flipNegativeControls = mapM_ (simStmt . QStmt . GateExp . \arg -> CallGate "x" [] [arg])

simControlled :: [Arg] -> QExp -> State Env ()
simControlled controls qexp = case qexp of
  GateExp exp -> simGateExp controls exp
  MeasureExp arg1 arg2 -> simMeasure controls arg1 arg2
  ResetExp arg -> simReset controls arg

simQASM :: QASM -> Env
simQASM (QASM _ stmts) =
  execState (mapM_ simStmt stmts) initEnv
