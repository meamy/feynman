module Feynman.Simulation.Pathsum where

import Feynman.Core hiding (Stmt,Gate,dagger,inputs)
import Feynman.Frontend.OpenQASM.Syntax
import Feynman.Frontend.OpenQASM.VerificationSyntax (GateSpec, sopOfSpec)
import Feynman.Algebra.Polynomial.Multilinear
import Feynman.Algebra.Pathsum.Balanced hiding (Var, Zero)
import qualified Feynman.Algebra.Pathsum.Balanced as PS
import Feynman.Algebra.Base (DMod2, fromDyadic, toDyadic)

import qualified Feynman.Util.Unicode as U

import Data.Maybe
import qualified Data.List as List
import Data.Map (Map, (!))
import qualified Data.Map as Map
import Data.Traversable (for)
import Data.Bits (testBit)

import qualified Debug.Trace as Trace

import Control.Monad.State.Strict

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

-- | Gives the unicode representation of the ith offset of v
varOfOffset :: ID -> Int -> String
varOfOffset v i = U.sub v (fromIntegral i)

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

-- action returns offset of allocated register
allocatePathsum :: ID -> Int -> State Env Int
allocatePathsum v size = do
  offset <- getPSSize
  ps' <- gets uninitialized >>= \tf -> case v `lookup` tf of
    Just (TypeAncilla _)  -> return $ ket (replicate size 0)
    Just _  -> return $ ket [ofVar (varOfOffset ("'" ++ v) (offset+i)) | i <- [0..size-1]]
    Nothing -> return $ ket (replicate size 0)
  ps'' <- gets uninitialized >>= \tf -> case v `lookup` tf of
    Just (TypeAncilla _)  -> return $ ket (replicate size 0)
    Just _  -> return $ ket [ofVar (varOfOffset v (offset+i)) | i <- [0..size-1]]
    Nothing -> return $ ket (replicate size 0)
  modify (allocate ps' ps'')
  return offset
  where
    allocate ps' ps'' env@(Env ps _ False _) = env { pathsum = ps <> ps'' }
    allocate ps' ps'' env@(Env ps _ True _)  = env { pathsum = newps }
      where
        oldsize  = outDeg ps `div` 2
        embedded = embed ps (size * 2) (\i -> i) (\i -> if i < oldsize then i else i + size)
        newps = (ps' <> ps'') .> embedded

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
  GateDec id [] qparams (Just spec) body -> do
    summary <- summarizeGate qparams body
    verifyGate' id spec summary
    addBind id (SumGate summary)
  GateDec id [] qparams Nothing body     -> do
    summary <- summarizeGate qparams body
    addBind id (SumGate summary)
  GateDec id cparams qparams _ body      ->
    addBind id (Gate cparams qparams body)

  VarDec id (Qreg size) -> do
    offset <- allocatePathsum id size
    addBind id (QReg size offset)
  VarDec id (Creg size) -> do
    offset <- allocatePathsum id size
    addBind id (CReg size offset)

  UIntDec _ _ _  -> return ()

verifyGate :: GateSpec -> Pathsum DMod2 -> Bool
verifyGate spec gate =
  let specPs = sopOfSpec spec
      n      = inDeg gate
  in
    (grind $ specPs .> (dagger gate)) == identity n

verifyGate' :: ID -> Spec -> Pathsum DMod2 -> State Env ()
verifyGate' id spec gatePS = do
  env <- get
  let mask   = createAncillaMask spec
  let specPS = mask .> sopOfPSSpec spec env
  let n      = inDeg mask
  let result = case (dropAmplitude $ grind $ specPS .> (dagger (mask .> gatePS))) == identity n of
        False -> "Failed!"
        True  -> "Success!"
  Trace.trace ("Verifying \"" ++ id ++ "\" against specification " ++ show (specPS) ++ "..." ++ result) $ return ()

traceList :: [ID] -> Env -> [Int]
traceList nxs = reverse . List.sort . concatMap go . concatMap Map.toList . binds
  where go (id, QReg size idx) | not (id `elem` nxs) = [idx+i | i <- [0..size-1]]
        go (id, CReg size idx) | not (id `elem` nxs) = [idx+i | i <- [0..size-1]]
        go _ = []

bindingList :: [TypedID] -> Env -> [String]
bindingList nxs env = concatMap go nxs
  where go (v, _)  = case evalState (searchBinding v) env of
          Just (QReg sz offset) -> [varOfOffset v i | i <- [offset..sz+offset-1]]
          _                -> [v]

bindingList' :: [TypedID] -> Env -> [String]
bindingList' nxs env = concatMap go nxs
  where go (v, _)  = case evalState (searchBinding v) env of
          Just (QReg sz _) -> [varOfOffset v i | i <- [0..sz-1]]
          _                -> [v]

verifyProg' :: Spec -> Env -> Bool
verifyProg' spec env =
  let mask       = channelize $ createAncillaMask spec
      specPs     = grind $ channelize $ sopOfPSSpec spec env
      initPS     = identity (inDeg mask)
      progPS     = case density env of
        False -> conjugate (pathsum env) <> pathsum env
        True  -> pathsum env
      traceBinds = traceList (fst . unzip $ inputs spec) env
      tracedPS   = grind $ foldl (\ps (i, idx) -> traceOut idx (idx+m-i) ps) progPS $ zip [0..] traceBinds
      bindings   = bindingList (inputs spec) env
      closedPS   = bind (map ("'" ++) bindings ++ bindings) tracedPS
      n          = inDeg specPs
      m          = case density env of
        False -> outDeg (pathsum env)
        True -> outDeg (pathsum env) `div` 2
  in
    Trace.trace (show . grind $ progPS) $
      (dropAmplitude $ grind $ mask .> closedPS .> (dagger (mask .> specPs))) == initPS

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
    liftM controlled' . evalGate $ CallGate "u1" [lambda] [arg2]
  CallGate "cu3" [theta, phi, lambda] [arg1, arg2] ->
    liftM controlled' . evalGate $ CallGate "u3" [theta, phi, lambda] [arg2]
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
      return $ applyGate' ps offsets
  where
    applyGate' :: Pathsum DMod2 -> [Int] -> Pathsum DMod2
    applyGate' ps@(Pathsum _ _ c _ _ _) offsets
      | not density = ps .> embed gate (c - b) f f
      | density     = ps .> embed (channelize gate) (c - 2*b) g g
      where
        f, g :: Int -> Int
        f = (!!) offsets
        g = (!!) (offsets ++ map (+c`div`2) offsets)

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

    applyMeasurement controlOffsets offset env@(Env ps _ True _) =
      env { pathsum = ps .> embed (controlledN m measureGate) (2*n - 2 - m) f f }
      where
        m = length controls
        n = outDeg ps `div` 2
        f i
          | i < m = controlOffsets !! i
          | i == m = offset
          | i == m+1 = offset + n

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
  AssertGate id spec -> do
    bind <- getBinding id
    case bind of
      SumGate ps -> return $ verifyGate spec ps 
      _ -> error "gate has no summary"
      
  where
    assertState offset state env@(Env ps _ density _) = 
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
simQASM (QASM _ (Just spec) stmts) =
  let env = execState (mapM_ simStmt stmts) (initEnv { density = True, uninitialized = inputs spec })
      result = case verifyProg' spec env of
        False -> "Failed!"
        True  -> "Success!"
  in
    Trace.trace ("Verifying whole program against specification " ++ (show $ sopOfPSSpec spec env) ++ "..." ++ result) $ env
  
simQASM (QASM _ _ stmts) =
  execState (mapM_ simStmt stmts) initEnv

{- Specification building -}
polyOfExp :: [TypedID] -> Exp -> PseudoBoolean PS.Var Double
polyOfExp boundIDs = polyOfExp'
  where
    polyOfExp' exp
      | isJust (evalExp exp) = constant $ fromJust (evalExp exp)
      | otherwise            = case exp of
          FloatExp d       -> constant d
          IntExp i         -> constant $ fromIntegral i
          PiExp            -> constant $ pi
          VarExp v         -> case lookup v boundIDs of
            Nothing -> ofVar $ FVar v
            Just TypeQubit   -> ofVar $ FVar v
            Just (TypeInt n) -> polyOfExp' $ bitBlast v n
          OffsetExp v i    -> ofVar $ FVar (varOfOffset v i)
          UOpExp uop e     -> cast (evalUOp uop) $ polyOfExp' e
          BOpExp e1 bop e2 -> case bop of
            PlusOp  -> e1' + e2'
            MinusOp -> e1' - e2'
            TimesOp -> e1' * e2'
            DivOp   -> error "Unsupported division of polynomials"
            PowOp   -> error "Unsupported exponent of polynomials"
            where e1' = polyOfExp' e1
                  e2' = polyOfExp' e2

polyOfMaybeExp :: [TypedID] -> Maybe Exp -> PseudoBoolean PS.Var Double
polyOfMaybeExp boundIDs Nothing    = 0
polyOfMaybeExp boundIDs (Just exp) = polyOfExp boundIDs exp

decomposeScalar :: Maybe Exp -> (Int, DMod2)
decomposeScalar Nothing    = (0, 0)
decomposeScalar (Just exp) = error "Normalization check not implemented"

castDMod2 :: PseudoBoolean v Double -> PseudoBoolean v DMod2
castDMod2 = cast (fromDyadic . toDyadic . (/pi))

castBoolean :: PseudoBoolean v Double -> SBool v
castBoolean = cast go where
  go 0.0 = 0
  go 1.0 = 1
  go _   = error "Not a Boolean polynomial"

sopOfPSSpec :: Spec -> Env -> Pathsum DMod2
sopOfPSSpec (PSSpec args scalar pvars ampl ovals) env = (bind bindings . sumover sumvars $ sop)
  where bindings      = bindingList' args env
        (s, gphase)   = decomposeScalar scalar
        boundIDs      = args ++ pvars
        pp            = constant gphase + (castDMod2 $ polyOfMaybeExp boundIDs ampl)
        out           = map (castBoolean . polyOfExp []) $ expandOutput boundIDs ovals
        sop           = Pathsum s 0 (length out) 0 pp out
        getID (id, _) = id
        sumvars       = concat . map vars $ pvars
        vars (id, t)  = case t of
          TypeInt n -> [varOfOffset id i | i <- [0..n-1]]
          TypeQubit -> [id]

createAncillaMask :: Spec -> Pathsum DMod2
createAncillaMask = go . inputs
  where 
    go [] = mempty
    go (a:as) = case a of
      (_, TypeQubit)     -> identity 1 <> go as
      (_, TypeInt n)     -> identity n <> go as
      (_, TypeAncilla n) -> (ket $ replicate n 0) <> go as


bitBlast :: ID -> Int -> Exp
bitBlast v n = foldl (\a b -> BOpExp a PlusOp b) (IntExp 0) [BOpExp (OffsetExp v i) TimesOp (powertwo i) | i <- [0..n-1]]
  where powertwo 0 = IntExp 1
        powertwo j = BOpExp (IntExp 2) TimesOp (powertwo $ j-1)

{- 1/28, I think need to expand int types recursively, to take care of exps like x + y both ints -}
expandInts :: [TypedID] -> [Exp] -> [Exp]
expandInts boundIDs = concat . map expand
  where 
    expand exp = case exp of
      VarExp v -> case lookup v boundIDs of
                  Nothing          -> error "Variable not bound"
                  Just TypeQubit   -> [VarExp v]
                  Just (TypeInt n) -> [OffsetExp v i | i <- [0..n-1]]
      e        -> [e]

lengthOfExp :: [TypedID] -> Exp -> Int
lengthOfExp boundIDs = go
  where 
    go e = case e of
      VarExp v -> case lookup v boundIDs of
                    Nothing              -> error "Variable not bound"
                    Just TypeQubit       -> 1
                    Just (TypeInt n)     -> n
                    Just (TypeAncilla n) -> n
      FloatExp _     -> 1
      IntExp _       -> 1
      PiExp          -> 1
      OffsetExp _ _  -> 1
      UOpExp _ e'    -> go e'
      BOpExp e1 _ e2 -> let l1 = go e1
                            l2 = go e2 in
                          if l1 == 1 || l2 == 1 || l1 == l2
                            then max l1 l2
                            else error "Variable length mismatch" 

expandOutput :: [TypedID] -> [Exp] -> [Exp]
expandOutput boundIDs = concat . map (expandOutputExp boundIDs)

{-
expandOutputExp :: [TypedID] -> Exp -> [Exp]
expandOutputExp boundIDs e = let l = lengthOfExp boundIDs e in
  map (expand e) [0..l-1]
  where 
    expand exp index = case exp of
      VarExp v -> case lookup v boundIDs of
                    Nothing -> error "Variable not bound"
                    Just TypeQubit ->       VarExp v
                    Just (TypeInt _) ->     OffsetExp v index
                    {- ancilla should be 0? or offset v i -}
                    Just (TypeAncilla _) -> IntExp 0
      BOpExp e1 bop e2 -> BOpExp (expand e1 index) bop (expand e2 index)
      UOpExp uop e     -> UOpExp uop (expand e index)
      OffsetExp _ _    -> exp
      FloatExp _       -> exp
      IntExp _         -> exp
      PiExp            -> exp
-}

expandOutputExp :: [TypedID] -> Exp -> [Exp]
expandOutputExp boundIDs e = let l = lengthOfExp boundIDs e in
  expand e
  where
    typeOf exp = case exp of
      VarExp v -> case lookup v boundIDs of
                    Nothing -> error "Variable not bound"
                    Just TypeQubit ->       TypeQubit
                    Just (TypeInt n) ->     TypeInt n
                    {- ancilla should not be allowed maybe? -}
                    Just (TypeAncilla n) -> TypeInt n
      BOpExp e1 _ e2 -> case (typeOf e1, typeOf e2) of
                          (TypeQubit, t) -> t
                          (t, TypeQubit) -> t
                          (TypeInt n, TypeInt m) | n == m -> TypeInt n
                          (TypeInt _, TypeInt _) -> error "length mismatch in spec"
      FloatExp _ -> TypeQubit
      IntExp _ -> TypeQubit
      PiExp -> TypeQubit
      OffsetExp _ _ -> TypeQubit
      UOpExp _ e -> typeOf e

    expand exp = case exp of
      VarExp v -> case lookup v boundIDs of
                    Nothing -> error "Variable not bound"
                    Just TypeQubit ->       [VarExp v]
                    Just (TypeInt n) ->     [OffsetExp v i | i <- [0..n-1]]
                    {- ancilla should be 0? or offset v i -}
                    Just (TypeAncilla n) -> [IntExp 0 | _ <- [0..n-1]]
      BOpExp e1 bop e2 ->
        case typeOf exp of
          TypeQubit -> [exp]
          TypeInt n -> [indexOf exp i | i <- [0..n-1]]
      UOpExp uop e     -> map (UOpExp uop) $ expand e
      OffsetExp _ _    -> [exp]
      FloatExp _       -> [exp]
      IntExp _         -> [exp]
      PiExp            -> [exp]

    indexOf exp (-1) = IntExp 0
    indexOf exp index = case exp of
      VarExp v -> case typeOf exp of
                    TypeQubit -> exp
                    TypeInt _ -> OffsetExp v index
      {- would we ever want to have x:qubit + y:int[n]? what should that mean -}
      BOpExp e1 bop e2    ->
        case (typeOf e1, typeOf e2) of
          (TypeQubit, _)         -> BOpExp e1 bop (indexOf e2 index)
          (_, TypeQubit)         -> BOpExp (indexOf e1 index) bop e2
          (TypeInt n, TypeInt _) -> 
            case bop of
              PlusOp -> BOpExp (BOpExp (indexOf e1 index) PlusOp (indexOf e2 index)) PlusOp (carryOf e1  e2 (index-1))
              op     -> BOpExp (indexOf e1 index) op (indexOf e2 index)
      UOpExp uop e        -> UOpExp uop (indexOf e index)

    carryOf e1 e2 index
      | index < 0 = IntExp 0
      | index == 0 = BOpExp (indexOf e1 index) TimesOp (indexOf e2 index)
      | otherwise  = 
          BOpExp (BOpExp (indexOf e1 index) TimesOp (indexOf e2 index))
            PlusOp (BOpExp (carryOf e1 e2 (index-1)) TimesOp (BOpExp (indexOf e1 (index)) PlusOp (indexOf e2 (index))))