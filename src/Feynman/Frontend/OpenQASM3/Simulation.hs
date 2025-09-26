module Feynman.Frontend.OpenQASM3.Simulation where

import Control.Monad.State.Strict
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromJust)
import qualified Data.List as List
import Feynman.Algebra.Base (DMod2)
import Feynman.Algebra.SArith
import Feynman.Algebra.Pathsum.Balanced
import Feynman.Core (ID)
import Feynman.Frontend.OpenQASM3.Core
import Feynman.Algebra.Polynomial.Multilinear (SBool, ofVar)
import Data.Bits (testBit, xor, (.>>.), (.&.))
import Data.Complex (realPart, imagPart)

import qualified Feynman.Util.Unicode as U

data Env a = Env {
  pathsum :: Pathsum DMod2,
  binds :: [Map ID (Binding a)],
  density :: Bool,
  qwidth :: Int                  -- number of allocated qubits
} deriving (Show)

data Binding a =
    Symbolic { typ :: Type a, offset :: Int }
  | Scalar { typ :: Type a, value :: Expr a }
  | Block { typ :: Type a, params :: [(ID, Type a)], returns :: Maybe (Type a), body :: Stmt a }
  deriving (Show)

getQWidth :: State (Env a) Int
getQWidth = gets qwidth

getCWidth :: State (Env a) Int
getCWidth = gets go
  where
    go (Env ps _ False qwidth) = outDeg ps - qwidth
    go (Env ps _ True  qwidth) = outDeg ps - 2*qwidth

{-
getEnvSize :: State (Env a) Int
getEnvSize = gets go
  where
    go (Env ps _ i)  = (outDeg ps - i) `div` 2
-}

getOffset :: ID -> State (Env a) Int
getOffset id = do
  bind <- searchBinding id
  case bind of
    Just (Symbolic _ offset) -> return offset
    Just _                   -> error "not a symbolic variable"
    Nothing                  -> error "binding not found"

evalOffset :: Expr a -> State (Env a) Int
evalOffset expr = case expr of
  EVar vid     -> getOffset vid
  EIndex e1 e2 -> do
    offset <- evalOffset e1
    index <- simInt e2
    return $ offset + index
  _ -> error "cannot find offset"

-- | Gives the unicode representation of the ith offset of v
varOfOffset :: ID -> Int -> String
varOfOffset v i = U.sub v (fromIntegral i)

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

{-
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
-}

-- TODO: size redundant if list given. replace with Either?
allocateQBits :: ID -> Int -> Maybe [SBool String] -> State (Env a) Int
allocateQBits v size init = do
  offset <- getQWidth
  modify $ allocateQ
  return $ offset 
  where
    qbits                              = case init of
      Nothing   -> ket $ [ofVar (varOfOffset v i) | i <- [0..size-1]]
      Just list -> ket $ list
    qbits'                             = case init of
      Nothing   -> ket $ [ofVar (varOfOffset ("'" ++ v) i) | i <- [0..size-1]]
      Just list -> ket $ list
    allocateQ env@(Env ps _ density w) = env { pathsum = newPs, qwidth = w + size }
      where
        psSize   = outDeg ps
        newOuts  = if density then qbits <> qbits' else qbits
        embedded = embed newOuts psSize (\i -> i) (\i -> if i < size then i + w else i + 2*w)
        newPs    = ps .> embedded

allocateCBits :: ID -> Int -> Maybe [SBool String] -> State (Env a) Int
allocateCBits v size init = do
  offset <- getCWidth
  modify $ allocateC
  return $ offset 
  where
    bits                                 = case init of
      Nothing   -> ket $ [ofVar (varOfOffset v i) | i <- [0..size-1]]
      Just list -> ket $ list
    allocateC env@(Env ps _ density w) = env { pathsum = newPs }
      where
        psSize   = outDeg ps
        embedded = embed bits psSize (\i -> i) (\i -> i + psSize)
        newPs    = ps .> embedded

measurePS :: Int -> Env a -> Env a
measurePS _      env@(Env _ _ False _)      = error "not density matrix"
measurePS offset env@(Env ps _ True qwidth) = env { pathsum = ps' }
  where
    ps' = applyMeasure offset (offset + qwidth) ps

bindParams :: [(ID, Type a)] -> [Expr a] -> State (Env a) ()
bindParams params args = mapM_ bindParam $ zip params args

-- no type checking
bindParam :: ((ID, Type a), Expr a) -> State (Env a) ()
bindParam ((pid, ptype), arg) = case (ptype, arg) of
  (TQBit, _)                 -> do
    offset <- evalOffset arg
    addBinding pid $ Symbolic ptype offset
  (TCBit, _)                 -> do
    offset <- evalOffset arg
    addBinding pid $ Symbolic ptype offset
  (TQReg (EInt n), EVar eid) -> do
    offset <- evalOffset arg
    addBinding pid $ Symbolic ptype offset
  (TCReg (EInt n), EVar eid) -> do
    offset <- evalOffset arg
    addBinding pid $ Symbolic ptype offset
  (TUInt (EInt n), EVar eid) -> do
    offset <- evalOffset arg
    addBinding pid $ Symbolic ptype offset
  (_, _)                     ->
    addBinding pid $ Scalar ptype arg
  
evalBool :: Expr a -> Maybe Bool
evalBool = error "TODO"

evalInt :: Expr a -> Maybe Int
evalInt expr = case expr of
  EInt n -> Just n
  EBool True -> Just 1
  EBool False -> Just 0
  _ -> Nothing

evalAngle = error "TODO"
evalFloat = error "TODO"
evalComplex = error "TODO"

initEnv :: Bool -> Env a
initEnv b = Env (ket []) [Map.empty] b 0

pushEmptyEnv :: State (Env a) ()
pushEmptyEnv =
  modify $ \env -> env { binds = Map.empty : binds env }

popEnv :: State (Env a) ()
popEnv =
  modify $ \env -> env { binds = tail $ binds env }

isValue :: Expr a -> Bool
isValue expr = case expr of
  EInt _   -> True
  EFloat _ -> True 
  ECmplx _ -> True
  EPi      -> True 
  EIm      -> True
  EBool _  -> True
  EStmt _  -> True
  ESet l   -> List.all isValue l
  EIndex x i -> isValue x && isValue i 

reduceExpr :: Expr a -> State (Env a) (Expr a)
reduceExpr expr = case expr of
  EInt _     -> return expr
  EFloat _   -> return expr
  ECmplx _   -> return expr
  EBool _    -> return expr
  EPi        -> return EPi
  EIm        -> return EIm
  EMeasure e -> do
    e' <- reduceExpr e
    return $ EMeasure e'
  EVar vid   -> do
    bind <- searchBinding vid
    case bind of
      Nothing             -> error "binding not found"
      Just (Scalar _ val) -> reduceExpr val
      Just _ -> return $ EVar vid
  EIndex x i -> do
    x' <- reduceExpr x
    i' <- reduceExpr i
    return $ EIndex x' i'
  ESet l     -> do
    l' <- mapM reduceExpr l
    return $ ESet l'
  ESlice start Nothing stop -> do
    start' <- reduceExpr start
    stop' <- reduceExpr stop
    return $ ESlice start' Nothing stop'
  ESlice start (Just step) stop -> do
    start' <- reduceExpr start
    step' <- reduceExpr step
    stop' <- reduceExpr stop
    return $ ESlice start' (Just step') stop'
  EUOp uop a -> do
    e <- reduceExpr a
    case (uop, e) of
      (SinOp     , _       ) -> return $ EFloat $ sin $ floatOf e
      (CosOp     , _       ) -> return $ EFloat $ cos $ floatOf e
      (TanOp     , _       ) -> return $ EFloat $ tan $ floatOf e
      (ArccosOp  , _       ) -> return $ EFloat $ acos $ floatOf e
      (ArcsinOp  , _       ) -> return $ EFloat $ asin $ floatOf e
      (ArctanOp  , _       ) -> return $ EFloat $ atan $ floatOf e
      (CeilOp    , _       ) -> return $ EInt $ ceiling $ floatOf e
      (FloorOp   , _       ) -> return $ EInt $ floor $ floatOf e
      (LnOp      , _       ) -> return $ EFloat $ log $ floatOf e --maybe need to check base
      (RealOp    , ECmplx c) -> return $ EFloat $ realPart c
      (RealOp    , _       ) -> return $ EFloat $ floatOf e
      (ImOp      , ECmplx c) -> return $ EFloat $ imagPart c
      (ImOp      , _       ) -> return $ EFloat 0.0              --maybe need to check type of e
      (NegOp     , _       ) -> error "TODO: need to clarify difference between neg and uminus"
      (UMinusOp  , _       ) -> error "TODO: need to clarify difference between neg and uminus"
      (PopcountOp, _       ) -> error "TODO"
  EBOp a bop b -> do
    e1 <- reduceExpr a
    e2 <- reduceExpr b
    case (bop, e1, e2) of
      (AndOp   , EBool b1 , EBool b2 ) -> return $ EBool $ b1 && b2
      (OrOp    , EBool b1 , EBool b2 ) -> return $ EBool $ b1 || b2
      (XorOp   , EBool b1 , EBool b2 ) -> return $ EBool $ b1 `xor` b2
--      (LShiftOp, _        , _        ) -> error "check: should work like rotl?"
--      (RShiftOp, _        , _        ) -> error "check: should work like rotr?"
      (LRotOp  , _        , _        ) -> error "check: how should this work for symbolic bvectors"
      (RRotOp  , _        , _        ) -> error "check: how should this work for symbolic bvectors"
      (EqOp    , EBool b1 , EBool b2 ) -> return $ EBool $ b1 == b2
      (EqOp    , EInt i1  , EInt i2  ) -> return $ EBool $ i1 == i2
      (EqOp    , EFloat f1, EFloat f2) -> return $ EBool $ f1 == f2
      (EqOp    , ECmplx c1, ECmplx c2) -> return $ EBool $ c1 == c2
--      (EqOp    , _        , _        ) -> error "constraint propagation? ex uint = int"
      (LTOp    , EInt i1  , EInt i2  ) -> return $ EBool $ i1 < i2
      (LTOp    , EFloat f1, EFloat f2) -> return $ EBool $ f1 < f2
      (LEqOp   , EInt i1  , EInt i2  ) -> return $ EBool $ i1 <= i2
      (LEqOp   , EFloat f1, EFloat f2) -> return $ EBool $ f1 <= f2
      (GTOp    , EInt i1  , EInt i2  ) -> return $ EBool $ i1 > i2
      (GTOp    , EFloat f1, EFloat f2) -> return $ EBool $ f1 > f2
      (GEqOp   , EInt i1  , EInt i2  ) -> return $ EBool $ i1 >= i2
      (GEqOp   , EFloat f1, EFloat f2) -> return $ EBool $ f1 >= f2
      (PlusOp  , EInt i1  , EInt i2  ) -> return $ EInt $ i1 + i2
      (PlusOp  , EFloat f1, EFloat f2) -> return $ EFloat $ f1 + f2
      (PlusOp  , ECmplx c1, ECmplx c2) -> return $ ECmplx $ c1 + c2
      (MinusOp , EInt i1  , EInt i2  ) -> return $ EInt $ i1 - i2
      (MinusOp , EFloat f1, EFloat f2) -> return $ EFloat $ f1 - f2
      (MinusOp , ECmplx c1, ECmplx c2) -> return $ ECmplx $ c1 - c2
      (TimesOp , EInt i1  , EInt i2  ) -> return $ EInt $ i1 * i2
      (TimesOp , EFloat f1, EFloat f2) -> return $ EFloat $ f1 * f2
      (TimesOp , ECmplx c1, ECmplx c2) -> return $ ECmplx $ c1 * c2 -- need to implement casting
      (DivOp   , EInt i1  , EInt i2  ) -> return $ EInt $ i1 `quot` i2 -- div?
      (DivOp   , EFloat f1, EFloat f2) -> return $ EFloat $ f1 / f2
      (DivOp   , ECmplx c1, ECmplx c2) -> return $ ECmplx $ c1 / c2
      (ModOp   , EInt i1  , EInt i2  ) -> return $ EInt $ i1 `mod` i2
      (PowOp   , EInt i1  , EInt i2  ) -> return $ EInt $ i1 ^ i2
      _                                -> return $ EBOp e1 bop e2    
      
floatOf :: Expr a -> Double
floatOf expr = case expr of
  EFloat f    -> f
  EInt i      -> fromIntegral i
  EPi         -> pi
  EBool False -> 0.0
  EBool True  -> 1.0
  _           -> error "cast to float forbidden or not handled"

simBool :: Expr a -> State (Env a) Bool
simBool expr = case expr of
  EVar vid -> do
    bind <- searchBinding vid
    case bind of
      Just (Scalar TBool (EBool b)) -> return b
      Just _                        -> error "not compile time bool" --symbolic cbit?
      Nothing                       -> error "binding not found"
  EBool b -> return b
  EUOp NegOp e -> do
    b <- simBool e
    return $ not b
  EBOp e1 bop e2 -> case bop of
    AndOp -> do
      b1 <- simBool e1
      b2 <- simBool e2
      return $ b1 && b2
    OrOp -> do
      b1 <- simBool e1
      b2 <- simBool e2
      return $ b1 || b2
    XorOp -> do
      b1 <- simBool e1
      b2 <- simBool e2
      return $ b1 `xor` b2
    EqOp -> do
      i1 <- simInt e1      -- need to either keep track of types of exps, or
      i2 <- simInt e2      -- reduce exps to some normal forms?
      return $ i1 == i2 
    LTOp -> do
      i1 <- simInt e1
      i2 <- simInt e2
      return $ i1 < i2
    LEqOp -> do
      i1 <- simInt e1
      i2 <- simInt e2
      return $ i1 <= i2
    GTOp -> do
      i1 <- simInt e1
      i2 <- simInt e2
      return $ i1 > i2
    GEqOp -> do
      i1 <- simInt e1
      i2 <- simInt e2
      return $ i1 >= i2

simInt :: Expr a -> State (Env a) Int
simInt expr = case expr of
  EVar vid -> do
    bind <- searchBinding vid
    case bind of
      Just (Scalar TInt (EInt n)) -> return n
      Just _                        -> error "not compile time int" --symbolic cbit?
      Nothing                       -> error "binding not found"
  EInt n -> return n

simList :: Expr a -> State (Env a) [Expr a]
simList expr = case expr of
  ESet l   -> return l
  EVar vid -> do
    bind <- searchBinding vid
    case bind of
      Just (Symbolic (TCReg (EInt n)) _) -> return [ EIndex (EVar vid) (EInt i) | i <- [0..n-1] ]
      Just (Symbolic (TQReg (EInt n)) _) -> return [ EIndex (EVar vid) (EInt i) | i <- [0..n-1] ]
      _ -> error "not a list"
  ESlice init step end -> do
    init' <- simInt init
    end' <- simInt end
    case step of
      Just s -> do
        step' <- simInt s
        return [ EInt j | i <- [init'..end'],
                          let j = i * step',
                          j <= end' ]
      Nothing -> return [ EInt i | i <- [init'..end']]
  _ -> error "not a list"

simStmt :: SBool Var -> Stmt a -> State (Env a) (Maybe (Expr a))
simStmt p stmt = case stmt of
  SInclude _ _               -> return Nothing
  SSkip _                    -> return Nothing
  SBarrier _ _               -> return Nothing
  SPragma _ _                -> return Nothing
  SBlock _ stmts             -> simBlock p stmts
  SWhile _ cond stmt         -> simWhile p cond stmt
  SIf _ cond stmtT stmtE     -> simIf p cond stmtT stmtE
  
  SReset _ expr              -> simReset expr >> return Nothing
  SDeclare _ decl            -> if p == 1 then
                                  simDeclare decl >> return Nothing
                                else
                                  error "invalid stmt in symbolic branch"
  SAssign _ path bop expr    -> simAssign p path bop expr >> return Nothing

  SAnnotated _ _ stmt        -> simStmt p stmt
  SFor _ (id, typ) expr stmt -> simFor p (id, typ) expr stmt
  SReturn _ e                -> liftM Just $ reduceExpr e
  SExpr _ expr               -> simExpr p expr >> return Nothing

simBlock :: SBool Var -> [Stmt a] -> State (Env a) (Maybe (Expr a))
simBlock p = foldM f Nothing
  where
    f (Just r) _    = return $ Just r
    f Nothing  stmt = simStmt p stmt

simWhile :: SBool Var -> Expr a -> Stmt a -> State (Env a) (Maybe (Expr a))
simWhile p cond stmt = do
  cond' <- simBool cond --symbolic branching?
  case cond' of
    True  -> do
      ret <- simStmt p stmt
      case ret of
        Nothing -> simWhile p cond stmt
        Just e  -> return $ Just e
    False -> return Nothing

simIf :: SBool Var -> Expr a -> Stmt a -> Stmt a -> State (Env a) (Maybe (Expr a))
simIf p cond stmtT stmtE = do
  cond' <- reduceExpr cond
  case cond' of
    EBool True  -> simStmt p stmtT
    EBool False -> simStmt p stmtE
    e           -> do
      q <- polyOfExpr e
      simStmt (p*q) stmtT
      simStmt (p*(1+q)) stmtE

simFor :: SBool Var -> (ID, Type a) -> Expr a -> Stmt a -> State (Env a) (Maybe (Expr a))
simFor p (id, typ) expr stmt = do
  list <- simList expr
  foldM iter Nothing list
  where
    iter (Just r) _ = return $ Just r
    iter Nothing  e = do
      pushEmptyEnv
      bindParam ((id, typ), e)
      ret <- simStmt p stmt
      popEnv
      return ret 

listOpOfBOp :: BinOp -> [SBool Var] -> [SBool Var] -> [SBool Var]
listOpOfBOp bop = case bop of
  AndOp    -> sAnd
  OrOp     -> sOr
  XorOp    -> sXor
  LShiftOp -> sLShift
  RShiftOp -> sRShift
  LRotOp   -> sLRot
  RRotOp   -> sRRot
  PlusOp   -> sPlus
  MinusOp  -> sMinus
  TimesOp  -> sMult 
  DivOp    -> sQuot
  ModOp    -> sMod
  PowOp    -> sPow
  ConcatOp -> error "++ not supported"
  _        -> error "given bop does not output list of polynomials"

boolOpOfBop :: BinOp -> [SBool Var] -> [SBool Var] -> SBool Var
boolOpOfBop bop = case bop of
  EqOp  -> sEq
  LTOp  -> sLT 
  LEqOp -> sLEq
  GTOp  -> sGT
  GEqOp -> sGEq
  _     -> error "given bop does not output boolean polynomial"

listOpOfUop :: UOp -> [SBool Var] -> [SBool Var]
listOpOfUop uop = case uop of
  NegOp    -> sNot
  UMinusOp -> sNeg
  _        -> error "given uop does not output list of polynomials"

exprOfPath :: AccessPath a -> Expr a
exprOfPath path = case path of
  AVar id     -> EVar id
  AIndex id e -> EIndex (EVar id) e

exprOfAssign :: AccessPath a -> Maybe BinOp -> Expr a -> Expr a
exprOfAssign _    Nothing    expr = expr
exprOfAssign path (Just bop) expr = EBOp (exprOfPath path) bop expr

simAssign :: SBool Var -> AccessPath a -> Maybe BinOp -> Expr a -> State (Env a) ()
simAssign p path maybeBop expr = case path of
  AVar id     -> do
    maybeBind <- searchBinding id
    case maybeBind of
      Nothing                    -> error "id not bound"
      Just (Scalar typ e)        -> if p == 1 then do
                                      e' <- reduceExpr e
                                      declareScalar id typ (Just $ e')
                                    else
                                      error "bad symbolic branching" 
      Just (Symbolic typ offset) -> simSymbolicAssign p offset typ (exprOfAssign path maybeBop expr)
  AIndex id i -> do
    maybeBind <- searchBinding id
    i' <- reduceExpr i
    case i' of
      EInt j ->
        case maybeBind of
          Nothing                    -> error "id not bound"
          Just (Scalar typ e)        -> error "not sure if allowed"
          Just (Symbolic typ offset) -> simSymbolicAssign p (offset + j) TCBit (exprOfAssign path maybeBop expr)
      _ -> error "index is not an int value"

simSymbolicAssign :: SBool Var -> Int -> Type a -> Expr a -> State (Env a) ()
simSymbolicAssign p offset typ expr =
  case typ of
    TCBit          -> do
      poly <- polyOfExpr expr
      modify $ f [poly]
    TCReg (EInt _) -> do
      polys <- polyListOfExpr expr
      modify $ f polys 
    TUInt (EInt _) -> do
      polys <- polyListOfExpr expr
      modify $ f polys 
  where
    f polyl env@(Env ps@(Pathsum _ _ _ _ _ out) _ density qwidth) =
      let n            = length polyl
          (qreg, creg) = splitAt (if density then 2*qwidth else qwidth) out
          oldList      = drop offset . take (offset + n) $ creg
          newList      = zipWith (\old new -> p*new + (1+p)*old) oldList polyl
          newCreg      = take offset creg ++ newList ++ drop (offset + n) creg in
        env { pathsum = ps { outVals = qreg ++ newCreg } }

{-
simAssign path (Just bop) expr = case path of
  AVar id -> do
    maybeBind <- searchBinding id
    case maybeBind of
      Nothing                     -> error "id not bound"
      Just (Symbolic typ offset) -> case (typ, bop) of
        (TCBit, AndOp) -> do
          l1 <- polyListOfExpr EVar id
          l2 <- polyListOfExpr expr
          polyListAnd l1 l2 
-}

polyOfExpr :: Expr a -> State (Env a) (SBool Var)
polyOfExpr expr = case expr of
  EVar vid     -> do
    maybeBind <- searchBinding vid
    case maybeBind of
      Nothing                    -> error "id not bound"
      Just (Symbolic typ offset) -> case typ of
        TCBit -> gets $ g offset
        _     -> error "symbolic type not polynomial list"
  EIndex e1 e2 -> do
    l <- polyListOfExpr e1
    e2' <- reduceExpr e2
    case e2' of
      EInt i -> return $ l !! i
      _      -> error "expr not int value"
  EBool True  -> return 1
  EBool False -> return 0
  EBOp e1 bop e2 -> do             -- need to handle cases where e1 and e2 are bool type
    l1 <- polyListOfExpr e1
    l2 <- polyListOfExpr e2
    return $ (boolOpOfBop bop) l1 l2
  EMeasure expr -> do
    offset <- evalOffset expr
    modify $ measurePS offset
    gets $ \env -> (!! offset) . outVals $ pathsum env
  where
    g j (Env (Pathsum _ _ _ _ _ out) _ False qwidth) = out !! (j + qwidth)
    g j (Env (Pathsum _ _ _ _ _ out) _ True  qwidth) = out !! (j + 2*qwidth)

polyListOfExpr :: Expr a -> State (Env a) [SBool Var]
polyListOfExpr expr = case expr of
  EVar vid       -> do
    maybeBind <- searchBinding vid
    case maybeBind of
      Nothing                    -> error "id not bound"
      Just (Symbolic typ offset) -> case typ of
        TCReg (EInt n) -> gets $ g offset n
        TUInt (EInt n) -> gets $ g offset n
        _              -> error "symbolic type not polynomial list"
  EInt n         -> return $ makeSNat . toInteger $ n
  EBOp e1 bop e2 -> do
    l1 <- polyListOfExpr e1
    l2 <- polyListOfExpr e2
    return $ (listOpOfBOp bop) l1 l2
  EUOp uop e     -> do
    l <- polyListOfExpr e
    return $ (listOpOfUop uop) l
  EIndex e1 e2   -> do
    p <- polyOfExpr expr
    return $ [p]
  where
    g start len (Env (Pathsum _ _ _ _ _ out) _ False qwidth) = take len . drop (start + qwidth) $ out
    g start len (Env (Pathsum _ _ _ _ _ out) _ True  qwidth) = take len . drop (start + 2*qwidth) $ out

declareSymbolic :: ID -> Type a -> Int -> Maybe [SBool String] -> State (Env a) ()
declareSymbolic id typ size init = do
  offset <- f id size init
  addBinding id (Symbolic typ offset)
  where
    f = case typ of
      TCBit   -> allocateCBits
      TCReg _ -> allocateCBits
      TUInt _ -> allocateCBits
      TQBit   -> allocateQBits
      TQReg _ -> allocateQBits

declareScalar :: ID -> Type a -> Maybe (Expr a) -> State (Env a) ()
declareScalar id typ maybeExpr = do
  expr <- getExpr
  addBinding id (Scalar typ expr)
  where
    getExpr = case maybeExpr of
      Just e  -> reduceExpr e            -- eval first?
      Nothing -> return $ case typ of
        TAngle -> EFloat 0 
        TBool  -> EBool False -- true?
        TInt   -> EInt 0
        TFloat -> EFloat 0
        TCmplx -> ECmplx 0

declareBlock :: ID -> [(ID, Type a)] -> Maybe (Type a) -> Stmt a -> State (Env a) ()
declareBlock id params returns body = let (_, sig) = unzip params in
  addBinding id (Block (TProc sig) params returns body)

simDeclare :: Decl a -> State (Env a) ()
simDeclare decl = case decl of
  DVar vid typ val -> case typ of
    TCBit   -> case val of
      Nothing -> declareSymbolic vid TCBit 1 Nothing
      Just v  -> case evalBool v of
        Just False -> declareSymbolic vid TCBit 1 (Just [0])
        Just True  -> declareSymbolic vid TCBit 1 (Just [1])
        Nothing    -> error $ "invalid value in declaration"
    TCReg n -> case evalInt n of
      Nothing   -> error $ "invalid register size"
      Just size -> case val of
        Nothing       -> declareSymbolic vid (TCReg $ EInt size) size Nothing
        Just (EInt j) -> declareSymbolic vid (TCReg $ EInt size) size (Just $ bitVec j size)
    TQBit   -> case val of
      Nothing -> declareSymbolic vid TQBit 1 Nothing
      Just v  -> case evalBool v of
        Just False -> declareSymbolic vid TQBit 1 (Just [0])
        Just True  -> declareSymbolic vid TQBit 1 (Just [1])
        Nothing    -> error $ "invalid value in declaration"
    TQReg n -> case evalInt n of
      Nothing   -> error $ "invalid register size"
      Just size -> case val of
        Nothing -> declareSymbolic vid (TQReg $ EInt size) size Nothing
        Just _  -> error $ "invalid array value"
    TUInt n -> case evalInt n of
      Nothing   -> error $ "invalid register size"
      Just size -> case val of
        Nothing -> declareSymbolic vid (TUInt $ EInt size) size Nothing
        Just v  -> case evalInt v of
          Nothing -> error $ "invalid uint value"
          Just i  -> declareSymbolic vid (TUInt $ EInt size) size (Just $ bitVec i size)
    TAngle  -> case val of
      Nothing -> declareScalar vid TAngle Nothing
      Just v  -> case evalAngle v of
        Nothing -> error $ "invalid angle value"
        Just f  -> declareScalar vid TAngle (Just $ EFloat f)
    TBool   -> case val of
      Nothing -> declareScalar vid TBool Nothing
      Just v  -> case evalBool v of
        Nothing -> error $ "invalid bool value"
        Just b  -> declareScalar vid TBool (Just $ EBool b)
    TInt    -> case val of
      Nothing -> declareScalar vid TInt Nothing
      Just v  -> case evalInt v of
        Nothing -> error $ "invalid int value"
        Just i  -> declareScalar vid TInt (Just $ EInt i)
    TFloat  -> case val of
      Nothing -> declareScalar vid TFloat Nothing
      Just v  -> case evalFloat v of
        Nothing -> error $ "invalid float value"
        Just f  -> declareScalar vid TFloat (Just $ EFloat f)
    TCmplx  -> case val of
      Nothing -> declareScalar vid TCmplx Nothing
      Just v  -> case evalComplex v of
        Nothing -> error $ "invalid complex value"
        Just c  -> declareScalar vid TCmplx (Just $ ECmplx c)
  DDef did dparams dreturns dbody -> declareBlock did dparams dreturns dbody
  DExtern _ _ _ -> error "TODO"
  DAlias  _ _   -> error "TODO"

bitVec :: Int -> Int -> [SBool String]
bitVec n size = map f [0..size-1]
  where
    f i = if testBit n i then 1 else 0

stdlib = ["x", "y", "z", "h", "cx", "cy", "cz", "ch", "id", "s", "sdg", "t", "tdg", "rz", "rx", "ry", "ccx", "crz", "u3", "u2", "u1", "cu1", "cu3"]

applyPS :: Pathsum DMod2 -> SBool Var -> [Int] -> State (Env a) ()
applyPS gatePS p offsets = modify $ f
  where
    f env@(Env ps _ False _) = env { pathsum = applyPControlled gatePS p offsets ps }
    f env@(Env ps _ True qwidth) = 
      let offsets' = map (+qwidth) offsets in
        env { pathsum = applyPControlled gatePS p offsets' . applyPControlled gatePS p offsets $ ps }

simStdGate :: SBool Var -> ID -> [Expr a] -> [Expr a] -> State (Env a) ()
simStdGate p gid cparams args = do
  gatePS <- getGatePS gid cparams
  offsets <- mapM evalOffset args
  env <- get
  applyPS gatePS p offsets

simExpr :: SBool Var -> Expr a -> State (Env a) (Maybe (Expr a))
simExpr p (EStmt stmt) = simStmt p stmt
simExpr p (ECall [] gid args)
  | gid `elem` stdlib  = do
      simStdGate p gid [] args
      return Nothing
    
simExpr p (ECall [] fid args) = do
  bind <- searchBinding fid
  args' <- (liftM $ map fromJust) $ mapM (simExpr p) args
  case bind of
    Just (Block _ params _ body) -> do
      pushEmptyEnv
      bindParams params args'
      ret <- simStmt p body
      popEnv
      return ret
    Nothing                      -> error "binding not found"

simExpr p expr = liftM Just $ reduceExpr expr

getGatePS :: ID -> [Expr a] -> State (Env a) (Pathsum DMod2)
getGatePS id params = case (id, params) of
  ("x", [])   -> return $ xgate
  ("y", [])   -> return $ ygate
  ("z", [])   -> return $ zgate
  ("h", [])   -> return $ hgate
  ("cx", [])  -> return $ cxgate
  ("cy", [])  -> return $ controlled ygate
  ("cz", [])  -> return $ czgate
  ("ch", [])  -> return $ controlled hgate 
  ("id", [])  -> return $ identity 1
  ("s", [])   -> return $ sgate
  ("sdg", []) -> return $ sdggate
  ("t", [])   -> return $ tgate
  ("tdg", []) -> return $ tdggate
  ("ccx", []) -> return $ ccxgate
  _           -> error "TODO"

simReset :: Expr a -> State (Env a) ()
simReset expr = case expr of
  EVar id -> do
    bind <- searchBinding id
    case bind of
      Nothing -> return ()
      Just (Symbolic TQBit offset) -> modify $ resetOffset offset
      Just (Symbolic (TQReg (EInt n)) offset) -> mapM_ modify [resetOffset i | i <- [offset..offset+n-1] ] 

  where
    resetOffset offset env@(Env ps@(Pathsum _ _ _ _ _ out) _ False _)     =
      env { pathsum = resetPS offset ps }
    resetOffset offset env@(Env ps@(Pathsum _ _ _ _ _ out) _ True qwidth) =
      env { pathsum = resetPS (offset + qwidth) . resetPS offset $ ps }

    resetPS offset ps@(Pathsum _ _ _ _ _ out) = ps { outVals = newOut }
      where
        newOut = take offset out ++ [0] ++ drop (offset + 1) out 

simStmts :: [Stmt a] -> State (Env a) ()
simStmts = mapM_ $ simStmt 1

simProgPure :: Prog a -> Env a
simProgPure (Prog _ stmts) = execState (simStmts stmts) (initEnv False)

simProg :: Prog a -> Env a
simProg (Prog _ stmts) = execState (simStmts stmts) (initEnv True)

simulationResult :: Prog a -> String
simulationResult prog = 
  let env = simProg prog in
    show (pathsum env)   
       
