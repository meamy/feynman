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
    Symbolic { typ :: Type a, offset :: Int }
  | Scalar { typ :: Type a, value :: Expr a }
  | Block { typ :: Type a, params :: [(ID, Type a)], returns :: Maybe (Type a), body :: Stmt a }
  deriving (Show)

getEnvSize :: State (Env a) Int
getEnvSize = gets go
  where
    go (Env ps _ False) = outDeg ps 
    go (Env ps _ True)  = outDeg ps `div` 2

getOffset :: ID -> State (Env a) Int
getOffset id = do
  bind <- searchBinding id
  case bind of
    Just (Symbolic _ offset) -> return offset
    Just _                   -> error "not a symbolic variable"
    Nothing                  -> error "binding not found"

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

bindParams :: [(ID, Type a)] -> [Expr a] -> State (Env a) ()
bindParams params args = mapM_ bindParam $ zip params args

-- no type checking
bindParam :: ((ID, Type a), Expr a) -> State (Env a) ()
bindParam ((pid, ptype), arg) = case arg of
  EVar eid            -> do
    offset <- getOffset eid
    addBinding pid $ Symbolic ptype offset
  EIndex (EVar eid) i -> do
    offset <- getOffset eid
    index <- simInt i
    addBinding pid $ Symbolic ptype (offset + index)
  e                   ->
    addBinding pid $ Scalar ptype e
  
evalBool :: Expr a -> Maybe Bool
evalBool = error "TODO"

evalInt :: Expr a -> Maybe Int
evalInt = error "TODO"

evalAngle = error "TODO"
evalFloat = error "TODO"
evalComplex = error "TODO"

initEnv :: Env a
initEnv = Env (ket []) [Map.empty] False

pushEmptyEnv :: State (Env a) ()
pushEmptyEnv =
  modify $ \env -> env { binds = Map.empty : binds env }

popEnv :: State (Env a) ()
popEnv =
  modify $ \env -> env { binds = tail $ binds env }

simBool :: Expr a -> State (Env a) Bool
simBool expr = case expr of
  EVar vid -> do
    bind <- searchBinding vid
    case bind of
      Nothing                       -> error "binding not found"
      Just (Scalar TBool (EBool b)) -> return b

simInt :: Expr a -> State (Env a) Int
simInt = error "TODO"

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

simStmt :: Stmt a -> State (Env a) ()
simStmt stmt = case stmt of
  SInclude _ _               -> return ()
  SSkip _                    -> return ()
  SBarrier _ _               -> return ()
  SPragma _ _                -> return ()
  SBlock _ stmts             -> mapM_ simStmt stmts
  SWhile _ cond stmt         -> simWhile cond stmt
  SIf _ cond stmtT stmtE     -> simIf cond stmtT stmtE
  
  SReset _ expr              -> simReset expr
  SDeclare _ decl            -> simDeclare decl
  SAssign _ p bop expr       -> simAssign p bop expr

  SAnnotated _ _ stmt        -> simStmt stmt
  SFor _ (id, typ) expr stmt -> simFor (id, typ) expr stmt
  SReturn _ _                -> return ()
  SExpr _ expr               -> simExpr expr 

simWhile :: Expr a -> Stmt a -> State (Env a) ()
simWhile cond stmt = do
  cond' <- simBool cond
  case cond' of
    True  -> do
      simStmt stmt
      simWhile cond stmt
    False -> return ()

simIf :: Expr a -> Stmt a -> Stmt a -> State (Env a) ()
simIf cond stmtT stmtE = do
  cond' <- simBool cond
  case cond' of
    True  -> simStmt stmtT
    False -> simStmt stmtE

simFor :: (ID, Type a) -> Expr a -> Stmt a -> State (Env a) ()
simFor (id, typ) expr stmt = do
  list <- simList expr
  mapM_ iter list
  where
    iter e = do
      pushEmptyEnv
      bindParam ((id, typ), e)
      simStmt stmt
      popEnv

simAssign :: AccessPath a -> Maybe BinOp -> Expr a -> State (Env a) ()
simAssign path Nothing expr = case path of
  AVar id     -> error "TODO"
  AIndex id i -> error "TODO"

declareSymbolic :: ID -> Type a -> Int -> Maybe [SBool String] -> State (Env a) ()
declareSymbolic id typ size init = do
  offset <- allocatePathsum id size init
  addBinding id (Symbolic typ offset)

declareScalar :: ID -> Type a -> Maybe (Expr a) -> State (Env a) ()
declareScalar id typ expr = addBinding id (Scalar typ expr')
  where
    expr' = case expr of
      Just e  -> e
      Nothing -> case typ of
        TAngle -> EFloat 0 
        TBool  -> EBool False --true?
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
        Nothing -> declareSymbolic vid (TCReg $ EInt size) size Nothing
        Just _  -> error $ "invalid array value"
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

simExpr :: Expr a -> State (Env a) ()
simExpr (EStmt stmt)             = simStmt stmt
simExpr (ECall [] fid args) = do
  bind <- searchBinding fid
  case bind of
    Just (Block _ params _ body) -> do
      pushEmptyEnv
      bindParams params args
      simStmt body
      popEnv
    Nothing                      -> error "binding not found"

simReset :: Expr a -> State (Env a) ()
simReset = error "TODO"

simStmts :: [Stmt a] -> State (Env a) ()
simStmts = mapM_ simStmt

simProg :: Prog a -> Env a
simProg (Prog _ stmts) = execState (simStmts stmts) initEnv
