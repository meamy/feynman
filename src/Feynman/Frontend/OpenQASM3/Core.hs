{-|
Module      : Core
Description : Core openQASM 3 abstract syntax
Copyright   : (c) Matthew Amy, 2025
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Feynman.Frontend.OpenQASM3.Core where

import qualified Feynman.Frontend.OpenQASM3.Syntax as S

{- Translation errors -}
data ErrMsg = Err String

{- Convenience types -}
type Annotation = String
type Version    = (Int, Maybe Int)

{- Core AST -}
data Type = TCBit       -- Symbolic
          | TCReg Expr  -- Symbolic
          | TQBit       -- Symbolic
          | TQReg Expr  -- Symbolic
          | TUInt Expr  -- Symbolic
          | TAngle
          | TBool
          | TInt
          | TFloat
          | TCmplx
          | TProc [Type]
          deriving (Show)

data AccessPath = AVar ID
                | AIndex ID Index
                deriving (Show)

data Index = IIndex Expr
           | ISlice Expr (Maybe Expr) Expr -- Inclusive on both ends
           | ISet [Expr]
           deriving (Show)
                    
data Expr = EVar ID
          | EIndex Expr Index
          | ECall ID [Expr]
          | EMeasur Expr
          | EInt Int
          | EFloat Double
          | EPi
          | EIm
          | EBool Bool
          | EUOp UOp Exp
          | EBOp Exp BinOp Exp
          | ECtrl [Expr] Expr
          | EInv Expr
          deriving (Show)

data UOp = SinOp
         | CosOp
         | TanOp
         | ArccosOp
         | ArcsinOp
         | ArctanOp
         | CeilOp
         | FloorOp
         | ExpOp
         | LnOp
         | SqrtOp
         | RealOp
         | ImOp
         | NegOp -- ~, !
         | UMinusOp -- -
         | PopcountOp -- popcount
         deriving (Show)

data BinOp = AndOp -- &, &&
           | OrOp  -- |, ||
           | XorOp -- ^
           | LShiftOp  -- <<
           | RShiftOp -- >>
           | LRotOp  -- rotl
           | RRotOp -- rotr
           | EqOp -- ==
           | LTOp -- <
           | LEqOp -- <=
           | RTOp -- >
           | REqOp -- >=
           | PlusOp -- +
           | MinusOp -- -
           | TimesOp -- *
           | DivOp -- / 
           | ModOp -- %
           | PowOp -- **
           | ConcatOp -- ++, not used in openQASM 3 spec
           deriving (Show)

data Decl =
    DVar { vid :: ID, typ :: Type, val :: Maybe Expr }
  | DDef { did :: ID, dparams :: [(ID, Type)], dreturns :: (Maybe Type), dbody :: Stmt }
  | DExtern { eid :: ID, eparams :: [Type], ereturns :: (Maybe Type) }
  | DAlias { aid :: ID, aexps :: [Expr] }
  deriving (Show)

data Stmt a =
    SInclude a String
  | SSkip a
  | SDeclare a Decl
  | SBarrier a [AccesPath]
  | SBlock a [Stmt]
  | SExpr a Expr
  | SAssign a AccessPath (Maybe BinOp) Expr
  | SFor a (ID, Type) Expr Stmt
  | SIf a Expr Stmt Stmt
  | SReset a Expr
  | SReturn a Expr
  | SWhile a Expr Stmt
  | SAnnotated a Annotation Stmt
  | SPragma a String
  deriving (Show)

-- Top level core QASM3 programs
data Prog = Prog Version [Stmt]

{- Utilities -}

-- | Gets the identifier being declared
declID :: Decl -> ID
declID decl = case decl of
  (DVar id _) -> id
  (DDef id _ _ _) -> id
  (DExtern id _ _) -> id
  (DAlias id _) -> id

{- Translation passes -}

-- | Translation from concrete syntax to the core subset
qasmToCore :: S.ParseNode -> Either ErrMsg Prog
qasmToCore = translateProg

-- | Top-level translation
translateProg :: S.ParseNode -> Either ErrMsg Prog
translateProg node = case node of
  S.Node (S.Program i j _) xs _ -> mapM translateStmt xs >>= return . Prog (i,j)
  _                             -> Left (Err "Malformed AST node: " ++ show node)

-- | Type translations
translateType :: S.ParseNode -> Either ErrMsg Type
translateType node = case node of
  S.Node S.BitTypeSpec [NilNode]  -> return $ TCBit
  S.Node S.BitTypeSpec [exprnode] -> translateExpr exprnode >>= return . TCReg

  S.Node S.IntTypeSpec _ -> return $ TInt

  S.Node S.UIntTypeSpec [NilNode]  -> return $ TUInt (EInt 32)
  S.Node S.UIntTypeSpec [exprnode] -> translateExpr exprnode >>= return . TUInt

  S.Node S.FloatTypeSpec _ -> return $ TFloat

  S.Node S.AngleTypeSpec _ -> return $ TAngle

  S.Node S.BoolTypeSpec _ -> return $ TBool

  S.Node S.DurationTypeSpec _ -> return $ TFloat

  S.Node S.StretchTypeSpec _ -> return $ TFloat

  S.Node S.ComplexTypeSpec _ -> return $ TCmplx

  S.Node S.CRegTypeSpec [NilNode]  -> return $ TCBit
  S.Node S.CRegTypeSpec [exprnode] -> translateExpr exprnode >>= return . TCReg

  S.Node S.QRegTypeSpec [NilNode]  -> return $ TQBit
  S.Node S.QRegTypeSpec [exprnode] -> translateExpr exprnode >>= return . TQReg

  S.Node S.QubitTypeSpec [NilNode]  -> return $ TQBit
  S.Node S.QubitTypeSpec [exprnode] -> translateExpr exprnode >>= return . TQReg

  S.Node S.ArrayTypeSpec _ ->
    Left (Err "Array types unsupported")

  S.Node S.ReadonlyArrayRefTypeSpec _ ->
    Left (Err "Array types unsupported")

  S.Node S.MutableArrayRefTypeSpec _ ->
    Left (Err "Array types unsupported")

-- | Identifier translations
translateIdent :: S.ParseNode -> Either ErrMsg ID
translateIdent node = case node of
  S.Node (S.Identifier id _) -> return id
  _                          -> Left (Err "Malformed identifier: " ++ show node)

-- | Access path translations
translateAccessPath :: S.ParseNode -> Either ErrMsg AccessPath
translateAccessPath node = case node of
  S.Node (S.HardwareQubit idx _) -> return $ AVar ("$" ++ show idx)

  S.Node S.IndexedIdentifier [idnode, idxlist] -> do
    id <- translateIdent idnode
    idxs <- inLst translateIndex idxlist
    case idxs of
      [idx] -> return $ AIndex id idx
      _     -> Left (Err "Error at " ++ (pp_source c) ++ ": Multiple indices unsupported")

  _                          -> Left (Err "Malformed access path: " ++ show node)

-- | Index translations
translateIndex :: S.ParseNode -> Either ErrMsg Index
translateIndex node = case node of
  S.Node S.RangeInitExpr [beginnode, stepnode, endnode] -> do
    begin <- translateExpr beginnode
    step <- (case stepnode of NilNode -> return Nothing; node -> translateExpr stepnode)
    end <- translateExpr endnode
    return $ ISlice begin step end

  S.Node S.SetInitExpr exprs -> do
    mapM translateExpr exprs >>= return . ISet
    
  S.Node _ _ -> do
    idx <- translateExpr node
    return $ IIndex idx

-- | Translation of Expressions
translateExpr :: S.ParseNode -> Either ErrMsg Expr

-- | Translation of statements
translateStmt S.ParseNode -> Either ErrMsg (Stmt SourceRef)
translateStmt node = case node of
  S.Node (S.Pragma str _) [] c -> return $ SPragma c str

  S.Node S.Statement [stmt, S.Node (S.Annotation _ str _)] c ->
    translateStmt stmt >>= return . SAnnotated c str 

  S.Node S.Scope stmts c ->
    mapM translateStmt stmts >>= return . SBlock c

  S.Node S.AliasDeclStmt (idnode:exprnodes) c -> do
    id <- translateIdent idnode
    exprs <- mapM translateExpr exprnodes
    return $ SDeclare c (DAlias id exprs)

  S.Node (S.AssignmentStmt op) [idnode, exprnode] c -> do
    idexpr <- translateAccessPath idnode
    expr <- translateExpr exprnode
    assop <- translateCompoundAOp op
    return $ SAssign c idexpr assop expr

  S.Node (S.BarrierStmt) [idnodes] c ->
    idexprs <- mapM translateAccessPath idnodes
    return $ SBarrier x idexprs

  S.Node S.Box [_, scope@(S.Node S.Scope _ _)] _ -> translateStmt scope

  S.Node S.Break [] c -> left (Err $ "Error at " ++ (pp_source c) ++ ": Break unsupported")

  S.Node (S.CalStmt _) [] c -> return $ SSkip c
  S.Node (S.DefcalgrammarStmt _ _) [] c -> return $ SSkip c

  S.Node S.ClassicalDeclStmt [typespec, ident, initexpr] c -> do
    ty <- translateType typespec
    id <- translateIdent ident
    expr <- (case initexpr of NilNode -> return Nothing; node -> translateExpr node)
    return $ SDeclare c (DVar id ty expr)

  S.Node S.ConstDeclStmt [typespec, ident, initexpr] c -> do
    ty <- translateType typespec
    id <- translateIdent ident
    expr <- translateExpr initexpr
    return $ SDeclare c (DVar id ty (Just expr))

  S.Node S.Continue [] c   -> left (Err $ "Error at " ++ (pp_source c) ++ ": Continue unsupported")

  S.Node S.DefStmt [idnode, argnodes, rettype, stmt] -> do
    id <- translateIdent ident
    args <- inLst translateArg argnodes
    ret <- (case rettype of NilNode -> return Nothing; node -> translateType node)
    body <- translateStmt stmt
    return $ SDeclare c (DDef id args ret body)

  S.Node S.DefcalStmt _ c -> return $ SSkip c

  S.Node S.DelayStmt _ c -> return $ SSkip c

  S.Node S.End [] c   -> left (Err $ "Error at " ++ (pp_source c) ++ ": End unsupported")

  S.Node S.Expression [exprnode] -> 
    translateExpr exprnode >>= return . SExpr c

  S.Node S.ExternStmt [idnode, typenodes, rettype] -> do
    id <- translateIdent ident
    types <- inLst translateType typenodes
    ret <- (case rettype of NilNode -> return Nothing; node -> translateType node)
    return $ SDeclare c (DExtern id types ret)

  S.Node S.ForStmt [typenode, idnode, exprnode, stmtnode] ->
    typ <- translateType typenode
    id <- translateIdent ident
    expr <- translateExpr exprnode
    body <- translateStmt stmtnode
    return $ SFor (id, typ) expr body

  S.Node S.GateStmt [idnode, cargnodes, qargnodes, stmt] -> do
    id <- translateIdent ident
    cargs <- (case cargnodes of NilNode -> return []; node -> inLst translateIdent node)
    qargs <- inLst translateIdent qargnodes
    body <- translateStmt stmt
    let args = zip cargs (repeat TCmplx) ++ zip qargs (repeat QBit)
    return $ SDeclare c (DDef id args Nothing body)

  S.Node S.GateCallStmt [modnodes, idnode, paramnodes, _, argnodes] ->
    modifiers <- inLst translateModifiers modifiers
    id <- translateIdent ident
    params <- inLst translateExpr paramnodes
    args <- inLst translateExpr argnodes
    return $ SExpr c (ECall id (params ++ args))
    
  S.Node S.IfStmt [condnode, thennode, elsenode] ->
    cond <- translateExpr exprnode
    thn <- translateStmt thennode
    els <- translateStmt elsenode
    return $ SIf c cond thn els

  S.Node (S.IncludeStmt path _) ->
    Left (Err $ "Error at " ++ (pp_source c) ++ ": include unsupported")

  S.Node S.InputIoDeclStmt [typenode, idnode] ->
    ty <- translateType typenode
    id <- translateIdent ident
    return $ SDeclare c (DVar id ty Nothing)

  S.Node S.OutputIoDeclStmt [typenode, idnode] ->
    ty <- translateType typenode
    id <- translateIdent ident
    return $ SDeclare c (DVar id ty Nothing)

  S.Node S.MeasureArrowAssignmentStmt [srcidexpr, tgtidexpr] ->
    srcid <- translateAccessPath idnode
    tgtid <- translateAccessPath idnode
    return $ SAssign c srcid Nothing (EMeasure tgtid)

  S.Node S.CregOldStyleDeclStmt [ident, exprnode] c -> do
    id <- translateIdent ident
    expr <- (case exprnode of NilNode -> return Nothing; node -> translateExpr node)
    case expr of
      Nothing -> return $ SDeclare c (DVar id CBit Nothing)
      Just e -> return $ SDeclare c (DVar id (CReg e) Nothing)

  S.Node S.QregOldStyleDeclStmt [ident, exprnode] c -> do
    id <- translateIdent ident
    expr <- (case exprnode of NilNode -> return Nothing; node -> translateExpr node)
    case expr of
      Nothing -> return $ SDeclare c (DVar id QBit Nothing)
      Just e -> return $ SDeclare c (DVar id (QReg e) Nothing)

  S.Node S.QuantumDeclStmt [typenode, ident] c -> do
    id <- translateIdent ident
    typ <- translateType typenode
    return $ SDeclare c (DVar id typ Nothing)

  S.Node (S.ResetStmt) [idnodes] c ->
    ids <- translateAccessPath idnodes
    return $ SReset ids

  S.Node S.ReturnStmt [] c   -> left (Err $ "Error at " ++ (pp_source c) ++ ": Return unsupported")

  S.Node S.WhileStmt [condnode, bodynode] ->
    cond <- translateExpr exprnode
    body <- translateStmt bodynode
    return $ SWhile c cond body

  _                           -> Left (Err "Malformed AST node: " ++ show node)

-- | Translation of compound assignment operators
translateCompoundAOp :: S.Token -> Either ErrMsg (Maybe BinOp)
translateCompoundAOp token = case token of
  EqualsToken               -> return Nothing
  PlusEqualsToken           -> return $ Just PlusOp
  MinusEqualsToken          -> return $ Just MinusOp
  AsteriskEqualsToken       -> return $ Just TimesOp
  SlashEqualsToken          -> return $ Just DivOp
  AmpersandEqualsToken      -> return $ Just AndOp
  PipeEqualsToken           -> return $ Just OrOp
  CaretEqualsToken          -> return $ Just XorOp
  DoubleLessEqualsToken     -> return $ Just LShiftOp
  DoubleGreaterEqualsToken  -> return $ Just RShiftOp
  PercentEqualsToken        -> return $ Just ModOp
  DoubleAsteriskEqualsToken -> return $ Just PowOp
