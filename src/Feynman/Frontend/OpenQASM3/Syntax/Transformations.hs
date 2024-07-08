module Feynman.Frontend.OpenQASM3.Syntax.Transformations where

import Control.Monad.State.Lazy
import Data.Char
import Data.List (intercalate, stripPrefix)
import Data.Maybe (fromMaybe, listToMaybe)
import Data.Map (Map, (!))
import qualified Data.Map as Map
import Debug.Trace (trace)
import Numeric
import Text.Read (readMaybe)

import qualified Feynman.Frontend.OpenQASM3.Ast as Ast
import Feynman.Frontend.OpenQASM3.Syntax

-- Adds unique id nuumbers to each node for identification
decorateIDs :: Ast.Node Tag c -> Ast.Node Tag Int
decorateIDs node = evalState (go node) 0 where
  go Ast.NilNode = return Ast.NilNode
  go (Ast.Node t stmts _) = do
    i <- get
    modify (+1)
    stmts' <- mapM go stmts
    return (Ast.Node t stmts' i)

data Decl c = Decl String [String] [String] (Ast.Node Tag c) deriving (Show)

getIdent :: Ast.Node Tag c -> String
getIdent (Ast.Node (Identifier name _) _ _) = name
getIdent _ = error "Not an identifier..."

getList :: Ast.Node Tag c -> [Ast.Node Tag c]
getList Ast.NilNode = []
getList (Ast.Node List stmts _) = stmts
getList _ = error "Not a list..."

asIntegerMaybe :: Ast.Node Tag c -> Maybe Integer
asIntegerMaybe node = case squashInts node of
  Ast.Node (IntegerLiteral i _) _ _ ->  Just i
  _                                 -> Nothing

asInteger :: Ast.Node Tag c -> Integer
asInteger node = case asIntegerMaybe node of
  Nothing -> trace ("Couldn't resolve integer") 0
  Just i  -> i

exprAsQlist :: Ast.Node Tag c -> [Ast.Node Tag c]
exprAsQlist node = case node of
  Ast.NilNode -> []
  (Ast.Node (Identifier name _) _ _) -> [node]
  (Ast.Node IndexedIdentifier [ident, expr] c) ->
    let idxs = resolveExpr expr in
      case idxs of
        []  -> []
        xs  -> map (\i -> Ast.Node IndexedIdentifier [ident, Ast.Node List [Ast.Node (IntegerLiteral i (DecimalIntegerLiteralToken $ show i)) [] c] c] c) xs
  _       -> trace ("Couldn't resolve identifier list") []
  where
    resolveExpr Ast.NilNode = []
    resolveExpr (Ast.Node List children c) = concatMap resolveExpr children
    resolveExpr (Ast.Node (IntegerLiteral i _) _ _) = [i]
    resolveExpr (Ast.Node RangeInitExpr [b,s,e] _) =
      let bInt = asInteger b
          sInt = fromMaybe 1 $ asIntegerMaybe s
          eInt = asInteger e
      in
        [bInt,(bInt + sInt)..eInt]
    resolveExpr _ = trace ("Couldn't resolve identifier range") $ []

squashInts :: Ast.Node Tag c -> Ast.Node Tag c
squashInts Ast.NilNode = Ast.NilNode
squashInts (Ast.Node tag exprs c) =
  let exprs' = map squashInts exprs in
    case (tag, exprs') of
      (ParenExpr, [Ast.Node (IntegerLiteral i _) _ _]) -> Ast.Node (IntegerLiteral i (DecimalIntegerLiteralToken $ show i)) [] c
      (UnaryOperatorExpr MinusToken, [Ast.Node (IntegerLiteral i _) _ _]) -> Ast.Node (IntegerLiteral (-i) (DecimalIntegerLiteralToken $ show (-i))) [] c
      (BinaryOperatorExpr PlusToken, [Ast.Node (IntegerLiteral i _) _ _, Ast.Node (IntegerLiteral j _) _ _]) -> Ast.Node (IntegerLiteral (i+j) (DecimalIntegerLiteralToken (show $ i+j))) [] c
      (BinaryOperatorExpr MinusToken, [Ast.Node (IntegerLiteral i _) _ _, Ast.Node (IntegerLiteral j _) _ _]) -> Ast.Node (IntegerLiteral (i-j) (DecimalIntegerLiteralToken (show $ i-j))) [] c
      (BinaryOperatorExpr AsteriskToken, [Ast.Node (IntegerLiteral i _) _ _, Ast.Node (IntegerLiteral j _) _ _]) -> Ast.Node (IntegerLiteral (i*j) (DecimalIntegerLiteralToken (show $ i*j))) [] c
      _ -> Ast.Node tag exprs' c

-- Applies substitutions
subst :: Map String (Ast.Node Tag c) -> Ast.Node Tag c -> Ast.Node Tag c
subst substs node = case node of
  Ast.NilNode                                                     -> Ast.NilNode
  (Ast.Node (Identifier name _) _ _) | Map.member name substs -> substs!name
  (Ast.Node tag stmts c)                                      -> Ast.Node tag (map (subst substs) stmts) c

-- Makes a basic gate call
makeBasicCall :: String -> [Ast.Node Tag c] -> c -> Ast.Node Tag c
makeBasicCall name args c =
  let target  = Ast.Node (Identifier name (IdentifierToken name)) [] c
      argList = Ast.Node List args c
  in
    Ast.Node GateCallStmt [Ast.NilNode, target, Ast.NilNode, Ast.NilNode, argList] c

-- Inlines all gate declarations
inlineGateCalls :: Ast.Node Tag c -> Ast.Node Tag c
inlineGateCalls node = evalState (go node) Map.empty where
  go Ast.NilNode = return Ast.NilNode
  go node@(Ast.Node GateStmt [ident, params, args, stmts] c) = do
    stmts' <- go stmts
    modify (Map.insert (getIdent ident) $ Decl (getIdent ident) (map getIdent $ getList params) (map getIdent $ getList args) stmts')
    return node
  go node@(Ast.Node GateCallStmt [modifiers, target, params, maybeTime, gateArgs] c)
    | getIdent target == "ccx" = do
        let [x,y,z] = getList gateArgs
        let gateList = [makeBasicCall "h" [z] c,
                        makeBasicCall "t" [x] c,
                        makeBasicCall "t" [y] c,
                        makeBasicCall "t" [z] c,
                        makeBasicCall "cx" [x,y] c,
                        makeBasicCall "cx" [y,z] c,
                        makeBasicCall "cx" [z,x] c,
                        makeBasicCall "tdg" [x] c,
                        makeBasicCall "tdg" [y] c,
                        makeBasicCall "t" [z] c,
                        makeBasicCall "cx" [y,x] c,
                        makeBasicCall "tdg" [x] c,
                        makeBasicCall "cx" [y,z] c,
                        makeBasicCall "cx" [z,x] c,
                        makeBasicCall "cx" [x,y] c,
                        makeBasicCall "h" [z] c]
        return $ Ast.Node Scope gateList c
    | otherwise                = do
        ctx <- get
        case Map.lookup (getIdent target) ctx of
          Nothing                          -> return node
          Just (Decl _ fparams fargs body) ->
            let substs = Map.fromList $ (zip fparams $ getList params) ++ (zip fargs $ getList gateArgs) in
              return $ subst substs body
  go (Ast.Node tag children c) = do
    children' <- mapM go children
    return $ Ast.Node tag children' c

-- Unrolls for loops
unrollLoops :: Ast.Node Tag c -> Ast.Node Tag c
unrollLoops node = squashInts $ evalState (go node) Map.empty where
      -- [ScalarTypeSpec, Identifier, (Expression | Range | Set), (Statement | Scope)]
  go Ast.NilNode = return Ast.NilNode
  go node@(Ast.Node ForStmt [tyspec, ident, range, stmt] c) = do
    let var = getIdent ident
    let rn  = resolveRange range
    let ur  = map (\i -> subst (Map.fromList [(var, Ast.Node (IntegerLiteral i (DecimalIntegerLiteralToken $ show i)) [] c)]) stmt) rn
    trace ("Unrolling loop over var " ++ show var ++ " with range " ++ show rn) $ return $ Ast.Node Scope ur c
  go node@(Ast.Node tag children c) = do
    children' <- mapM go children
    return $ Ast.Node tag children' c

  resolveRange Ast.NilNode = []
  resolveRange (Ast.Node RangeInitExpr [b,s,e] c) =
    let bInt = asInteger b
        sInt = fromMaybe 1 $ asIntegerMaybe s
        eInt = asInteger e
    in
      [bInt,(bInt + sInt)..eInt]
