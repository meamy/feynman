{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use head" #-}
module Frontend.OpenQASM3.SemanticAnalyzer where

import Ast qualified
import Control.Monad.State qualified as State
import Data.Int (Int64)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Data.Word (Word64)
import Frontend.OpenQASM3.SemanticGraph
import Frontend.OpenQASM3.Syntax

type SemanticStateM a = State.State SemanticState a

data SemanticState = SemanticState
  { stateNextRefId :: Int,
    stateErrors :: [String]
  }
  deriving (Eq, Read, Show)

initialSemanticState :: SemanticState
initialSemanticState = SemanticState {stateNextRefId = 2, stateErrors = []}

-- semanticProgramAssignScopes :: Program -> SemanticStateM (Program)
-- semanticProgramAssignScopes (Program semPgmScope) = do
--   state <- State.get
--   pgmScope <- withScope (stateRootScopeRef state) $ semanticScopeAssignScopes semPgmScope
--   return $ Program pgmScope

-- semanticScopeAssignScopes :: Block -> SemanticStateM Block
-- semanticScopeAssignScopes (Block scopeRef stmts) = do
--   newScopeRef <- addScope
--   newStmts <- withScope newScopeRef $ mapM semanticStatementAssignScopes stmts
--   return $ Block newScopeRef newStmts

-- semanticStatementAssignScopes :: Statement -> SemanticStateM Statement
-- semanticStatementAssignScopes stmt = return stmt

uniqueRef :: SemanticStateM Ref
uniqueRef = do
  state <- State.get
  let refId = stateNextRefId state
  State.put (state {stateNextRefId = refId + 1})
  return $ Ref refId

addSemanticError :: String -> SemanticStateM ()
addSemanticError errStr = do
  state <- State.get
  State.put (state {stateErrors = errStr : stateErrors state})

{-

semanticTreeResolveIdentifiers :: LexicalScope -> SemanticNode -> SemanticStateM (LexicalScope, SemanticNode)
--
-- ScopeStmt: for each statement in the scope, update the lexical scope (for Let)
semanticTreeResolveIdentifiers scope node@(Ast.Node ScopeStmt children info) = do
  (scope, newRevChildren) <- accumulateStatementScopes scope [] children
  return (scope, node {Ast.children = reverse newRevChildren})
  where
    accumulateStatementScopes accumScope accumRevChildren [] = return (accumScope, accumRevChildren)
    accumulateStatementScopes accumScope accumRevChildren (child : childrenRemain) = do
      (newAccumScope, newChild) <- semanticTreeResolveIdentifiers accumScope child
      accumulateStatementScopes newAccumScope (newChild : accumRevChildren) childrenRemain
--
-- LetStmt: add the identifier to the merged scope and update it, pass new scope into the init expression
semanticTreeResolveIdentifiers scope node@(Ast.Node LetStmt children _) =
  let [declTypeNode, declIdentNode, initExprNode] = children
      declType = expressionTypeFromNode declTypeNode
      Ast.Node (Identifier declName) _ _ = declIdentNode
   in do
        newIdentRef <- uniqueRef
        newScopeRef <- uniqueRef
        let identAttrs =
              initialIdentifierAttributes
                { identName = declName,
                  identRef = newIdentRef,
                  identScopeRef = scopeRef scope,
                  identType = declType
                }
            newIdentMap = Map.insert declName identAttrs (scopeIdentifiers scope)
            newScope = scope {scopeRef = newScopeRef, scopeParentRef = scopeRef scope, scopeIdentifiers = newIdentMap}
        newPairs <- mapM (semanticTreeResolveIdentifiers newScope) children
        return (newScope, node {Ast.children = map snd newPairs})
--
-- Identifier: find the identifier in the scope and decorate the node with its attributes
semanticTreeResolveIdentifiers scope node@(Ast.Node (Identifier name) [] _) =
  case scopeIdentifiers scope Map.!? name of
    Nothing -> do addSemanticError ("Could not resolve identifier " ++ name); return (scope, node)
    Just identAttrs ->
      return (scope, node {Ast.context = (Ast.context node) {infoIdentifierAttributes = identAttrs}})
--
-- Anything else: pass current scope through to children
semanticTreeResolveIdentifiers scope node@(Ast.Node _ children _) = do
  newPairs <- mapM (semanticTreeResolveIdentifiers scope) children
  return (scope, node {Ast.children = map snd newPairs})

-}
