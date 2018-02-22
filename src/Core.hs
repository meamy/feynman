module Core where

import Data.List

import Data.Set (Set)
import qualified Data.Set as Set

import Text.ParserCombinators.Parsec hiding (space)
import Control.Monad

type ID = String
type Loc = Int

data Primitive =
    H    ID
  | X    ID
  | Y    ID
  | Z    ID
  | CNOT ID ID
  | S    ID
  | Sinv ID
  | T    ID
  | Tinv ID
  | Swap ID ID
  | Rz   Double ID

data Stmt =
    Gate Primitive
  | Seq [Stmt]
  | Call ID [ID]
  | Repeat Int Stmt
   
data Decl = Decl { name   :: ID,
                   params :: [ID],
                   body   :: Stmt }
 
data Circuit = Circuit { qubits :: [ID],
                         inputs :: Set ID,
                         decls  :: [Decl] }

foldCirc f b c = foldl (foldStmt f . body) b (decls c)

foldStmt f (Seq st)      b = f (Seq st) (foldr (foldStmt f) b st)
foldStmt f (Repeat i st) b = f (Repeat i st) (foldStmt f st b)
foldStmt f s             b = f s b

countGates (Circuit _ _ decls) = foldl' f [0,0,0,0,0,0,0,0] decls
  where plus                   = zipWith (+)
        f cnt (Decl _ _ stmt)  = g cnt stmt
        g cnt (Seq xs)         = foldl' g cnt xs
        g cnt (Call _ _)       = error "Unimplemented call"
        g cnt (Repeat 0 stmt)  = g cnt stmt
        g cnt (Repeat i stmt)  = g (g cnt stmt) (Repeat (i-1) stmt)
        g cnt (Gate gate)      = case gate of
          H _      -> plus cnt [1,0,0,0,0,0,0,0]
          X _      -> plus cnt [0,1,0,0,0,0,0,0]
          Y _      -> plus cnt [0,0,1,0,0,0,0,0]
          Z _      -> plus cnt [0,0,0,1,0,0,0,0]
          CNOT _ _ -> plus cnt [0,0,0,0,1,0,0,0]
          S _      -> plus cnt [0,0,0,0,0,1,0,0]
          Sinv _   -> plus cnt [0,0,0,0,0,1,0,0]
          T _      -> plus cnt [0,0,0,0,0,0,1,0]
          Tinv _   -> plus cnt [0,0,0,0,0,0,1,0]
          Swap _ _ -> plus cnt [0,0,0,0,0,0,0,1]

-- Transformations

--inline :: Circuit -> Circuit
--inline circ = List.map expandCalls

--subst sub stmt = case stmt of
--  | Gate 

-- Printing

instance Show Primitive where
  show (H x)      = "H " ++ x
  show (X x)      = "X " ++ x
  show (Y x)      = "Y " ++ x
  show (CNOT x y) = "tof " ++ x ++ " " ++ y
  show (S x)      = "S " ++ x
  show (Sinv x)   = "S* " ++ x
  show (T x)      = "T " ++ x
  show (Tinv x)   = "T* " ++ x
  show (Swap x y) = "swap " ++ x ++ " " ++ y

instance Show Stmt where
  show (Gate gate)               = show gate
  show (Seq lst)                 = intercalate "\n" (map show lst)
  show (Call id args)            = show id ++ showLst args
  show (Repeat i (Call id args)) = show id ++ "^" ++ show i ++ showLst args
  show (Repeat i stmt)           = "BEGIN^" ++ show i ++ "\n" ++ show stmt ++ "\n" ++ "END"

instance Show Decl where
  show decl = "BEGIN " ++ putName (name decl) ++ showLst (params decl) ++ "\n" ++ show (body decl) ++ "\n" ++ "END"
    where putName "main" = ""
          putName s      = s

instance Show Circuit where
  show circ = intercalate "\n" (qubitline:inputline:body)
    where qubitline = ".v " ++ showLst (qubits circ)
          inputline = ".i " ++ showLst (filter (`Set.member` inputs circ) (qubits circ))
          body      = map show (decls circ)

showLst = intercalate " "

-- Test

toffoli = Circuit { qubits = ["x", "y", "z"],
                    inputs = Set.fromList ["x", "y", "z"],
                    decls  = [tof] }
    where tof = Decl { name = "main",
                       params = [],
                       body = Seq [ Gate $ H "z",
                                    Gate $ T "x", Gate $ T "y", Gate $ T "z", 
                                    Gate $ CNOT "x" "y", Gate $ CNOT "y" "z", Gate $ CNOT "z" "x",
                                    Gate $ Tinv "x", Gate $ Tinv "y", Gate $ T "z",
                                    Gate $ CNOT "y" "x",
                                    Gate $ Tinv "x",
                                    Gate $ CNOT "y" "z", Gate  $CNOT "z" "x", Gate $ CNOT "x" "y",
                                    Gate $ H "z" ] }

