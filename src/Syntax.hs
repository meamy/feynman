module Syntax where

import Data.Map (Map)
import qualified Data.Map as Map

type ID = String

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

data Stmt =
    Gate Primitive
  | Seq [Stmt]
  | Call ID [ID]
  | Repeat Int Stmt
   
data Decl = Decl { name   :: ID,
                   params :: [ID],
                   body   :: Stmt }
 
data Circuit = Circuit { qubits :: [ID],
                         inputs :: Map ID Bool,
                         decls  :: [Decl] }

foldCirc f b c = foldl (foldStmt f . body) b (decls c)

foldStmt f (Seq st)      b = f (Seq st) (foldr (foldStmt f) b st)
foldStmt f (Repeat i st) b = f (Repeat i st) (foldStmt f st b)
foldStmt f s             b = f s b

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


printStmt stmt = case stmt of
    Gate gate               -> putStrLn $ show gate
    Seq lst                 -> mapM_ printStmt lst
    Call id args            -> putStrLn $ show id ++ showLst args
    Repeat i (Call id args) -> putStrLn $ show id ++ "^" ++ show i ++ showLst args
    Repeat i stmt           -> putStrLn ("Begin^" ++ show i) >> printStmt stmt >> putStrLn "End"

printDecl decl = do
    putStrLn $ "BEGIN " ++ putName (name decl) ++ showLst (params decl)
    printStmt (body decl)
    putStrLn $ "END"
    where putName "main" = ""
          putName s      = s

printCirc circ = do
    putStrLn  $ ".v" ++ showLst (qubits circ)
    putStrLn  $ ".i" ++ showLst (filter (\t -> Map.notMember t (inputs circ)) (qubits circ))
    mapM_ (\decl -> putStrLn "" >> printDecl decl) (decls circ)

showLst = concatMap (" " ++)

-- Test

toffoli = Circuit { qubits = ["x", "y", "z"],
                    inputs = Map.fromList [("x", True), ("y", True), ("z", True)],
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

