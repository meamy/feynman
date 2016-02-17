module Syntax where

import Data.List

import Data.Set (Set)
import qualified Data.Set as Set

import Text.ParserCombinators.Parsec hiding (space)
import Control.Monad

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
                         inputs :: Set ID,
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

-- Parsing

space = char ' '
semicolon = char ';'
sep = space <|> tab
skipSpaces = skipMany (sep <|> semicolon <|> newline)
parseLineEnd = skipMany sep >> (semicolon <|> newline) >> skipSpaces
parseToken s = string s >> return s
parseCircuitID = letter >>= \c -> many alphaNum >>= \cs -> return (c:cs)
parseArgList = sepBy (many1 alphaNum) (many1 sep) 
parseIDlst :: Int -> Parser [String]
parseIDlst n = count n (many1 alphaNum >>= \id -> many sep >> return id)

parseGate =
  (parseToken "H" >> skipMany1 sep >> parseIDlst 1 >>= \lst -> return $ H (lst !! 0)) <|>
  (parseToken "X" >> skipMany1 sep >> parseIDlst 1 >>= \lst -> return $ X (lst !! 0)) <|>
  (parseToken "Y" >> skipMany1 sep >> parseIDlst 1 >>= \lst -> return $ Y (lst !! 0)) <|>
  (parseToken "Z" >> skipMany1 sep >> parseIDlst 1 >>= \lst -> return $ Z (lst !! 0)) <|>
  ((parseToken "P" <|> parseToken "S") >> skipMany1 sep >> parseIDlst 1 >>= \lst -> return $ S (lst !! 0)) <|>
  ((parseToken "P*" <|> parseToken "S*") >> skipMany1 sep >> parseIDlst 1 >>= \lst -> return $ Sinv (lst !! 0)) <|>
  (parseToken "T" >> skipMany1 sep >> parseIDlst 1 >>= \lst -> return $ T (lst !! 0)) <|>
  (parseToken "T*" >> skipMany1 sep >> parseIDlst 1 >>= \lst -> return $ Tinv (lst !! 0)) <|>
  ((parseToken "tof" <|> parseToken "cnot") >> skipMany1 sep >> parseIDlst 2 >>= \lst -> return $ CNOT (lst !! 0) (lst !! 1))

parseStmt = liftM Gate $ try parseGate
parseStmtSeq = liftM Seq $ endBy parseStmt skipSpaces

parseDecl = do
  parseToken "BEGIN"
  id <- option "main" (try (skipMany1 sep >> parseCircuitID))
  args <- option [] (try (skipMany1 sep >> parseArgList))
  skipSpaces
  stmt <- parseStmtSeq
  skipSpaces
  parseToken "END"
  return $ Decl id args stmt

parseFile = do
  skipSpaces
  parseToken ".v"
  skipMany1 sep
  qubits <- parseArgList
  skipSpaces
  parseToken ".i"
  skipMany1 sep
  inputs <- parseArgList
  skipSpaces
  decls <- endBy parseDecl skipSpaces
  eof
  return $ Circuit qubits (Set.fromList inputs) decls

parseQC = parse parseFile ".qc parser" 

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

