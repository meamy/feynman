module DotQC where

import Data.List

import Data.Set (Set)
import qualified Data.Set as Set

import Text.ParserCombinators.Parsec hiding (space)
import Text.ParserCombinators.Parsec.Number
import Control.Monad

type Nat = Word
type ID = String

{- A gate has an identifier, a non-negative number of iterations,
 - and a list of parameters -}
data Gate = Gate ID Nat [ID]
data Decl = Decl { name   :: ID,
                   params :: [ID],
                   body   :: [Gate] }
 
data DotQC = DotQC { qubits  :: [ID],
                     inputs  :: Set ID,
                     outputs :: Set ID,
                     decls   :: [Decl] }

-- Printing
showLst = intercalate " "

instance Show Gate where
  show (Gate name 0 params) = ""
  show (Gate name 1 params) = name ++ " " ++ showLst params
  show (Gate name i params) = name ++ "^" ++ show i ++ " " ++ showLst params

instance Show Decl where
  show (Decl name params body) = intercalate "\n" [l1, l2, l3]
    where showName "main" = ""
          showName s      = s
          l1 = "BEGIN " ++ showName name ++ if length params > 0 then "(" ++ showLst params ++ ")" else ""
          l2 = intercalate "\n" $ map show body
          l3 = "END"

instance Show DotQC where
  show (DotQC q i o decls) = intercalate "\n" (q':i':o':bod)
    where q'  = ".v " ++ showLst q
          i'  = ".i " ++ showLst (filter (`Set.member` i) q)
          o'  = ".o " ++ showLst (filter (`Set.member` o) q)
          bod = map show decls

-- Parsing

space = char ' '
semicolon = char ';'
sep = space <|> tab
breaker = semicolon <|> newline

skipSpace     = skipMany sep
skipWithBreak = many1 (skipMany sep >> breaker >> skipMany sep)

parseID = letter >>= \c -> many alphaNum >>= \cs -> return (c:cs)
parseParams = sepBy (many1 alphaNum) (many1 sep) 

parseGate = do
  name <- parseID
  reps <- option 1 (char '^' >> nat)
  skipSpace
  params <- parseParams
  return $ Gate name reps params

parseFormals = do
  skipMany $ char '('
  skipSpace
  params <- parseParams
  skipSpace
  skipMany $ char ')'
  return params

parseDecl = do
  string "BEGIN"
  skipSpace
  id <- option "main" (try parseID)
  skipSpace
  args <- parseFormals 
  skipWithBreak
  body <- sepBy parseGate skipWithBreak
  skipWithBreak
  string "END"
  return $ Decl id args body

parseHeaderLine s = do
  string s
  skipSpace
  parseParams

parseFile = do
  skipMany $ sep <|> breaker
  qubits <- parseHeaderLine ".v"
  skipWithBreak
  inputs <- option qubits $ parseHeaderLine ".i"
  skipWithBreak
  outputs <- option qubits $ parseHeaderLine ".o"
  skipWithBreak
  decls <- endBy parseDecl skipWithBreak
  eof
  return $ DotQC qubits (Set.fromList inputs) (Set.fromList outputs) decls

parseDotQC = parse parseFile ".qc parser" 

-- Test

toffoli = DotQC { qubits  = ["x", "y", "z"],
                  inputs  = Set.fromList ["x", "y", "z"],
                  outputs = Set.fromList ["x", "y", "z"],
                   decls  = [tof] }
    where tof = Decl { name = "main",
                       params = [],
                       body = [ Gate "H" 1 ["z"],
                                Gate "T" 1 ["x"],
                                Gate "T" 1 ["y"],
                                Gate "T" 1 ["z"], 
                                Gate "tof" 1 ["x", "y"],
                                Gate "tof" 1 ["y", "z"],
                                Gate "tof" 1 ["z", "x"],
                                Gate "T*" 1 ["x"],
                                Gate "T*" 1 ["y"],
                                Gate "T" 1 ["z"],
                                Gate "tof" 1 ["y", "x"],
                                Gate "T*" 1 ["x"],
                                Gate "tof" 1 ["y", "z"],
                                Gate "tof" 1 ["z", "x"],
                                Gate "tof" 1 ["x", "y"],
                                Gate "H" 1 ["z"] ] }

