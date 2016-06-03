module DotQC where

import Data.List

import Data.Set (Set)
import qualified Data.Set as Set

import Text.ParserCombinators.Parsec hiding (space)
import Text.ParserCombinators.Parsec.Number
import Control.Monad

import Syntax (ID, Primitive(..))

type Nat = Word
--type ID = String

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

-- Transformations
subst :: (ID -> ID) -> [Gate] -> [Gate]
subst f = map $ \(Gate g i params) -> Gate g i $ map f params

{-
inline :: DotQC -> DotQC
inline circ@(DotQC _ _ _ decls) =
  let f decls def@(Decl _ _ body) = def':decls 
  circ { decls = reverse $ foldl' f [] decls }
-}

gateToCliffordT :: Gate -> [Syntax.Primitive]
gateToCliffordT (Gate g i p) =
  let circ = case (g, p) of
        ("H", [x])     -> [H x]
        ("X", [x])     -> [X x]
        ("tof", [x])   -> [X x]
        ("Y", [x])     -> [Y x]
        ("Z", [x])     -> [Z x]
        ("S", [x])     -> [S x]
        ("S*", [x])    -> [Sinv x]
        ("T", [x])     -> [T x]
        ("T*", [x])    -> [Tinv x]
        ("tof", [x,y]) -> [CNOT x y]
        ("Z", [x,y,z]) -> [H z, T x, T y, T z, CNOT x y, CNOT y z,
                           CNOT z x, Tinv x, Tinv y, T z, CNOT y x,
                           Tinv x, CNOT y z, CNOT z x, CNOT x y, H z]
  in
    concat $ genericReplicate i circ


toCliffordT :: [Gate] -> [Primitive]
toCliffordT = concatMap gateToCliffordT

-- Parsing

space = char ' '
semicolon = char ';'
sep = space <|> tab
comment = char '#' >> manyTill anyChar newline >> return '#'
delimiter = semicolon <|> newline 

skipSpace     = skipMany $ sep <|> comment
skipWithBreak = many1 (skipMany sep >> delimiter >> skipMany sep)

parseID = try $ do
  c  <- letter
  cs <- many alphaNum
  if (c:cs) == "BEGIN" || (c:cs) == "END" then fail "" else return (c:cs)
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
  body <- endBy parseGate skipWithBreak
  string "END"
  return $ Decl id args body

parseHeaderLine s = do
  string s
  skipSpace
  params <- parseParams
  skipWithBreak
  return params

parseFile = do
  skipMany $ sep <|> comment <|> delimiter
  qubits <- parseHeaderLine ".v"
  inputs <- option qubits $ try $ parseHeaderLine ".i"
  outputs <- option qubits $ try $ parseHeaderLine ".o"
  option qubits $ try $ parseHeaderLine ".c"
  option qubits $ try $ parseHeaderLine ".ov"
  decls <- sepEndBy parseDecl skipWithBreak
  skipMany $ sep <|> delimiter
  eof
  return $ DotQC qubits (Set.fromList inputs) (Set.fromList outputs) decls

parseDotQC = parse parseFile ".qc parser"


-- Tests

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

