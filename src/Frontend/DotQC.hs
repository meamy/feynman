module Frontend.DotQC where

import Data.List

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Text.ParserCombinators.Parsec hiding (space)
import Text.ParserCombinators.Parsec.Number
import Control.Monad

import Core (ID, Primitive(..), showLst, Angle(..))
import Algebra.Base

type Nat = Word
--type ID = String

{- A gate has an identifier, a non-negative number of iterations,
 - and a list of parameters. Parameterized gates are not pretty
 - but this is a nice quick solution -}
data Gate =
    Gate ID Nat [ID]
  | ParamGate ID Nat Double [ID] deriving (Eq)

data Decl = Decl { name   :: ID,
                   params :: [ID],
                   body   :: [Gate] }
 
data DotQC = DotQC { qubits  :: [ID],
                     inputs  :: Set ID,
                     outputs :: Set ID,
                     decls   :: [Decl] }

-- Printing

instance Show Gate where
  show (Gate name 0 params) = ""
  show (Gate name 1 params) = name ++ " " ++ showLst params
  show (Gate name i params) = name ++ "^" ++ show i ++ " " ++ showLst params
  show (ParamGate name 0 p params) = ""
  show (ParamGate name 1 p params) = name ++ "(" ++ show p ++ ")" ++ " " ++ showLst params
  show (ParamGate name i p params) = name ++ "(" ++ show p ++ ")^" ++ show i ++ " " ++ showLst params

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

inv :: Gate -> Gate
inv gate@(Gate g i p) =
  case g of
    "H"    -> gate
    "X"    -> gate
    "Y"    -> gate
    "Z"    -> gate
    "S"    -> Gate "S*" i p
    "S*"   -> Gate "S" i p
    "P"    -> Gate "P*" i p
    "P*"   -> Gate "P" i p
    "T"    -> Gate "T*" i p
    "T*"   -> Gate "T" i p
    "tof"  -> gate
    "cnot" -> gate
inv gate@(ParamGate g i f p) =
  case g of
    "Rz"   -> ParamGate g i (-f) p
    "Rx"   -> ParamGate g i (-f) p
    "Ry"   -> ParamGate g i (-f) p

simplify :: [Gate] -> [Gate]
simplify circ =
  let circ' = zip circ [0..]
      allSame xs = foldM (\x y -> if fst x == fst y then Just x else Nothing) (head xs) (tail xs)
      f (last, erasures) (gate, uid) =
        let p = case gate of
              Gate _ _ p -> p
              ParamGate _ _ _ p -> p
            last' = foldr (\q -> Map.insert q (gate, uid)) last p
        in
          case mapM (\q -> Map.lookup q last) p >>= allSame of
            Nothing -> (last', erasures)
            Just (gate', uid') ->
              if gate == (inv gate') then
                (last', Set.insert uid $ Set.insert uid' erasures)
              else
                (last', erasures)
      erasures = snd $ foldl' f (Map.empty, Set.empty) circ'
  in
    fst $ unzip $ filter (\(_, uid) -> not $ Set.member uid erasures) circ'

simplifyDotQC :: DotQC -> DotQC
simplifyDotQC (DotQC q i o decls) = DotQC q i o $ map f decls
  where f (Decl n p body) =
          let body' = simplify body in
          if body' == body then
            Decl n p body
          else
            f $ Decl n p body'

subst :: (ID -> ID) -> [Gate] -> [Gate]
subst f = map g
  where g (Gate g i params) = Gate g i $ map f params
        g (ParamGate g i p params) = ParamGate g i p $ map f params

{-
inline :: DotQC -> DotQC
inline circ@(DotQC _ _ _ decls) =
  let f decls def@(Decl _ _ body) = def':decls 
  circ { decls = reverse $ foldl' f [] decls }
-}

gateToCliffordT :: Gate -> [Primitive]
gateToCliffordT (Gate g i p) =
  let circ = case (g, p) of
        ("H", [x])      -> [H x]
        ("X", [x])      -> [X x]
        ("Y", [x])      -> [Y x]
        ("Z", [x])      -> [Z x]
        ("S", [x])      -> [S x]
        ("P", [x])      -> [S x]
        ("S*", [x])     -> [Sinv x]
        ("P*", [x])     -> [Sinv x]
        ("T", [x])      -> [T x]
        ("T*", [x])     -> [Tinv x]
        ("tof", [x])    -> [X x]
        ("tof", [x,y])  -> [CNOT x y]
        ("tof", [x,y,z])-> [H z, T x, T y, T z, CNOT x y, CNOT y z,
                            CNOT z x, Tinv x, Tinv y, T z, CNOT y x,
                            Tinv x, CNOT y z, CNOT z x, CNOT x y, H z]
        ("cnot", [x,y]) -> [CNOT x y]
        ("swap", [x,y]) -> [Swap x y]
        ("Z", [x,y,z])  -> [T x, T y, T z, CNOT x y, CNOT y z,
                            CNOT z x, Tinv x, Tinv y, T z, CNOT y x,
                            Tinv x, CNOT y z, CNOT z x, CNOT x y]
  in
    concat $ genericReplicate i circ
gateToCliffordT (ParamGate g i f p) =
  let circ = case (g, p) of
        ("Rz", [x]) -> [Rz (Continuous f) x]
        ("Rx", [x]) -> [Rx (Continuous f) x]
        ("Ry", [x]) -> [Ry (Continuous f) x]
  in
    concat $ genericReplicate i circ


toCliffordT :: [Gate] -> [Primitive]
toCliffordT = concatMap gateToCliffordT

gateFromCliffordT :: Primitive -> Gate
gateFromCliffordT g = case g of
  H x      -> Gate "H" 1 [x]
  X x      -> Gate "X" 1 [x]
  Y x      -> Gate "Y" 1 [x]
  Z x      -> Gate "Z" 1 [x]
  S x      -> Gate "S" 1 [x]
  Sinv x   -> Gate "S*" 1 [x]
  T x      -> Gate "T" 1 [x]
  Tinv x   -> Gate "T*" 1 [x]
  CNOT x y -> Gate "tof" 1 [x, y]
  Swap x y -> Gate "swap" 1 [x, y]
  Rz f x   -> ParamGate "Rz" 1 (makeFloat f) [x]
  Rx f x   -> ParamGate "Rx" 1 (makeFloat f) [x]
  Ry f x   -> ParamGate "Ry" 1 (makeFloat f) [x]
  where makeFloat (Continuous theta) = theta
        makeFloat (Discrete theta)   = toDouble theta

fromCliffordT :: [Primitive] -> [Gate]
fromCliffordT = map gateFromCliffordT

-- This is totally wrong, but no benchmarks have function calls yet
countGates (DotQC _ _ _ decls) = foldl' f [0,0,0,0,0,0,0,0] decls
  where plus                   = zipWith (+)
        f cnt (Decl _ _ gates) = foldl' g cnt $ toCliffordT gates
        g cnt gate             = case gate of
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
          _        -> cnt

-- This is also totally wrong
tDepth :: DotQC -> Int
tDepth (DotQC _ _ _ decls)    = maximum $ 0:(Map.elems $ foldl' f Map.empty decls)
  where addOne val            = case val of
          Nothing -> Just 1
          Just v  -> Just $ v + 1
        f mp (Decl _ _ gates) = foldl' g mp $ toCliffordT gates
        g mp gate             = case gate of
          T x      -> Map.alter addOne x mp
          Tinv x   -> Map.alter addOne x mp
          CNOT x y ->
            let xval = Map.findWithDefault 0 x mp
                yval = Map.findWithDefault 0 y mp
                maxv = max xval yval
            in
              Map.insert x maxv $ Map.insert y maxv mp
          Swap x y ->
            let xval = Map.findWithDefault 0 x mp
                yval = Map.findWithDefault 0 y mp
            in
              Map.insert x yval $ Map.insert y xval mp
          _        -> mp
          

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
  cs <- many (alphaNum <|> char '*')
  if (c:cs) == "BEGIN" || (c:cs) == "END" then fail "" else return (c:cs)
parseParams = sepEndBy (many1 alphaNum) (many1 sep) 

parseGate = do
  name <- parseID
  param <- optionMaybe (char '(' >> sign <*> (floating2 True >>= \f -> char ')' >> return f))
  reps <- option 1 (char '^' >> nat)
  skipSpace
  params <- parseParams
  skipSpace
  case param of
    Nothing -> return $ Gate name reps params
    Just f  -> return $ ParamGate name reps f params

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
  skipSpace
  eof
  return $ DotQC qubits (Set.fromList inputs) (Set.fromList outputs) decls

parseDotQC = (liftM simplifyDotQC) . (parse parseFile ".qc parser")


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


toffoli2 = DotQC { qubits  = ["x", "y", "z"],
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
                                Gate "H" 1 ["z"],
                                Gate "H" 1 ["z"],
                                Gate "tof" 1 ["x", "y"],
                                Gate "tof" 1 ["z", "x"],
                                Gate "tof" 1 ["y", "z"],
                                Gate "T" 1 ["x"],
                                Gate "tof" 1 ["y", "x"],
                                Gate "T*" 1 ["z"],
                                Gate "T" 1 ["y"],
                                Gate "T" 1 ["x"],
                                Gate "tof" 1 ["z", "x"],
                                Gate "tof" 1 ["y", "z"],
                                Gate "tof" 1 ["x", "y"],
                                Gate "T*" 1 ["z"], 
                                Gate "T*" 1 ["y"],
                                Gate "T*" 1 ["x"],
                                Gate "H" 1 ["z"] ] }
