{-# LANGUAGE DeriveGeneric #-}
module Feynman.Frontend.DotQC (DotQC(..), Gate(..), Decl(..), gateCounts, depth, fromCliffordT, parseDotQC, tDepth, toCliffordT, toGatelist) where

import Feynman.Core (ID, Primitive(..), showLst, Angle(..), dyadicPhase, continuousPhase, expandCNOT, expandCZ)
import Feynman.Algebra.Base
import Feynman.Synthesis.Pathsum.Unitary (ExtractionGates(..), resynthesizeCircuit)

import Data.List

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Map.Strict (Map, (!))
import qualified Data.Map.Strict as Map

import Data.ByteString (ByteString)
import qualified Data.ByteString as B

import Text.Parsec hiding (space)
import Text.Parsec.Char hiding (space)
import Text.Parsec.Number
import Control.Monad

import Control.DeepSeq (NFData)
import GHC.Generics (Generic)

import qualified Feynman.Frontend.Frontend as FE

import Feynman.Optimization.PhaseFold
import Feynman.Optimization.StateFold
import Feynman.Optimization.TPar
import Feynman.Optimization.Clifford
import Feynman.Optimization.RelationalFold as L
import Feynman.Optimization.RelationalFoldNL as NL
import Feynman.Synthesis.Pathsum.Unitary
import Feynman.Verification.Symbolic

import Numeric (showFFloat)

type Nat = Word

{- Data structures -}

data Gate =
    Gate ID Nat [ID]
  | ParamGate ID Nat Angle [ID] deriving (Eq, Generic)

data Decl = Decl { name   :: ID,
                   params :: [ID],
                   body   :: [Gate] }
            deriving (Generic)

data DotQC = DotQC { qubits  :: [ID],
                     inputs  :: Set ID,
                     outputs :: Set ID,
                     decls   :: [Decl] }
             deriving (Generic)

instance NFData Gate
instance NFData Decl
instance NFData DotQC

{- Printing -}

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
          showName ""     = ""
          showName s      = " " ++ s
          l1 = "BEGIN" ++ showName name ++ if length params > 0 then "(" ++ showLst params ++ ")" else ""
          l2 = intercalate "\n" $ map show body
          l3 = "END"

instance Show DotQC where
  show (DotQC q i o decls) = intercalate "\n" (q':i':o':bod)
    where q'  = ".v " ++ showLst q
          i'  = ".i " ++ showLst (filter (`Set.member` i) q)
          o'  = ".o " ++ showLst (filter (`Set.member` o) q)
          bod = map show . uncurry (++) . partition (\decl -> name decl /= "main") $ decls

{- Accessors -}

repeats :: Num a => Gate -> a
repeats (Gate _ i _)        = fromIntegral i
repeats (ParamGate _ i _ _) = fromIntegral i

arguments :: Gate -> [ID]
arguments (Gate _ _ xs)        = xs
arguments (ParamGate _ _ _ xs) = xs

gateName :: Gate -> ID
gateName (Gate g _ _)        = g
gateName (ParamGate g _ a _) = g ++ "(" ++ show a ++ ")"

{- Transformations -}

subst :: (ID -> ID) -> [Gate] -> [Gate]
subst f = map g
  where g (Gate g i params) = Gate g i $ map f params
        g (ParamGate g i p params) = ParamGate g i p $ map f params

-- Inlines all declarations. Doesn't check for cycles, all gates without definitions are uninterpreted
inlineAll :: DotQC -> DotQC
inlineAll circ =
  let accGatelist ctx []     = (ctx, [])
      accGatelist ctx (x:xs) =
        let (ctx', xpand)   = gateToList ctx x
            (ctx'', xspand) = accGatelist ctx' xs
        in
          (ctx'', (concat . replicate (repeats x) $ xpand) ++ xspand)
      gateToList ctx x@(ParamGate _ _ _ _) = (ctx, [x])
      gateToList ctx x@(Gate g _ args)     = case find (\decl -> name decl == g) (decls circ) of
        Nothing   -> (ctx, [x])
        Just decl ->
          let (ctx', gatelist) = expandSubdec ctx decl
              f id             = Map.findWithDefault id id $ Map.fromList $ zip (params decl) args
          in
            (ctx', subst f gatelist)
      expandSubdec ctx decl = case Map.lookup (name decl) ctx of
        Nothing ->
          let (ctx', gatelist) = accGatelist ctx (body decl) in
            (Map.insert (name decl) gatelist ctx', gatelist)
        Just gatelist -> (ctx, gatelist)
      inlined = foldl (\ctx decl -> fst $ expandSubdec ctx decl) Map.empty $ decls circ
  in
    circ { decls = map (\decl -> decl { body = inlined!(name decl) }) (decls circ) }

-- Strips all other functions out of the inlined one
inlineDotQC :: DotQC -> DotQC
inlineDotQC circ = circ' { decls = filter (\decl -> name decl == "main") $ decls circ' }
  where circ' = inlineAll circ

-- Returns the inlined main function
toGatelist :: DotQC -> [Gate]
toGatelist circ = case find (\decl -> name decl == "main") (decls $ inlineAll circ) of
  Nothing   -> []
  Just decl -> body decl

inv :: Gate -> Maybe Gate
inv gate@(Gate g i p) =
  case g of
    "H"    -> Just gate
    "X"    -> Just gate
    "Y"    -> Just gate
    "Z"    -> Just gate
    "S"    -> Just $ Gate "S*" i p
    "S*"   -> Just $ Gate "S" i p
    "P"    -> Just $ Gate "P*" i p
    "P*"   -> Just $ Gate "P" i p
    "T"    -> Just $ Gate "T*" i p
    "T*"   -> Just $ Gate "T" i p
    "tof"  -> Just gate
    "cnot" -> Just gate
    "swap" -> Just gate
    _      -> Nothing
inv gate@(ParamGate g i f p) =
  case g of
    "Rz"   -> Just $ ParamGate g i (-f) p
    "Rx"   -> Just $ ParamGate g i (-f) p
    "Ry"   -> Just $ ParamGate g i (-f) p

simplify :: [Gate] -> [Gate]
simplify circ =
  let circ' = zip circ [0..]
      erasures = snd $ foldl' f (Map.empty, Set.empty) circ'
      f (last, erasures) (gate, uid) =
        let p = case gate of
              Gate _ _ p -> p
              ParamGate _ _ _ p -> p
            last' = foldr (\q -> Map.insert q (gate, uid)) last p
        in
          case mapM (\q -> Map.lookup q last) p >>= allSame of
            Nothing -> (last', erasures)
            Just (gate', uid') ->
              if Just gate == (inv gate') then
                (foldr Map.delete last' p, Set.insert uid $ Set.insert uid' erasures)
              else
                (last', erasures)
      allSame xs = foldM (\x y -> if fst x == fst y then Just x else Nothing) (head xs) (tail xs)
  in
    fst . unzip $ filter (\(_, uid) -> not $ Set.member uid erasures) circ'

simplifyDotQC :: DotQC -> DotQC
simplifyDotQC circ = circ { decls = map f $ decls circ }
  where f decl =
          let body' = simplify $ body decl in
          if body' == body decl then
            decl
          else
            f $ decl { body = body' }

applyDotQC :: ([Gate] -> [Gate]) -> DotQC -> DotQC
applyDotQC trans circ = circ { decls = map f $ decls circ }
  where f decl = decl { body = trans $ body decl }

expandAll :: DotQC -> DotQC
expandAll = applyDotQC (fromCliffordT . toCliffordT)

expandToffolis :: DotQC -> DotQC
expandToffolis circ =
  let (maxlength, circ') =
        let (maxlength', decls') = foldl f (0, []) $ decls circ in
          (maxlength', circ { decls = decls' })
      f (maxlength, decls) decl@(Decl _ _ body) =
        let (maxlength', body') = foldl g (maxlength, []) body in
          (maxlength', decls ++ [decl { body = body' }])
      g (maxlength, gates) gate@(Gate name i p) =
        let res = case (name, p) of
              ("tof", xs) | length xs > 3 -> concatMap (\_ -> mct xs) [1..i]
              _                           -> [gate]
        in
          (max maxlength (length p), gates ++ res)
      ancillas = ["anc" ++ show i | i <- [0..maxlength-4]]
  in
    circ' { qubits = (qubits circ) ++ ancillas }

-- Circuit expansions
mct :: [ID] -> [Gate]
mct = go 0
  where go i []         = []
        go i (x:[])     = [Gate "X" 1 []]
        go i (x:y:[])   = [Gate "tof" 1 [x,y]]
        go i (x:y:z:[]) = [Gate "tof" 1 [x,y,z]]
        go i (x:y:z:xs) =
          let anc        = "anc" ++ show i
              subproduct = [Gate "tof" 1 [x,y,anc]]
          in
            subproduct ++ go (i+1) (anc:z:xs) ++ reverse subproduct

gateToCliffordT :: Gate -> [Primitive]
gateToCliffordT (Gate g i p) =
  let circ = case (g, p) of
        ("H", [x])      -> [H x]
        ("X", [x])      -> [X x]
        ("Y", [x])      -> [Y x]
        ("Z", [x])      -> [Z x]
        ("Z", [x,y])    -> [CZ x y]
        ("S", [x])      -> [S x]
        ("P", [x])      -> [S x]
        ("S*", [x])     -> [Sinv x]
        ("P*", [x])     -> [Sinv x]
        ("T", [x])      -> [T x]
        ("T*", [x])     -> [Tinv x]
        ("tof", [x])    -> [X x]
        ("tof", [x,y])  -> [CNOT x y]
        ("cnot", [x,y]) -> [CNOT x y]
        ("swap", [x,y]) -> [Swap x y]
        ("cz", [x,y])   -> [CZ x y]
        ("tof", [x,y,z])-> [H z, T x, T y, CNOT z x, Tinv x, CNOT y z, Tinv z,
                            CNOT y x, T x, CNOT y z, CNOT z x, Tinv x,
                            T z, CNOT y x, H z]
        ("Z", [x,y,z])  -> [T x, T y, CNOT z x, Tinv x, CNOT y z, Tinv z,
                            CNOT y x, T x, CNOT y z, CNOT z x, Tinv x,
                            T z, CNOT y x]
        ("Zd", [x,y,z]) -> [Tinv x, Tinv y, CNOT z x, T x, CNOT y z, T z,
                            CNOT y x, Tinv x, CNOT y z, CNOT z x, T x,
                            Tinv z, CNOT y x]
        ("tof", xs)     -> toCliffordT $ mct xs
        ("X", xs)       -> toCliffordT $ mct xs
        otherwise       -> [Uninterp g p]
  in
    concat $ genericReplicate i circ
gateToCliffordT (ParamGate g i theta p) =
  let circ = case (g, p) of
        ("Rz", [x]) -> [Rz theta x]
        ("Rx", [x]) -> [Rx theta x]
        ("Ry", [x]) -> [Ry theta x]
        otherwise   -> [Uninterp (g ++ "(" ++ show theta ++ ")") p]
  in
    concat $ genericReplicate i circ

toCliffordT :: [Gate] -> [Primitive]
toCliffordT = concatMap gateToCliffordT

gateFromCliffordT :: Primitive -> Gate
gateFromCliffordT g = case g of
  H x           -> Gate "H" 1 [x]
  X x           -> Gate "X" 1 [x]
  Y x           -> Gate "Y" 1 [x]
  Z x           -> Gate "Z" 1 [x]
  S x           -> Gate "S" 1 [x]
  Sinv x        -> Gate "S*" 1 [x]
  T x           -> Gate "T" 1 [x]
  Tinv x        -> Gate "T*" 1 [x]
  CNOT x y      -> Gate "cnot" 1 [x, y]
  CZ x y        -> Gate "cz" 1 [x, y]
  Swap x y      -> Gate "swap" 1 [x, y]
  Rz f x        -> ParamGate "Rz" 1 f [x]
  Rx f x        -> ParamGate "Rx" 1 f [x]
  Ry f x        -> ParamGate "Ry" 1 f [x]
  Uninterp s xs -> Gate s 1 xs

fromCliffordT :: [Primitive] -> [Gate]
fromCliffordT = map gateFromCliffordT

gateFromExtractionBasis :: ExtractionGates -> Gate
gateFromExtractionBasis g = case g of
  Hadamard x    -> Gate "H" 1 [x]
  MCT xs x      -> Gate "tof" 1 $ xs ++ [x]
  Phase f xs    -> ParamGate "Rz" 1 (Discrete f) $ xs
  Swapper x y   -> Gate "swap" 1 [x, y]

fromExtractionBasis :: [ExtractionGates] -> [Gate]
fromExtractionBasis = map gateFromExtractionBasis

{- Statistics -}

stripAdjoint :: String -> String
stripAdjoint = filter (\c -> c /= '*')

gateCounts :: [Gate] -> Map ID Int
gateCounts = foldl f Map.empty
  where f counts gate = addToCount (repeats gate) (stripAdjoint $ gateName gate) counts
        addToCount i g counts =
          let alterf val = case val of
                Nothing -> Just 1
                Just c  -> Just $ c+1
          in
            Map.alter alterf g counts

depth :: [Gate] -> Int
depth = maximum . Map.elems . foldl f Map.empty
  where f depths gate =
          let maxIn = maximum $ map (\id -> Map.findWithDefault 0 id depths) args
              args  = arguments gate
          in
            foldr (\id -> Map.insert id (maxIn + 1)) depths args

gateDepth :: [ID] -> [Gate] -> Int
gateDepth gates = maximum . Map.elems . foldl f Map.empty
  where f depths gate =
          let maxIn = maximum $ map (\id -> Map.findWithDefault 0 id depths) args
              args  = arguments gate
              tot   = if (gateName gate) `elem` gates then maxIn + 1 else maxIn
          in
            foldr (\id -> Map.insert id tot) depths args

tDepth :: [Gate] -> Int
tDepth = gateDepth ["T", "T*"]

computeStats :: DotQC -> FE.ProgramStats
computeStats circ =
  let gatelist   = fromCliffordT . toCliffordT . toGatelist $ circ
      counts     = gateCounts gatelist
      qubitCount = length . qubits $ circ
      totaldepth = Just $ depth gatelist
      tdepth     = Just $ tDepth gatelist
  in
    FE.ProgramStats counts Nothing qubitCount totaldepth tdepth


showStats :: DotQC -> [String]
showStats = FE.statsLines . computeStats

showCliffordTStats :: DotQC -> [String]
showCliffordTStats = showStats

{- Parser -}

space = char ' '
semicolon = char ';'
sep = space <|> tab
comment = char '#' >> manyTill anyChar endOfLine >> return '#'
delimiter = semicolon <|> endOfLine

skipSpace     = skipMany $ sep <|> comment
skipWithBreak = many1 (skipMany sep >> delimiter >> skipMany sep)

parseID = try $ do
  c  <- letter
  cs <- many (alphaNum <|> char '*')
  if (c:cs) == "BEGIN" || (c:cs) == "END" then fail "" else return (c:cs)
parseParams = sepEndBy (many1 alphaNum) (many1 sep)

parseDiscrete = do
  numerator <- option 1 nat
  string "pi"
  string "/2^"
  power <- int
  return $ dyadicPhase $ dyadic numerator power

parseContinuous = floating2 True >>= return . continuousPhase

parseAngle = do
  char '('
  theta <- sign <*> (parseDiscrete <|> parseContinuous)
  char ')'
  return theta

parseGate = do
  name <- parseID
  param <- optionMaybe parseAngle
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

parseDotQC :: ByteString -> Either ParseError DotQC
parseDotQC = parse parseFile ".qc parser"

printErr (Left l)  = Left $ show l
printErr (Right r) = Right r

optimizeDotQC :: ([ID] -> [ID] -> [Primitive] -> [Primitive]) -> DotQC -> DotQC
optimizeDotQC f qc = qc { decls = map go $ decls qc }
  where go decl =
          let circuitQubits = qubits qc ++ params decl
              circuitInputs = (Set.toList $ inputs qc) ++ params decl
              wrap g        = fromCliffordT . g . toCliffordT
          in
            decl { body = wrap (f circuitQubits circuitInputs) $ body decl }

decompileDotQC :: DotQC -> DotQC
decompileDotQC qc = qc { decls = map go $ decls qc }
  where go decl =
          let circuitQubits  = qubits qc ++ params decl
              circuitInputs  = (Set.toList $ inputs qc) ++ params decl
              resynthesize c = case resynthesizeCircuit $ toCliffordT c of
                Nothing -> c
                Just c' -> fromExtractionBasis c'
          in
            decl { body = resynthesize $ body decl }

formatFloatN floatNum numOfDecimals = showFFloat (Just numOfDecimals) floatNum ""

instance FE.ProgramRepresentation DotQC where
  readAndParse path = do
    src <- B.readFile path
    return $ printErr $ parseDotQC src

  expectValid _ = Right ()

  applyPass _ pass = case pass of
    FE.Triv        -> id
    FE.Inline      -> inlineDotQC
    FE.Unroll      -> id
    FE.MCT         -> expandToffolis
    FE.CT          -> expandAll
    FE.Simplify    -> simplifyDotQC
    FE.Phasefold   -> optimizeDotQC phaseFold
    FE.PauliFold d -> optimizeDotQC (pauliFold d)
    FE.Statefold d -> optimizeDotQC (stateFold d)
    FE.CNOTMin     -> optimizeDotQC minCNOT
    FE.TPar        -> optimizeDotQC tpar
    FE.Cliff       -> optimizeDotQC (\_ _ -> simplifyCliffords)
    FE.CZ          -> optimizeDotQC (\_ _ -> expandCNOT)
    FE.CX          -> optimizeDotQC (\_ _ -> expandCZ)
    FE.Decompile   -> decompileDotQC

  prettyPrint = show
  computeStats = computeStats

  prettyPrintWithBenchmarkInfo name time stats stats' verified qc =
    unlines (
        [ "# Feynman -- quantum circuit toolkit",
          "# Original (" ++ name ++ "):"
        ] ++ map ("#   " ++) (FE.statsLines stats) ++ [
          "# Result (" ++ formatFloatN time 3 ++ "ms" ++
          (if verified then ", Verified" else "") ++ "):"
        ] ++ map ("#   " ++) (FE.statsLines stats')
        ++ lines (show qc)
      )

  equivalenceCheck qc qc' =
    let circ    = toCliffordT . toGatelist $ qc
        circ'   = toCliffordT . toGatelist $ qc'
        vars    = union (qubits qc) (qubits qc')
        ins     = Set.toList $ inputs qc
        result  = validate True vars ins circ circ'
    in
      case (inputs qc == inputs qc', result) of
        (False, _)            -> Left $ "Circuits not equivalent (different inputs)"
        (_, NotIdentity ce)   -> Left $ "Circuits not equivalent (" ++ ce ++ ")"
        (_, Inconclusive sop) -> Left $ "Failed to verify: \n  " ++ show sop
        _                     -> Right qc'

