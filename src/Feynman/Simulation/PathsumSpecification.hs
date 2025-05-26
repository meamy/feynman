module Feynman.Simulation.PathsumSpecification where


import Feynman.Algebra.Base (DMod2, fromDyadic, toDyadic)
import Feynman.Algebra.Pathsum.Balanced hiding (Var, Zero)
import qualified Feynman.Algebra.Pathsum.Balanced as PS
import Feynman.Algebra.Polynomial.Multilinear
import Feynman.Core (ID)
import Feynman.Frontend.OpenQASM.Syntax
import Feynman.Simulation.Env

import qualified Feynman.Util.Unicode as U

import Data.Maybe
import Control.Monad.State.Strict

-- | Gives the unicode representation of the ith offset of v
varOfOffset :: ID -> Int -> String
varOfOffset v i = U.sub v (fromIntegral i)

bindingList :: [TypedID] -> Env -> [String]
bindingList nxs env = concatMap go nxs
  where go (v, _)  = case evalState (searchBinding v) env of
          Just (QReg sz offset) -> [varOfOffset v i | i <- [offset..sz+offset-1]]
          _                -> [v]

bindingList' :: [TypedID] -> Env -> [String]
bindingList' nxs env = concatMap go nxs
  where go (v, _)  = case evalState (searchBinding v) env of
          Just (QReg sz _) -> [varOfOffset v i | i <- [0..sz-1]]
          _                -> [v]

polyOfExp :: [TypedID] -> Exp -> PseudoBoolean PS.Var Double
polyOfExp boundIDs = polyOfExp'
  where
    polyOfExp' exp
      | isJust (evalExp exp) = constant $ fromJust (evalExp exp)
      | otherwise            = case exp of
          FloatExp d       -> constant d
          IntExp i         -> constant $ fromIntegral i
          PiExp            -> constant $ pi
          VarExp v         -> case lookup v boundIDs of
            Nothing -> ofVar $ FVar v
            Just TypeQubit   -> ofVar $ FVar v
            Just (TypeInt n) -> polyOfExp' $ bitBlast v n
          OffsetExp v i    -> ofVar $ FVar (varOfOffset v i)
          UOpExp uop e     -> cast (evalUOp uop) $ polyOfExp' e
          BOpExp e1 bop e2 -> case bop of
            PlusOp  -> e1' + e2'
            MinusOp -> e1' - e2'
            TimesOp -> e1' * e2'
            DivOp   -> error "Unsupported division of polynomials"
            PowOp   -> error "Unsupported exponent of polynomials"
            where e1' = polyOfExp' e1
                  e2' = polyOfExp' e2

polyOfMaybeExp :: [TypedID] -> Maybe Exp -> PseudoBoolean PS.Var Double
polyOfMaybeExp boundIDs Nothing    = 0
polyOfMaybeExp boundIDs (Just exp) = polyOfExp boundIDs exp

decomposeScalar :: Maybe Exp -> (Int, DMod2)
decomposeScalar Nothing    = (0, 0)
decomposeScalar (Just exp) = error "Normalization check not implemented"

castDMod2 :: PseudoBoolean v Double -> PseudoBoolean v DMod2
castDMod2 = cast (fromDyadic . toDyadic . (/pi))

castBoolean :: PseudoBoolean v Double -> SBool v
castBoolean = cast go where
  go 0.0 = 0
  go 1.0 = 1
  go _   = error "Not a Boolean polynomial"

sopOfPSSpec :: Spec -> Env -> Pathsum DMod2
sopOfPSSpec (PSSpec args scalar pvars ampl ovals) env = (bind bindings . sumover sumvars $ sop)
  where bindings      = bindingList' args env
        (s, gphase)   = decomposeScalar scalar
        boundIDs      = args ++ pvars
        pp            = constant gphase + (castDMod2 $ polyOfMaybeExp boundIDs ampl)
        out           = map (castBoolean . polyOfExp []) $ expandOutput boundIDs ovals
        sop           = Pathsum s 0 (length out) 0 pp out
        getID (id, _) = id
        sumvars       = concat . map vars $ pvars
        vars (id, t)  = case t of
          TypeInt n -> [varOfOffset id i | i <- [0..n-1]]
          TypeQubit -> [id]

createAncillaMask :: Spec -> Pathsum DMod2
createAncillaMask = go . inputs
  where 
    go [] = mempty
    go (a:as) = case a of
      (_, TypeQubit)     -> identity 1 <> go as
      (_, TypeInt n)     -> identity n <> go as
      (_, TypeAncilla n) -> (ket $ replicate n 0) <> go as

bitBlast :: ID -> Int -> Exp
bitBlast v n = foldl (\a b -> BOpExp a PlusOp b) (IntExp 0) [BOpExp (OffsetExp v i) TimesOp (powertwo i) | i <- [0..n-1]]
  where powertwo 0 = IntExp 1
        powertwo j = BOpExp (IntExp 2) TimesOp (powertwo $ j-1)

{- 1/28, I think need to expand int types recursively, to take care of exps like x + y both ints -}
expandInts :: [TypedID] -> [Exp] -> [Exp]
expandInts boundIDs = concat . map expand
  where 
    expand exp = case exp of
      VarExp v -> case lookup v boundIDs of
                  Nothing          -> error "Variable not bound"
                  Just TypeQubit   -> [VarExp v]
                  Just (TypeInt n) -> [OffsetExp v i | i <- [0..n-1]]
      e        -> [e]

lengthOfExp :: [TypedID] -> Exp -> Int
lengthOfExp boundIDs = go
  where 
    go e = case e of
      VarExp v -> case lookup v boundIDs of
                    Nothing              -> error "Variable not bound"
                    Just TypeQubit       -> 1
                    Just (TypeInt n)     -> n
                    Just (TypeAncilla n) -> n
      FloatExp _     -> 1
      IntExp _       -> 1
      PiExp          -> 1
      OffsetExp _ _  -> 1
      UOpExp _ e'    -> go e'
      BOpExp e1 _ e2 -> let l1 = go e1
                            l2 = go e2 in
                          if l1 == 1 || l2 == 1 || l1 == l2
                            then max l1 l2
                            else error "Variable length mismatch" 

expandOutput :: [TypedID] -> [Exp] -> [Exp]
expandOutput boundIDs = concat . map (expandOutputExp boundIDs)

{-
expandOutputExp :: [TypedID] -> Exp -> [Exp]
expandOutputExp boundIDs e = let l = lengthOfExp boundIDs e in
  map (expand e) [0..l-1]
  where 
    expand exp index = case exp of
      VarExp v -> case lookup v boundIDs of
                    Nothing -> error "Variable not bound"
                    Just TypeQubit ->       VarExp v
                    Just (TypeInt _) ->     OffsetExp v index
                    {- ancilla should be 0? or offset v i -}
                    Just (TypeAncilla _) -> IntExp 0
      BOpExp e1 bop e2 -> BOpExp (expand e1 index) bop (expand e2 index)
      UOpExp uop e     -> UOpExp uop (expand e index)
      OffsetExp _ _    -> exp
      FloatExp _       -> exp
      IntExp _         -> exp
      PiExp            -> exp
-}

expandOutputExp :: [TypedID] -> Exp -> [Exp]
expandOutputExp boundIDs e = let l = lengthOfExp boundIDs e in
  expand e
  where
    typeOf exp = case exp of
      VarExp v -> case lookup v boundIDs of
                    Nothing -> error "Variable not bound"
                    Just TypeQubit ->       TypeQubit
                    Just (TypeInt n) ->     TypeInt n
                    {- ancilla should not be allowed maybe? -}
                    Just (TypeAncilla n) -> TypeInt n
      BOpExp e1 _ e2 -> case (typeOf e1, typeOf e2) of
                          (TypeQubit, t) -> t
                          (t, TypeQubit) -> t
                          (TypeInt n, TypeInt m) | n == m -> TypeInt n
                          (TypeInt _, TypeInt _) -> error "length mismatch in spec"
      FloatExp _ -> TypeQubit
      IntExp _ -> TypeQubit
      PiExp -> TypeQubit
      OffsetExp _ _ -> TypeQubit
      UOpExp _ e -> typeOf e

    expand exp = case exp of
      VarExp v -> case lookup v boundIDs of
                    Nothing -> error "Variable not bound"
                    Just TypeQubit ->       [VarExp v]
                    Just (TypeInt n) ->     [OffsetExp v i | i <- [0..n-1]]
                    {- ancilla should be 0? or offset v i -}
                    Just (TypeAncilla n) -> [IntExp 0 | _ <- [0..n-1]]
      BOpExp e1 bop e2 ->
        case typeOf exp of
          TypeQubit -> [exp]
          TypeInt n -> [indexOf exp i | i <- [0..n-1]]
      UOpExp uop e     -> map (UOpExp uop) $ expand e
      OffsetExp _ _    -> [exp]
      FloatExp _       -> [exp]
      IntExp _         -> [exp]
      PiExp            -> [exp]

    indexOf exp (-1) = IntExp 0
    indexOf exp index = case exp of
      VarExp v -> case typeOf exp of
                    TypeQubit -> exp
                    TypeInt _ -> OffsetExp v index
      {- would we ever want to have x:qubit + y:int[n]? what should that mean -}
      BOpExp e1 bop e2    ->
        case (typeOf e1, typeOf e2) of
          (TypeQubit, _)         -> BOpExp e1 bop (indexOf e2 index)
          (_, TypeQubit)         -> BOpExp (indexOf e1 index) bop e2
          (TypeInt n, TypeInt _) -> 
            case bop of
              PlusOp -> BOpExp (BOpExp (indexOf e1 index) PlusOp (indexOf e2 index)) PlusOp (carryOf e1  e2 (index-1))
              op     -> BOpExp (indexOf e1 index) op (indexOf e2 index)
      UOpExp uop e        -> UOpExp uop (indexOf e index)

    carryOf e1 e2 index
      | index < 0 = IntExp 0
      | index == 0 = BOpExp (indexOf e1 index) TimesOp (indexOf e2 index)
      | otherwise  = 
          BOpExp (BOpExp (indexOf e1 index) TimesOp (indexOf e2 index))
            PlusOp (BOpExp (carryOf e1 e2 (index-1)) TimesOp (BOpExp (indexOf e1 (index)) PlusOp (indexOf e2 (index))))
