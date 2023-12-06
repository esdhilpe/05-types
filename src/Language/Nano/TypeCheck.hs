{-# LANGUAGE FlexibleInstances, OverloadedStrings, BangPatterns #-}

module Language.Nano.TypeCheck where

import Language.Nano.Types
import Language.Nano.Parser

import qualified Data.List as L
import           Text.Printf (printf)  
import           Control.Exception (throw)

--------------------------------------------------------------------------------
typeOfFile :: FilePath -> IO Type
typeOfFile f = parseFile f >>= typeOfExpr

typeOfString :: String -> IO Type
typeOfString s = typeOfExpr (parseString s)

typeOfExpr :: Expr -> IO Type
typeOfExpr e = do
  let (!st, t) = infer initInferState preludeTypes e
  if (length (stSub st)) < 0 then throw (Error ("count Negative: " ++ show (stCnt st)))
  else return t

--------------------------------------------------------------------------------
-- Problem 1: Warm-up
--------------------------------------------------------------------------------

-- | Things that have free type variables
class HasTVars a where
  freeTVars :: a -> [TVar]

-- | Type variables of a type
instance HasTVars Type where
  freeTVars t     = case t of
    TInt -> []
    TBool -> []
    t1 :=> t2 -> L.nub $ freeTVars t1 ++ freeTVars t2
    TVar x -> [x]
    TList l -> freeTVars l

-- | Free type variables of a poly-type (remove forall-bound vars)
instance HasTVars Poly where
  freeTVars s     = case s of
    Mono x -> freeTVars x
    Forall id p -> L.filter a b
                   where
                    a = (\y -> y /= id)
                    b = freeTVars p


-- | Free type variables of a type environment
instance HasTVars TypeEnv where
  freeTVars gamma   = concat [freeTVars s | (x, s) <- gamma]  
  
-- | Lookup a variable in the type environment  
lookupVarType :: Id -> TypeEnv -> Poly
lookupVarType x ((y, s) : gamma)
  | x == y    = s
  | otherwise = lookupVarType x gamma
lookupVarType x [] = throw (Error ("unbound variable: " ++ x))

-- | Extend the type environment with a new biding
extendTypeEnv :: Id -> Poly -> TypeEnv -> TypeEnv
extendTypeEnv x s gamma = (x,s) : gamma  

-- | Lookup a type variable in a substitution;
--   if not present, return the variable unchanged
-- Part 1b
-- Base Case: If empty subst, return variable unchanged
lookupTVar :: TVar -> Subst -> Type
-- Base Case:
lookupTVar a [] = TVar a
lookupTVar a ((x,y):sub) = 
  if a == x then y
  else lookupTVar a sub

-- | Remove a type variable from a substitution
-- Part 1b
-- Utilize .filter
-- if x /= a, then (x,y) is in the list
-- creating a new list containing pairs from sub which
-- x is not equal to a.
removeTVar :: TVar -> Subst -> Subst
removeTVar a sub = [(x, y) | (x, y) <- sub, x /= a]
     
-- | Things to which type substitutions can be apply
class Substitutable a where
  apply :: Subst -> a -> a
  
-- | Apply substitution to type
-- Part 1b
instance Substitutable Type where  
  apply sub t         = case t of
    TInt -> TInt
    TBool -> TBool
    t1 :=> t2 -> apply sub t1 :=> apply sub t2
    TVar x -> lookupTVar x sub
    TList l -> list (apply sub l)

-- | Apply substitution to poly-type
-- Part 1b
instance Substitutable Poly where    
  apply sub s         = case s of
    Mono x -> Mono (apply sub x)
    Forall id p -> Forall id m
                   where
                    temp = removeTVar id sub
                    m = apply temp p

-- | Apply substitution to (all poly-types in) another substitution
instance Substitutable Subst where  
  apply sub to = zip keys $ map (apply sub) vals
    where
      (keys, vals) = unzip to
      
-- | Apply substitution to a type environment
instance Substitutable TypeEnv where  
  apply sub gamma = zip keys $ map (apply sub) vals
    where
      (keys, vals) = unzip gamma
      
-- | Extend substitution with a new type assignment
-- Part 1b
extendSubst :: Subst -> TVar -> Type -> Subst
extendSubst sub a t = (a,t):tail
                        where
                          tail = apply ((a,t):sub) sub
      
--------------------------------------------------------------------------------
-- Problem 2: Unification
--------------------------------------------------------------------------------
      
-- | State of the type inference algorithm      
data InferState = InferState { 
    stSub :: Subst -- ^ current substitution
  , stCnt :: Int   -- ^ number of fresh type variables generated so far
} deriving (Eq,Show)

-- | Initial state: empty substitution; 0 type variables
initInferState = InferState [] 0

-- | Fresh type variable number n
freshTV n = TVar $ "a" ++ show n      
    
-- | Extend the current substitution of a state with a new type assignment   
extendState :: InferState -> TVar -> Type -> InferState
extendState (InferState sub n) a t = InferState (extendSubst sub a t) n
        
-- | Unify a type variable with a type; 
--   if successful return an updated state, otherwise throw an error
unifyTVar :: InferState -> TVar -> Type -> InferState
unifyTVar st a t = error "TBD: unifyTVar"
    
-- | Unify two types;
--   if successful return an updated state, otherwise throw an error
unify :: InferState -> Type -> Type -> InferState
unify st t1 t2 = error "TBD: unify"

--------------------------------------------------------------------------------
-- Problem 3: Type Inference
--------------------------------------------------------------------------------    
  
infer :: InferState -> TypeEnv -> Expr -> (InferState, Type)
infer st _   (EInt _)          = error "TBD: infer EInt"
infer st _   (EBool _)         = error "TBD: infer EBool"
infer st gamma (EVar x)        = error "TBD: infer EVar"
infer st gamma (ELam x body)   = error "TBD: infer ELam"
infer st gamma (EApp e1 e2)    = error "TBD: infer EApp"
infer st gamma (ELet x e1 e2)  = error "TBD: infer ELet"
infer st gamma (EBin op e1 e2) = infer st gamma asApp
  where
    asApp = EApp (EApp opVar e1) e2
    opVar = EVar (show op)
infer st gamma (EIf c e1 e2) = infer st gamma asApp
  where
    asApp = EApp (EApp (EApp ifVar c) e1) e2
    ifVar = EVar "if"    
infer st gamma ENil = infer st gamma (EVar "[]")

-- | Generalize type variables inside a type
generalize :: TypeEnv -> Type -> Poly
generalize gamma t = error "TBD: generalize"
    
-- | Instantiate a polymorphic type into a mono-type with fresh type variables
instantiate :: Int -> Poly -> (Int, Type)
instantiate n s = error "TBD: instantiate"
      
-- | Types of built-in operators and functions      
preludeTypes :: TypeEnv
preludeTypes =
  [ ("+",    Mono $ TInt :=> TInt :=> TInt)
  , ("-",    error "TBD: -")
  , ("*",    error "TBD: *")
  , ("/",    error "TBD: /")
  , ("==",   error "TBD: ==")
  , ("!=",   error "TBD: !=")
  , ("<",    error "TBD: <")
  , ("<=",   error "TBD: <=")
  , ("&&",   error "TBD: &&")
  , ("||",   error "TBD: ||")
  , ("if",   error "TBD: if")
  -- lists: 
  , ("[]",   error "TBD: []")
  , (":",    error "TBD: :")
  , ("head", error "TBD: head")
  , ("tail", error "TBD: tail")
  ]
