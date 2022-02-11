module Syntax where 

import Data.Set 

type Var = Int 
{-@ type Var    = {v:Int | 0 <  v } @-}
{-@ type AnyVar = {v:Int | 0 <= v } @-}
data EPrim = PBool Bool | PInt Int 
  deriving Eq 
  
data TPrim = TBool | TInt 
  deriving Eq 

data Expr = EApp Expr Expr 
          | ELam Var  Expr 
          | EVar Var 
          | EPrim EPrim 
  deriving Eq

data TBase   = TPrim TPrim
  deriving Eq 


data Predicate = Predicate Int Expr 
  deriving Eq 

{-@ type Refinement = {p:Expr | true } @-}

{-@ data Predicate = Predicate {pv :: {pv:AnyVar | pv == pvar},  pexpr :: Refinement } @-}
{-@ reflect pvar @-}
{-@ pvar :: AnyVar @-}
pvar :: Int
pvar = 0  


{-@ reflect top @-}
top :: Predicate 
top = Predicate pvar (EPrim (PBool True))

data Type    = TBase TBase Predicate
             | TFun Var Type Type 
             | TEx  Var Type Type 
  deriving Eq 

data FType = FTBase TPrim | FTFun FType FType 
  deriving Eq 

{-@ typeSize :: Type -> Nat @-}
{-@ measure typeSize @-}
typeSize :: Type -> Int 
typeSize (TBase _ _)   = 1
typeSize (TFun _ tx t) = 1 + typeSize tx + typeSize t 
typeSize (TEx  _ tx t) = 1 + typeSize tx + typeSize t 


data Env = EEmp | EBind Var Type Env
  deriving Eq

data UEnv = UEEmp | UEBind Var FType UEnv
  deriving Eq

-- Invariant: pvar cannot enter in the environment!  
{-@ data Env = EEmp 
             | EBind { envVar  :: {v:Var | 0 < v } 
                     , eType ::  Type
                     , eTail :: {g:Env | not (member envVar (dom g)) } 
                     } @-}


{-@ measure udom @-}
udom :: UEnv -> Set Var 
udom (UEBind x _ g) = singleton x `union` udom g 
udom UEEmp          = empty 

{-@ measure dom @-}
dom :: Env -> Set Var 
{-@ dom :: Env -> {d:Set Var | not (member pvar d)} @-}
dom (EBind x _ g) = singleton x `union` dom g 
dom EEmp          = empty 