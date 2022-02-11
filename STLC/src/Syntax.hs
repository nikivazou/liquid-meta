module Syntax where 

import Data.Set 
import Helpers.ProofCombinators

type  Var = Int 
type BVar = Int 

{-@ type BVar = {i:Int | 0 <= i} @-} 

data EPrim = PBool Bool  | PInt Int 
           | PNot | PAdd | PIAdd Int 
  deriving Eq 
  
data TPrim = TBool | TInt 
  deriving Eq 

data Expr = EApp  Expr Expr 
          | ELam  Type Expr 
          | EBVar BVar 
          | EFVar Var 
          | EPrim EPrim 
  deriving Eq

data Type = TPrim TPrim
          | TFun Type Type 
  deriving Eq 

{-@ measure isTFun @-}
isTFun :: Type -> Bool 
isTFun (TFun _ _) = True 
isTFun _          = False 

{-@ typeSize :: Type -> Nat @-}
{-@ measure typeSize @-}
typeSize :: Type -> Int 
typeSize (TPrim _)   = 1
typeSize (TFun tx t) = 1 + typeSize tx + typeSize t 

data Env = EEmp | EBind Var Type Env
  deriving Eq

{-@ data Env = EEmp 
             | EBind { eVar  :: Var
                     , eType :: Type
                     , eTail :: {g:Env | not (member eVar (dom g)) } 
                     } @-}

{-@ measure dom @-}
dom :: Env -> Set Var 
dom (EBind x _ g) = singleton x `union` dom g 
dom EEmp          = empty 


{-@ reflect lookupEnv @-}
lookupEnv :: Env -> Var -> Type 
{-@ lookupEnv :: g:Env -> {x:Var | member x (dom g)} -> Type  @-} 
lookupEnv (EBind x t g) y
  | x == y    = t 
  | otherwise = lookupEnv g y 


{-@ reflect eAppend @-}
{-@ eAppend :: g1:Env -> g2:{Env | disjoined (dom g1) (dom g2) } 
            -> {g:Env | dom g == union (dom g1) (dom g2) } @-}
eAppend :: Env -> Env -> Env 
eAppend EEmp            g2 = g2 
eAppend (EBind x tx g1) g2 = EBind x tx (eAppend g1 g2)


{-@ inline disjoined @-}
disjoined :: Ord a => Set a -> Set a -> Bool 
disjoined g1 g2 = intersection g1 g2 == empty
