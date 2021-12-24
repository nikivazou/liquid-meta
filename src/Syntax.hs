module Syntax where 

{- measure Set_mem :: a -> Bool@-}

type Var = Int 
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


data Predicate = Predicate Var Expr 
  deriving Eq 

{-@ data Predicate = Predicate {pv :: {pv:Var | pv == pvar},  pexpr :: Expr } @-}
{-@ reflect pvar @-}
pvar :: Var
pvar = 0 


{-@ reflect top @-}
top :: Predicate 
top = Predicate 0 (EPrim (PBool True))

data Type    = TBase TBase Predicate
             | TFun Var Type Type 
             | TEx  Var Type Type 
  deriving Eq 

{-@ typeSize :: Type -> Nat @-}
{-@ measure typeSize @-}
typeSize :: Type -> Int 
typeSize (TBase _ _)   = 1
typeSize (TFun _ tx t) = 1 + typeSize tx + typeSize t 
typeSize (TEx  _ tx t) = 1 + typeSize tx + typeSize t 


data Env = EEmp | EBind Var Type Env