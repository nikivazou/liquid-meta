module Syntax where 


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


data Predicate = PTop 
  deriving Eq 

data Type    = TBase TBase Predicate
             | TFun Var Type Type 
             | TEx  Var Type Type 
  deriving Eq 

data Env = EEmp | EBind Var Type Env