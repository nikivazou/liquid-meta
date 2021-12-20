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

data Type    = TBase TBase | TFun Type Type 
  deriving Eq 

data Env = EEmp | EBind Var Type Env