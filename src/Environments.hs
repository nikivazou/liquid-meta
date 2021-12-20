{-@ LIQUID "--reflection" @-}

module Environments where 
import Syntax 

{-@ reflect inEnv @-}
inEnv :: Var -> Type -> Env -> Bool 
inEnv _ _  EEmp = False 
inEnv x t (EBind x' t' g)
  = if x == x' && t == t' then True else inEnv x t g 

{-@ reflect eAppend @-}
eAppend :: Env -> Env -> Env 
eAppend (EBind x t g1) g2 = EBind x t (eAppend g1 g2)
eAppend EEmp           g  = g 