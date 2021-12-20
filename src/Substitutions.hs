{-@ LIQUID "--reflection" @-}

module Substitutions where 

import Syntax 

{-@ reflect subst @-}
subst :: Expr -> Var -> Expr -> Expr 
subst (EApp e1 e2) x ex 
  = EApp (subst e1 x ex) (subst e2 x ex)
subst (ELam y e) x ex 
  | x == y    = ELam y e 
  | otherwise = ELam y (subst e x ex)
subst (EVar y) x ex 
  | x == y    = ex 
  | otherwise = EVar y  
subst (EPrim p) _ _ 
  = EPrim p
