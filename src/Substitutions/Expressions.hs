{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local"  @-}

module Substitutions.Expressions where 

import Syntax 
import Expressions 
import Helpers.ProofCombinators
import Data.Set 

{-@ reflect subst @-}
subst :: Expr -> Var -> Expr -> Expr 
{-@ subst :: e:Expr -> x:Var -> ex:Expr 
          -> {r:Expr | (not (member x (Expressions.freeVars e))) => r == e } @-} 
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

{-@ ple substId @-}
{-@ substId :: e:Expr -> x:Var -> {Substitutions.Expressions.subst e x (EVar x) == e} @-}
substId :: Expr -> Var -> () 
substId (EApp e1 e2) x = substId e1 x ? substId e2 x 
substId (ELam y e) x   = substId e  x  
substId _ _ = ()   
