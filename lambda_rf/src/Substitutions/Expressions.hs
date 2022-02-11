{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"  @-}

module Substitutions.Expressions where 

import Syntax 
import Expressions 
import Helpers.ProofCombinators
import Data.Set 

{-@ inline disjoined @-}
disjoined :: (Eq a, Ord a) => Set a -> Set a -> Bool 
disjoined s1 s2 = intersection s1 s2 == empty

{-@ inline subable @-}
subable :: Expr -> Expr -> Bool 
subable ex e = disjoined (boundVars e) (freeVars ex)


{-@ type Subable E =  {ex:Expr | subable ex e } @-}




{-@ reflect subst @-}
subst :: Expr -> Var -> Expr -> Expr 
{-@ subst :: e:Expr -> x:AnyVar -> ex:Subable e 
          -> {r:Expr | if (member x (freeVars e)) 
                         then ( (isSubsetOf (freeVars r) (union (difference (freeVars e) (singleton x)) (freeVars ex)))
                           && (union (boundVars e) (freeVars r) == union (boundVars e) (union (difference (freeVars e) (singleton x)) (freeVars ex)))
                           && (boundVars r == union (boundVars ex) (boundVars e))
                         )
                         else (r == e) } @-} 
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
{-@ substId :: e:Expr -> x:AnyVar -> {Substitutions.Expressions.subst e x (EVar x) == e} @-}
substId :: Expr -> Var -> () 
substId (EApp e1 e2) x = substId e1 x ? substId e2 x 
substId (ELam y e) x   = substId e  x  
substId _ _ = ()   

{-@ ple substFlip @-}
{-@ substFlip :: e:Expr -> x:AnyVar -> ex:Expr
              -> y:{AnyVar | y /= x && (not (member y (freeVars ex)) || not (member y (boundVars e)) )} 
              -> ey:{Expr | not (member x (freeVars ey)) 
                         && subable ey e && subable ey ex && subable (subst ex y ey) (subst e y ey) && subable ey ex } 
              -> { subst (subst e y ey) x (subst ex y ey) == 
                   subst (subst e x ex) y ey } @-}
substFlip :: Expr -> Var -> Expr -> Var -> Expr -> ()
substFlip (EApp e1 e2) x ex y ey 
  = substFlip e1 x ex y ey 
  ? substFlip e2 x ex y ey 
substFlip (ELam z e) x ex y ey | z == x 
  = () 
substFlip (ELam z ez) x ex y ey | z == y 
  = assert (subst ex y ey == ex)
substFlip (ELam _ e) x ex y ey 
  = substFlip e x ex y ey  
substFlip (EVar z) x ex y ey | z == y 
  = assert (subst ey x (subst ex y ey) == ey) 
substFlip (EVar z) x ex y ey 
  = ()
substFlip (EPrim _) _ _ _ _ 
  = () 


{-@ fbVars :: e:Expr -> { disjoined (freeVars e) (boundVars e) } @-}
fbVars :: Expr -> () 
fbVars = undefined 