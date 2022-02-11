{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"  @-}

module Expressions where 

import Syntax 
import Helpers.ProofCombinators
import Data.Set 


{-@ measure isValue @-}
isValue :: Expr -> Bool 
isValue (EApp _ _) = False 
isValue (ELam _ _) = True 
isValue (EPrim _)  = True 
isValue (EBVar _)  = False 
isValue (EFVar _)  = False 


{-@ measure freeVars @-}
freeVars :: Expr -> Set Var  
freeVars (EApp e1 e2) = freeVars e1 `union` freeVars e2 
freeVars (ELam _ e)   = freeVars e
freeVars (EFVar x)    = singleton x 
freeVars (EBVar x)    = empty
freeVars (EPrim _)    = empty


{-@ measure boundVars @-}
boundVars :: Expr -> Set Var 
boundVars (EApp e1 e2) = boundVars e1 `union` boundVars e2
boundVars (ELam _ e)   = boundVars e 
boundVars (EBVar x)    = singleton x 
boundVars (EFVar _)    = empty 
boundVars (EPrim _)    = empty
 

{-@ reflect open @-}
{-@ open :: e:Expr -> ex:Expr 
         -> {s:Expr | freeVars s = freeVars e || freeVars s = union (freeVars e) (freeVars ex) } @-} 
open :: Expr -> Expr -> Expr 
open e u = substBound e 0 u 

{-@ reflect substBound @-}
{-@ substBound :: e:Expr -> BVar -> ex:Expr 
               -> {s:Expr | freeVars s = freeVars e || freeVars s = union (freeVars e) (freeVars ex)} @-} 
substBound :: Expr -> BVar -> Expr -> Expr 
substBound (EApp e1 e2) x ex 
  = EApp (substBound e1 x ex) (substBound e2 x ex)
substBound (ELam t e) x ex 
  = ELam t (substBound e (x+1) ex)
substBound (EFVar y) _ _   
  =  EFVar y   
substBound (EBVar y) x ex 
  | x == y    = ex 
  | otherwise = EBVar y  
substBound (EPrim p) _ _ 
  = EPrim p


{-@ reflect lc @-}
lc :: Expr -> Bool
lc e = lc_at 0 e 

{-@ reflect lc_at @-}
lc_at :: BVar -> Expr -> Bool 
lc_at k (EBVar i)    = i < k 
lc_at k (EFVar _)    = True 
lc_at k (EApp e1 e2) = lc_at k e1 && lc_at k e2 
lc_at k (ELam _ e)   = lc_at (k+1) e 
lc_at k (EPrim _)    = True 

{-@ reflect subst @-}
{-@ subst :: e:Expr -> x:Var -> ex:Expr 
          -> {s:Expr | isSubsetOf (freeVars s) (union (freeVars e) (freeVars ex)) 
                     &&  ((not (member x (freeVars e))) => s == e )} @-}
subst :: Expr -> Var -> Expr -> Expr 
subst (EApp e1 e2) x ex 
  = EApp (subst e1 x ex) (subst e2 x ex)
subst (ELam t e) x ex 
  = ELam t (subst e x ex)
subst (EFVar y) x ex  
  = if x == y then ex else EFVar y   
subst (EBVar y) _ _
  = EBVar y   
subst (EPrim p) _ _ 
  = EPrim p


