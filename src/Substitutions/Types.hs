{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local"  @-}

module Substitutions.Types where 

import Syntax 
import qualified Expressions as E 
import qualified Substitutions.Expressions as E
import Helpers.ProofCombinators

import Data.Set 
import Types 

{-@ ignore subst @-}
{-@ reflect subst @-}
subst :: Type -> Var -> Expr -> Type 
{-@ subst :: t:Type -> x:AnyVar -> ex:Expr 
          -> {r:Type | if (member x (freeVars t)) 
                         then (isSubsetOf (freeVars r) (union (difference (freeVars t) (singleton x)) (E.freeVars ex)))
                         else (r == t) } @-} 
subst (TBase b (Predicate x e)) y ey 
  | x == y    = TBase b (Predicate x e)
  | otherwise = TBase b (Predicate x (E.subst e y ey)) 
subst (TFun x tx t) y ey 
  | x == y    = TFun x (subst tx y ey) t 
  | otherwise = TFun x (subst tx y ey) (subst t y ey)
subst (TEx x tx t) y ey 
  | x == y    = TEx x (subst tx y ey) t 
  | otherwise = TEx x (subst tx y ey) (subst t y ey)  


{-@ ple substId @-}
substId :: Type -> Var -> ()
{-@ substId :: t:Type -> x:AnyVar -> {Substitutions.Types.subst t x (EVar x) == t} @-}
substId (TBase _ (Predicate _ e)) x = E.substId e x 
substId (TFun _ t1 t2) x = substId t1 x ? substId t2 x  
substId (TEx  _ t1 t2) x = substId t1 x ? substId t2 x  


{-@ ple substFlip @-}
{-@ substFlip :: t:Type -> x:Var -> ex:Expr 
              -> y:{Var | y /= x && not (member y (boundVars t))} 
              -> ey:{Expr | not (member x (E.freeVars ey))} 
              -> { subst (subst t y ey) x (E.subst ex y ey) == subst (subst t x ex) y ey} @-}
substFlip :: Type -> Var -> Expr -> Var -> Expr -> ()
substFlip (TEx z tz tt)  x ex y ey | z == y 
  = substFlip tz x ex y ey 
  ? substFlip tt x ex y ey 
substFlip (TEx z tz tt)  x ex y ey | z == x 
  = substFlip tz x ex y ey 
  ? substFlip tt x ex y ey 
substFlip (TEx z tz tt)  x ex y ey 
  = substFlip tz x ex y ey 
  ? substFlip tt x ex y ey   
substFlip (TFun z tz tt) x ex y ey | z == x 
  = substFlip tz x ex y ey 
  ? substFlip tt x ex y ey  
substFlip (TFun z tz tt) x ex y ey | z == y 
  = substFlip tz x ex y ey 
  ? substFlip tt x ex y ey  
substFlip (TFun z tz tt) x ex y ey 
  = substFlip tz x ex y ey 
  ? substFlip tt x ex y ey  
substFlip t@(TBase b (Predicate z e)) x ex y ey | z == x || z == y 
  = ()
substFlip t@(TBase b (Predicate z e)) x ex y ey 
  =  E.substFlip e x ex y ey 

-- NV This again
checkMember :: Int -> Set Int -> Bool 
checkMember = member 