{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local"  @-}

module Substitutions.Types where 

import Syntax 
import qualified Substitutions.Expressions as E
import Helpers.ProofCombinators

import Data.Set 
import Types 

{-@ reflect subst @-}
subst :: Type -> Var -> Expr -> Type 
{-@ subst :: t:Type -> x:Var -> ex:Expr 
          -> {r:Type | (not (member x (Types.freeVars t))) => r == t } @-} 
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
{-@ substId :: t:Type -> x:Var -> {Substitutions.Types.subst t x (EVar x) == t} @-}
substId (TBase _ (Predicate _ e)) x = E.substId e x 
substId (TFun _ t1 t2) x = substId t1 x ? substId t2 x  
substId (TEx  _ t1 t2) x = substId t1 x ? substId t2 x  

