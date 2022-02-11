{-@ LIQUID "--reflection" @-}
module Assumptions.Constants where 

import Propositions 
import Syntax 
import Types 
import Substitutions.Types

import Data.Set 



noTEx :: EPrim -> () 
{-@ noTEx :: p:EPrim -> { not (isTEx (primType p)) } @-}
noTEx = undefined -- SAFE undefined 


{-@ primWellFormed :: g:Env -> p:EPrim 
                   -> Prop (WellFormedEnv g) 
                   -> Prop (IsWellFormed g (primType p)) @-}
primWellFormed :: Env -> EPrim -> WellFormedEnv -> IsWellFormed 
primWellFormed = undefined -- SAFE undefined 


{-@ primAss :: x:Var -> tx:Type -> t:Type -> {p:EPrim | primType p = TFun x tx t } 
         -> ex:Expr -> g:Env 
         -> Prop (HasType g ex tx) 
         -> Prop (HasType g (delta p ex) (Substitutions.Types.subst t x ex)) @-}
primAss :: Var -> Type -> Type -> EPrim -> Expr -> Env -> HasType -> HasType 
primAss = undefined       -- SAFE undefined 

primTypeNoFree :: EPrim -> ()
{-@ primTypeNoFree :: p:EPrim -> { freeVars (primType p) == empty} @-}
primTypeNoFree = undefined -- SAFE undefined 