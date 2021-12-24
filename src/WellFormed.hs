{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module WellFormed where 

import Syntax
import Propositions
import Environments 
import Substitutions.Types

import Data.Set 
import Types 



wellformed :: Env -> Type -> IsWellFormed -> ()
{-@ wellformed :: g:Env -> t:Type -> Prop (IsWellFormed g t) -> { isSubsetOf (freeVars t) (dom g) } @-}
wellformed = undefined 

wellformedTEx :: Env -> Var -> Type -> Type -> Expr -> HasType -> IsWellFormed -> IsWellFormed 
{-@ wellformedTEx :: g:Env -> x:Var -> tx:Type -> t:Type -> ex:Expr 
                 -> Prop (HasType g ex tx)
                 -> Prop (IsWellFormed g (TEx x tx t))
                 -> Prop (IsWellFormed g (Substitutions.Types.subst t x ex)) @-}
wellformedTEx = undefined 


wellformedTFunArg :: Env -> Var -> Type -> Type -> IsWellFormed -> IsWellFormed 
{-@ wellformedTFunArg :: g:Env -> x:Var -> tx:Type -> t:Type 
                 -> Prop (IsWellFormed g (TFun x tx t))
                 -> Prop (IsWellFormed g tx) @-}
wellformedTFunArg _ _ _ _ (WFFun _ _ _ _ wf _) = wf


wellformedTFunRes :: Env -> Var -> Type -> Type -> Type -> IsSubType -> IsWellFormed -> IsWellFormed 
{-@ wellformedTFunRes :: g:Env -> x:Var -> tx:Type -> t:Type -> sx:Type 
                 -> Prop (IsSubType g sx tx)
                 -> Prop (IsWellFormed g (TFun x tx t))
                 -> Prop (IsWellFormed (EBind x sx g) t) @-}
wellformedTFunRes _ _ _ _ _ _ (WFFun _ _ _ _ wf _) = undefined

wfWeakening :: Env -> Env -> Var -> Type -> Type -> IsWellFormed -> IsWellFormed 
{-@ wfWeakening :: g1:Env -> g2:Env -> x:Var -> tx:Type -> t:Type  
                 -> Prop (IsWellFormed g2 t)
                 -> Prop (IsWellFormed (eAppend g1 (EBind x tx g2)) t) @-}
wfWeakening = undefined