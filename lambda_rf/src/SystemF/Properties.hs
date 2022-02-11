{-@ LIQUID "--reflection" @-}

module SystemF.Properties where 

import Syntax 
import Unrefine
import Propositions 
import Environments
import Substitutions.Expressions
import Substitutions.Environment

{-@ reflect ueAppend @-}
ueAppend :: UEnv -> UEnv -> UEnv
ueAppend UEEmp g2 = g2 
ueAppend (UEBind x t g1) g2 = UEBind x t (ueAppend g1 g2)

{-@ uhastype :: g:Env -> e:Expr -> t:Type 
             -> Prop (HasType g e t)
             -> Prop (HasTypeF (uenv g) e (utype t)) @-}
uhastype :: Env -> Expr -> Type -> HasType -> HasTypeF
uhastype = undefined 

{-@ substitution :: g1:UEnv -> g2:UEnv -> x:Var -> ex:Expr -> tx:FType -> e:Expr -> t:FType 
             -> Prop (HasTypeF g2 ex tx)
             -> Prop (HasTypeF (ueAppend g1 (UEBind x tx g2)) e t)
             -> Prop (HasTypeF (ueAppend g1 g2) (Substitutions.Expressions.subst e x ex) t) @-}
substitution :: UEnv -> UEnv -> Var -> Expr -> FType -> Expr -> FType -> HasTypeF -> HasTypeF -> HasTypeF 
substitution = undefined 

{-@ uenvAppend :: g1:Env -> g2:Env -> {uenv (eAppend g1 g2) == ueAppend (uenv g1) (uenv g2)} @-}
uenvAppend :: Env -> Env -> () 
uenvAppend = undefined 

{-@ uenvSubst :: g:Env -> x:Var -> ex:Expr -> {uenv g == uenv (Substitutions.Environment.subst g x ex)} @-}
uenvSubst :: Env -> Var -> Expr -> () 
uenvSubst = undefined  