module Lemmata.Substitution where 


import Syntax 
import Propositions
import Expressions 
import Environments
import Types 
import Substitutions.Expressions 
import Substitutions.Types 


{-@ expressions :: g1:Env -> g2:Env -> x:Var -> ex:Expr -> tx:Type -> e:Expr -> t:Type 
                       -> Prop (HasType (eAppend g1 g2) ex tx)
                       -> Prop (HasType (eAppend g1 (EBind x tx g2)) e t) 
                       -> Prop (HasType (eAppend g1 g2) (Substitutions.Expressions.subst e x ex) (TEx x tx t)) @-}
expressions :: Env -> Env -> Var -> Expr -> Type -> Expr -> Type -> HasType -> HasType -> HasType 
expressions = undefined 



{-@ types :: g1:Env -> g2:Env -> x:Var -> ex:Expr -> tx:Type -> s:Type -> t:Type 
                       -> Prop (HasType (eAppend g1 g2) ex tx)
                       -> Prop (IsSubType (eAppend g1 (EBind x tx g2)) s t) 
                       -> Prop (IsSubType (eAppend g1 g2) (Substitutions.Types.subst s x ex) (Substitutions.Types.subst t x ex)) @-}
types :: Env -> Env -> Var -> Expr -> Type -> Type -> Type -> HasType -> IsSubType -> IsSubType 
types = undefined 