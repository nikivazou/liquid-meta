module Lemmata.Substitution where 


import Syntax 
import Propositions
import Expressions 
import Environments
import Types 
import Substitutions 


{-@ substitution_lemma :: g1:Env -> g2:Env -> x:Var -> ex:Expr -> tx:Type -> e:Expr -> t:Type 
                       -> Prop (HasType (eAppend g1 g2) ex tx)
                       -> Prop (HasType (eAppend g1 (EBind x tx g2)) e t) 
                       -> Prop (HasType (eAppend g1 g2) (Substitutions.subst e x ex) t) @-}
substitution_lemma :: Env -> Env -> Var -> Expr -> Type -> Expr -> Type -> HasType -> HasType -> HasType 
substitution_lemma = undefined 