module Lemmata.Narrowing.HasType where 

import Syntax 
import Propositions 
import Environments


{-@ narrowing :: g1:Env -> g2:Env -> x:Var -> sx:Type -> tx:Type -> t:Type -> e:Expr
              -> Prop (IsSubType g2 sx tx)
              -> Prop (HasType (eAppend g1 (EBind x tx g2)) e t) 
              -> Prop (HasType (eAppend g1 (EBind x sx g2)) e t) @-} 
narrowing :: Env -> Env -> Var -> Type -> Type -> Type -> Expr -> IsSubType -> HasType -> HasType
narrowing = undefined 