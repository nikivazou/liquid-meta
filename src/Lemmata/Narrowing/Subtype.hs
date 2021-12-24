module Lemmata.Narrowing.Subtype where 

import Syntax 
import Propositions 
import Environments


{-@ narrowing :: g1:Env -> g2:Env -> x:Var -> sx:Type -> tx:Type -> s:Type -> t:Type
              -> Prop (IsSubType g2 sx tx)
              -> Prop (IsSubType (eAppend g1 (EBind x tx g2)) s t) 
              -> Prop (IsSubType (eAppend g1 (EBind x sx g2)) s t) @-} 
narrowing :: Env -> Env -> Var -> Type -> Type -> Type -> Type -> IsSubType -> IsSubType -> IsSubType
narrowing = undefined 