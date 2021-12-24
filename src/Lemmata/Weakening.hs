module Lemmata.Weakening where 

import Syntax 
import Propositions 
import Environments


{-@ weakening :: g1:Env -> g2:Env -> x:Var -> tx:Type -> s:Type -> t:Type
              -> Prop (IsSubType (eAppend g1 g2) s t)
              -> Prop (IsSubType (eAppend g1 (EBind x tx g2)) s t) @-} 
weakening :: Env -> Env -> Var -> Type -> Type -> Type -> IsSubType -> IsSubType
weakening = undefined 