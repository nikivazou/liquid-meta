module Lemmata.Subtyping where 

import Syntax 
import Propositions

subtypeId :: Env -> Type -> IsSubType
{-@ subtypeId :: g:Env -> t:Type -> Prop (IsSubType g t t) @-}
subtypeId  = undefined 

subtypeTrans :: Env -> Type -> Type -> Type -> IsSubType -> IsSubType -> IsSubType
{-@ subtypeTrans :: g:Env -> t:Type -> w:Type -> s:Type 
              -> Prop (IsSubType g t w) 
              -> Prop (IsSubType g w s)
              -> Prop (IsSubType g t s) @-}
subtypeTrans  = undefined 