module Lemmata.Narrowing where 


import Syntax 
import Propositions 
import Environments


{-@ hastype :: g1:Env -> g2:Env -> x:Var -> sx:Type -> tx:Type -> t:Type -> e:Expr
              -> Prop (IsSubType g2 sx tx)
              -> Prop (HasType (eAppend g1 (EBind x tx g2)) e t) 
              -> Prop (HasType (eAppend g1 (EBind x sx g2)) e t) @-} 
hastype :: Env -> Env -> Var -> Type -> Type -> Type -> Expr -> IsSubType -> HasType -> HasType
hastype = undefined 


{-@ iswellformed :: g1:Env -> g2:Env -> x:Var -> sx:Type -> tx:Type -> t:Type
              -> Prop (IsSubType g2 sx tx)
              -> Prop (IsWellFormed (eAppend g1 (EBind x tx g2)) t) 
              -> Prop (IsWellFormed (eAppend g1 (EBind x sx g2)) t) @-} 
iswellformed :: Env -> Env -> Var -> Type -> Type -> Type -> IsSubType -> IsWellFormed -> IsWellFormed
iswellformed = undefined 



{-@ issubtype :: g1:Env -> g2:Env -> x:Var -> sx:Type -> tx:Type -> s:Type -> t:Type
              -> Prop (IsSubType g2 sx tx)
              -> Prop (IsSubType (eAppend g1 (EBind x tx g2)) s t) 
              -> Prop (IsSubType (eAppend g1 (EBind x sx g2)) s t) @-} 
issubtype :: Env -> Env -> Var -> Type -> Type -> Type -> Type -> IsSubType -> IsSubType -> IsSubType
issubtype = undefined 