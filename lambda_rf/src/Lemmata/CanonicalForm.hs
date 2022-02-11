{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{-@ LIQUID "--max-case-expand=5" @-}
module Lemmata.CanonicalForm (lam) where 

import Syntax
import Expressions
import Environments
import Propositions
import Unrefine
import Lemmata.Unrefine 


{-@ lam :: x:Var -> tx:Type -> t:Type -> v:{Expr | isValue v } 
        -> Prop (HasType EEmp v (TFun x tx t)) 
        -> Either ((Var, Expr)<{\xx e -> v == ELam xx e}>) {p:EPrim | v == EPrim p } @-}
lam :: Var -> Type -> Type -> Expr -> HasType -> Either (Var,Expr) EPrim
lam x tx t v v_hastype 
  = ulam (utype tx) (utype t) v (unrefine EEmp v (TFun x tx t) v_hastype)


{-@ ulam :: tx:FType -> t:FType -> v:{Expr | isValue v } 
        -> Prop (HasTypeF UEEmp v (FTFun tx t)) 
        -> Either ((Var, Expr)<{\xx e -> v == ELam xx e}>) {p:EPrim | v == EPrim p } @-}
ulam :: FType -> FType -> Expr -> HasTypeF -> Either (Var,Expr) EPrim
ulam _ _ _ (FTLam _ x e tx t _)  = Left (x,e)
ulam _ _ _ (FTApp _ _ _ _ _ _ _) = error "not value"
ulam _ _ _ (FTVar _ _)           = error "empty env"
ulam _ _ _ (FTCon _ p)           = Right p

