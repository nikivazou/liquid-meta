{-# LANGUAGE GADTs #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--no-termination" @-}
module Propositions where

import Syntax 
import Environments
import Substitutions.Expressions 
import Substitutions.Types 
import Types 
import Expressions 
import Constants

{-@ type Prop E = {propBind:_ | prop propBind = E } @-}
{-@ measure prop :: a -> Proposition @-}

{-@ assertProp :: p:Proposition  -> Prop p -> Prop p @-}
assertProp :: Proposition -> a -> a 
assertProp _ x = x 

{-@ assume assumeProp :: p:Proposition  -> Prop p @-}
assumeProp :: Proposition -> a  
assumeProp _ = undefined 


data Proposition 
  = HasType   Env Expr Type 
  | IsSubType Env Type Type 
  | Step      Expr Expr 
  | Evals     Expr Expr 

data HasType where 
     TApp :: Env -> Expr -> Expr -> Type -> Var -> Type -> HasType -> HasType -> HasType
     TLam :: Env -> Var -> Expr -> Type -> Type -> HasType -> HasType
     TVar :: Env -> Var -> Type -> HasType
     TCon :: Env -> EPrim -> HasType 
     TSub :: Env -> Expr -> Type -> Type -> HasType -> IsSubType -> HasType 

{-@ data HasType where 
     TApp :: g:Env -> e:Expr -> ex:Expr -> t:Type -> x:Var -> tx:Type 
            -> Prop (HasType g e (TFun x tx t)) 
            -> Prop (HasType g ex tx)
            -> Prop (HasType g (EApp e ex) (TEx x tx t)) 
     TLam  :: g:Env -> x:Var -> e:Expr -> tx:Type -> t:Type 
            -> Prop (HasType (EBind x tx g) e t) 
            -> Prop (HasType g (ELam x e) (TFun x tx t)) 
     TVar  :: g:Env -> x:Var -> t:{Type | inEnv x t g}
           -> Prop (HasType g (EVar x) t)
     TCon :: g:Env -> p:EPrim
           -> Prop (HasType g (EPrim p) (primType p))
     TSub :: g:Env -> e:Expr -> s:Type -> t:Type 
          -> Prop (HasType g e s) -> Prop (IsSubType g s t)
          -> Prop (HasType g e t)
 @-}

hasTypeSize :: HasType -> Int  
{-@ hasTypeSize :: HasType -> {v:Int | 0 < v } @-}
{-@ measure hasTypeSize @-}
hasTypeSize (TCon _ _)                 = 1 
hasTypeSize (TVar _ _ _)               = 1 
hasTypeSize (TLam _ _ _ _ _ ht)        = hasTypeSize ht + 1 
hasTypeSize (TApp _ _ _ _ _ _ ht1 ht2) = hasTypeSize ht1 + hasTypeSize ht2 + 1 
hasTypeSize (TSub _ _ _ _ ht st)       = hasTypeSize ht  + isSubTypeSize st + 1 


data IsSubType where 
  SBase :: Env -> TBase -> Predicate -> Predicate -> IsSubType 
  SFun  :: Env -> Var -> Type -> Type -> Type -> Type -> IsSubType -> IsSubType -> IsSubType  
  SWit  :: Env -> Var -> Type -> Expr -> Type -> Type -> HasType -> IsSubType -> IsSubType  


{-@ data IsSubType where 
     SBase :: g:Env -> b:TBase -> p1:Predicate -> p2:Predicate 
           -> Prop (IsSubType g (TBase b p1) (TBase b p2)) 
     SFun  :: g:Env -> x:Var -> s1:Type -> s2:Type -> t1:Type -> t2:Type 
           -> Prop (IsSubType g s2 s1)
           -> Prop (IsSubType (EBind x s2 g) t1 t2)
           -> Prop (IsSubType g (TFun x s1 t1) (TFun x s2 t2)) 
     SWit  :: g:Env -> x:Var -> tx:Type -> ex:Expr -> s:Type -> t:Type 
           -> Prop (HasType g ex tx)
           -> Prop (IsSubType g s (Substitutions.Types.subst t x ex ))
           -> Prop (IsSubType g s (TEx x tx t)) 
@-}


isSubTypeSize :: IsSubType -> Int  
{-@ isSubTypeSize :: IsSubType -> {v:Int | 0 < v } @-}
{-@ measure isSubTypeSize @-}
isSubTypeSize (SBase _ _ _ _)            = 1 
isSubTypeSize (SFun _ _ _ _ _ _ st1 st2) = 1 + isSubTypeSize st1 + isSubTypeSize st2  
isSubTypeSize (SWit _ _ _ _ _ _ t1 st2)  = 1 + hasTypeSize t1 + isSubTypeSize st2  


data Step where 
  SAppPL :: Expr  -> Expr -> Expr -> Step -> Step 
  SAppPR :: Expr  -> Expr -> Expr -> Step -> Step 
  SAppEL :: Var   -> Expr -> Expr -> Step 
  SAppEP :: EPrim -> Expr -> Step 
  
{-@ 
data Step where 
  SAppPL :: e1:Expr -> e1':Expr -> e2:Expr 
         -> Prop (Step e1 e1')
         -> Prop (Step (EApp e1 e2) (EApp e1' e2)) 
  SAppPR :: e1:{Expr | isValue e1 } -> e2:Expr -> e2':Expr 
         -> Prop (Step e2 e2')
         -> Prop (Step (EApp e1 e2) (EApp e1 e2')) 
  SAppEL :: x:Var -> e:Expr -> ex:Expr 
         -> Prop (Step (EApp (ELam x e) ex) (Substitutions.Expressions.subst e x ex)) 
  SAppEP :: p:EPrim -> ex:Expr 
         -> Prop (Step (EApp (EPrim p) ex) (delta p ex)) 
  @-}


data Evals where 
  ERefl :: Expr -> Evals 
  EStep :: Expr -> Expr -> Step -> Expr -> Evals -> Evals  

{-@ 
data Evals where 
  ERefl :: e:Expr -> Prop {Evals e e}
  EStep :: e1:Expr -> e2:Expr -> Prop (Step e1 e2) 
        -> e3:Expr -> Prop (Evals e2 e3) 
        -> Prop (Evals e1 e3)  
  @-}