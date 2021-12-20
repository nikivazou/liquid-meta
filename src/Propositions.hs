{-# LANGUAGE GADTs #-}
{-@ LIQUID "--reflection" @-}
module Propositions where

import Syntax 
import Environments
import Types 
import Constants
import Substitutions 

{-@ type Prop E = {propBind:_ | prop propBind = E } @-}
{-@ measure prop :: a -> Proposition @-}

{-@ assertProp :: p:Proposition  -> Prop p -> () @-}
assertProp :: Proposition -> a -> () 
assertProp _ _ = ()

data Proposition 
  = HasType Env Expr Type 
  | Step    Expr Expr 
  | Evals   Expr Expr 

data HasType where 
     TApp :: Env -> Expr -> Expr -> Type -> Type -> HasType -> HasType -> HasType
     TLam :: Env -> Var -> Expr -> Type -> Type -> HasType -> HasType
     TVar :: Env -> Var -> Type -> HasType
     TCon :: Env -> EPrim -> HasType 

{-@ data HasType where 
     TApp :: g:Env -> e:Expr -> ex:Expr -> t:Type -> tx:Type 
            -> Prop (HasType g e (TFun tx t)) 
            -> Prop (HasType g ex tx)
            -> Prop (HasType g (EApp e ex) t) 
     TLam  :: g:Env -> x:Var -> e:Expr -> tx:Type -> t:Type 
            -> Prop (HasType (EBind x tx g) e t) 
            -> Prop (HasType g (ELam x e) (TFun tx t)) 
     TVar  :: g:Env -> x:Var -> t:{Type | inEnv x t g}
           -> Prop (HasType g (EVar x) t)
     TCon :: g:Env -> p:EPrim
           -> Prop (HasType g (EPrim p) (Types.primType p))
 @-}

hasTypeSize :: HasType -> Int  
{-@ hasTypeSize :: HasType -> {v:Int | 0 < v } @-}
{-@ measure hasTypeSize @-}
hasTypeSize (TCon _ _)               = 1 
hasTypeSize (TVar _ _ _)             = 1 
hasTypeSize (TLam _ _ _ _ _ ht)      = hasTypeSize ht + 1 
hasTypeSize (TApp _ _ _ _ _ ht1 ht2) = hasTypeSize ht1 + hasTypeSize ht2 + 1 


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
  SAppPR :: e1:Expr -> e2:Expr -> e2':Expr 
         -> Prop (Step e2 e2')
         -> Prop (Step (EApp e1 e2) (EApp e1 e2')) 
  SAppEL :: x:Var -> e:Expr -> ex:Expr 
         -> Prop (Step (EApp (ELam x e) ex) (Substitutions.subst e x ex)) 
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