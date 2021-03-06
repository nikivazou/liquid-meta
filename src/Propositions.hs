{-# LANGUAGE GADTs #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--no-termination" @-}
module Propositions where

import Syntax 
import Unrefine 
import Environments
import Substitutions.Expressions 
import Substitutions.Types 
import Substitutions.Environment 
import Types 
import Expressions
import Constants
import Data.Set 

{-@ type Prop E = {propBind:_ | prop propBind = E } @-}
{-@ measure prop :: a -> Proposition @-}

{-@ assertProp :: p:Proposition  -> Prop p -> Prop p @-}
assertProp :: Proposition -> a -> a 
assertProp _ x = x 


{-@ todoProp :: p:Proposition -> Proposition -> Prop p @-}
todoProp :: Proposition -> Proposition -> a 
todoProp _ _ = undefined -- SAFE undefined


{-@ assume assumeProp :: p:Proposition  -> Prop p @-}
assumeProp :: Proposition -> a
assumeProp _ = undefined -- SAFE undefined 


data Proposition 
  = HasType   Env Expr Type 
  | HasTypeF  UEnv Expr FType 
  | IsSubType Env Type Type 
  | IsWellFormed Env Type 
  | WellFormedEnv Env 
  | Implies   Env TBase Expr Expr  
  | Step      Expr Expr 
  | Evals     Expr Expr 
  | TODO


data HasTypeF where 
  FTLam :: UEnv -> Var  -> Expr -> FType -> FType -> HasTypeF -> HasTypeF 
  FTApp :: UEnv -> Expr -> Expr -> FType -> FType -> HasTypeF -> HasTypeF -> HasTypeF 
  FTVar :: UEnv -> Var   -> HasTypeF
  FTCon :: UEnv -> EPrim -> HasTypeF

{-@ data HasTypeF where 
     FTLam :: g:UEnv -> x:{Var | not (member x (udom g))} 
           -> e:Expr -> tx:FType -> t:FType 
           -> Prop (HasTypeF (UEBind x tx g) e t) 
           -> Prop (HasTypeF g (ELam x e) (FTFun tx t)) 
     FTApp :: g:UEnv -> e:Expr -> ex:Expr -> tx:FType -> t:FType 
           -> Prop (HasTypeF g e (FTFun tx t))
           -> Prop (HasTypeF g ex tx) 
           -> Prop (HasTypeF g (EApp e ex) t) 
     FTVar :: g:UEnv -> x:Var 
           -> Prop (HasTypeF g (EVar x) (Environments.lookupUEnv g x)) 
     FTCon :: g:UEnv -> p:EPrim  
           -> Prop (HasTypeF g (EPrim p) ((primUType p))) 
@-}

data WellFormedEnv where 
  WFEEmp :: WellFormedEnv
  WFFBnd :: Env -> Var -> Type -> IsWellFormed -> WellFormedEnv -> WellFormedEnv

{-@ data WellFormedEnv where 
     WFEEmp :: Prop (WellFormedEnv EEmp)
     WFFBnd :: g:Env -> x:{Var | not (member x (dom g))} -> tx:Type 
            -> Prop (IsWellFormed g tx)
            -> Prop (WellFormedEnv g) 
            -> Prop (WellFormedEnv (EBind x tx g)) @-}

data IsWellFormed where 
  WFBs  :: Env -> TPrim -> Expr -> Var -> HasTypeF -> IsWellFormed
  WFFun :: Env -> Var -> Type -> Type -> IsWellFormed -> IsWellFormed -> IsWellFormed  
  WFEx  :: Env -> Var -> Type -> Type -> IsWellFormed -> IsWellFormed -> IsWellFormed  

{-@ data IsWellFormed where 
     WFBs  :: g:Env -> b:TPrim 
           -> p:{Expr | isSubsetOf (Expressions.freeVars p) (union (singleton pvar) (dom g))}
           -> x:{Var | not (member x (dom g)) && not (member x (freeVars p))} 
           -> Prop (HasTypeF (UEBind x (FTBase b) (Unrefine.uenv g)) (Substitutions.Expressions.subst p pvar (EVar x)) (FTBase TBool) )
           -> Prop (IsWellFormed g (TBase (TPrim b) (Predicate pvar p)))
     WFFun :: g:Env -> x:{Var | not (member x (dom g))} -> tx:Type -> t:Type 
           -> Prop (IsWellFormed g tx)
           -> Prop (IsWellFormed (EBind x tx g) t)
           -> Prop (IsWellFormed g (TFun x tx t)) 
     WFEx  :: g:Env -> x:{Var | not (member x (dom g))} -> tx:Type -> t:Type 
           -> Prop (IsWellFormed g tx)
           -> Prop (IsWellFormed (EBind x tx g) t)
           -> Prop (IsWellFormed g (TEx x tx t)) 
  @-}

isWellFormedSize :: IsWellFormed -> Int  
{-@ isWellFormedSize :: IsWellFormed -> {v:Int | 0 < v } @-}
{-@ measure isWellFormedSize @-}
isWellFormedSize (WFBs  _ _ _ _ _)       = 1 
isWellFormedSize (WFFun _ _ _ _ wf1 wf2) = 1 + isWellFormedSize wf1 + isWellFormedSize wf2  
isWellFormedSize (WFEx  _ _ _ _ wf1 wf2) = 1 + isWellFormedSize wf1 + isWellFormedSize wf2  

data HasType where 
     TApp :: Env -> Expr -> Expr -> Type -> Var -> Type -> HasType -> HasType -> HasType
     TLam :: Env -> Var -> Expr -> Type -> Type -> HasType -> IsWellFormed -> HasType
     TVar :: Env -> Var ->  HasType
     TCon :: Env -> EPrim -> HasType 
     TSub :: Env -> Expr -> Type -> Type -> HasType -> IsSubType -> IsWellFormed -> HasType 

{-@ data HasType where 
     TApp :: g:Env -> e:Expr -> ex:Expr -> t:Type -> x:Var -> tx:Type 
            -> Prop (HasType g e (TFun x tx t)) 
            -> Prop (HasType g ex tx)
            -> Prop (HasType g (EApp e ex) (TEx x tx t)) 
     TLam  :: g:Env -> x:{Var | not (member x (dom g))} -> e:Expr -> tx:Type -> t:Type 
           -> Prop (HasType (EBind x tx g) e t) 
           -> Prop (IsWellFormed g tx)
           -> Prop (HasType g (ELam x e) (TFun x tx t)) 
     TVar  :: g:Env -> x:{Var | member x (dom g)} 
           -> Prop (HasType g (EVar x) (Environments.lookupEnv g x))
     TCon  :: g:Env -> p:EPrim
           -> Prop (HasType g (EPrim p) (primType p))
     TSub  :: g:Env -> e:Expr -> s:Type -> t:Type 
           -> Prop (HasType g e s) 
           -> Prop (IsSubType g s t)
           -> Prop (IsWellFormed g t)
           -> Prop (HasType g e t)
 @-}

hasTypeSize :: HasType -> Int  
{-@ hasTypeSize :: HasType -> {v:Int | 0 < v } @-}
{-@ measure hasTypeSize @-}
hasTypeSize (TCon _ _)                 = 1 
hasTypeSize (TVar _ _)                 = 1 
hasTypeSize (TLam _ _ _ _ _ ht wf)     = hasTypeSize ht + isWellFormedSize wf + 1 
hasTypeSize (TApp _ _ _ _ _ _ ht1 ht2) = hasTypeSize ht1 + hasTypeSize ht2 + 1 
hasTypeSize (TSub _ _ _ _ ht st wf)    = hasTypeSize ht  + isSubTypeSize st + isWellFormedSize wf + 1 


data IsSubType where 
  SBase :: Env -> TBase -> Expr -> Expr -> Implies -> IsSubType 
  SFun  :: Env -> Var -> Type -> Type -> Type -> Type -> IsSubType -> IsSubType -> IsSubType  
  SWit  :: Env -> Var -> Type -> Expr -> Type -> Type -> HasType -> IsSubType -> IsSubType  
  SBnd  :: Env -> Var -> Type -> Type -> Type -> IsSubType -> IsSubType  


{-@ data IsSubType where 
     SBase :: g:Env -> b:TBase -> p1:Expr -> p2:Expr 
           -> Prop (Implies g b p1 p2)
           -> Prop (IsSubType g (TBase b (Predicate pvar p1)) (TBase b (Predicate pvar p2))) 
     SFun  :: g:Env -> x:Var -> s1:Type -> s2:Type -> t1:Type -> t2:Type 
           -> Prop (IsSubType g s2 s1)
           -> Prop (IsSubType (EBind x s2 g) t1 t2)
           -> Prop (IsSubType g (TFun x s1 t1) (TFun x s2 t2)) 
     SWit  :: g:Env -> x:Var -> tx:Type -> ex:Expr -> s:Type -> t:Type 
           -> Prop (HasType g ex tx)
           -> Prop (IsSubType g s (Substitutions.Types.subst t x ex))
           -> Prop (IsSubType g s (TEx x tx t)) 
     SBnd  :: g:Env -> x:{Var | not (member x (dom g))} -> sx:Type -> s:Type 
           -> t:{Type | not (member x (Types.freeVars t))} 
           -> Prop (IsSubType (EBind x sx g) s t)
           -> Prop (IsSubType g (TEx x sx s) t) 
@-}

-- NV: LH TOFIX This is required to properly import member in the logic.... 
isMember :: Int -> Set Int -> Bool 
isMember = member 


isSubTypeSize :: IsSubType -> Int  
{-@ isSubTypeSize :: IsSubType -> {v:Int | 0 < v } @-}
{-@ measure isSubTypeSize @-}
isSubTypeSize (SBase _ _ _ _ _)          = 1 
isSubTypeSize (SFun _ _ _ _ _ _ st1 st2) = 1 + isSubTypeSize st1 + isSubTypeSize st2  
isSubTypeSize (SWit _ _ _ _ _ _ t1 st2)  = 1 + hasTypeSize t1 + isSubTypeSize st2  
isSubTypeSize (SBnd _ _ _ _ _ st)        = 1 + isSubTypeSize st  

data Implies where 
  IRefl  :: Env -> TBase -> Expr -> Implies 
  ITrans :: Env -> TBase -> Expr -> Expr -> Expr -> Implies -> Implies -> Implies
  ISubst :: Env -> Env -> TBase -> Var -> Type -> Expr -> Expr -> Expr -> HasType -> Implies -> Implies 

{-@ data Implies where 
      IRefl  :: g:Env -> b:TBase -> e:Expr -> Prop (Implies g b e e)  
      ITrans :: g:Env -> b:TBase -> e1:Expr -> e2:Expr -> e3:Expr
             -> Prop (Implies g b e1 e2)  
             -> Prop (Implies g b e2 e3)  
             -> Prop (Implies g b e1 e3)
      ISubst :: g1:Env -> g2:Env -> b:TBase
             -> x:{Var | not (member x (union (dom g1) (dom g2)))} 
             -> tx:Type -> ex:Expr -> p1:Expr -> p2:Expr 
             -> Prop (HasType g2 ex tx)
             -> Prop (Implies (Environments.eAppend g1 (EBind x tx g2)) b p1 p2)
             -> Prop (Implies 
                       (Environments.eAppend (Substitutions.Environment.subst g1 x ex) g2)
                       b  
                       (Substitutions.Expressions.subst p1 x ex) 
                       (Substitutions.Expressions.subst p2 x ex))  
  @-}


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