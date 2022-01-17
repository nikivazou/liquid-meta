{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"               @-}
{-@ LIQUID "--max-case-expand=5" @-}
{- LIQUID "--no-termination" @-}

module Lemmata.Inversion where 

import Syntax 
import Environments
import Propositions
import Constants
import Unrefine
import Substitutions.Expressions
import Substitutions.Types 

import WellFormed 
import qualified Lemmata.Narrowing (hastype)
import Lemmata.Subtyping 
import Assumptions.Constants 


{-@ prim :: g:Env -> p:EPrim -> t:Type  
               -> Prop (WellFormedEnv g)
               -> Prop (HasType g (EPrim p) t) 
               -> Prop (IsSubType g (primType p) t ) @-}
prim :: Env -> EPrim -> Type -> WellFormedEnv -> HasType -> IsSubType
prim g p t g_wf ht@(TCon _ _ ) = subtypeId g t (typed g (EPrim p) t g_wf ht) 
prim g p _ g_wf (TSub _ _ s t p_hastype_s s_subtype_t t_wf) 
  = subtypeTrans g (primType p) s t g_wf 
       (primWellFormed g p g_wf)
       (typed g (EPrim p) s g_wf p_hastype_s)
       t_wf
       (prim g p s g_wf p_hastype_s) s_subtype_t  


{-@ lam :: g:Env -> x:Var -> e:Expr -> tx:Type -> t:Type 
        -> Prop (WellFormedEnv g)
        -> Prop (HasType g (ELam x e) (TFun x tx t))
        -> Prop (HasType (EBind x tx g) e t) 
         @-}
lam :: Env -> Var -> Expr -> Type -> Type -> WellFormedEnv -> HasType -> HasType 
lam g x e tx t g_wf ht 
  = lamNoSBind g x e tx t g_wf (collapseSub g (ELam x e) (TFun x tx t) g_wf ht)

{-@ lamSameName :: g:Env -> y:Var -> x:Var -> e:Expr -> tx:Type -> t:Type 
        -> Prop (WellFormedEnv g)
        -> Prop (HasType g (ELam y e) (TFun x tx t))
        -> {x == y} 
         @-}
lamSameName :: Env -> Var -> Var -> Expr -> Type -> Type -> WellFormedEnv -> HasType -> () 
lamSameName g y x e tx t g_wf ht 
  = lamNoSBindSameName g y x e tx t g_wf (collapseSub g (ELam y e) (TFun x tx t) g_wf ht)


{-@ lamNoSBindSameName :: g:Env -> y:Var -> x:Var -> e:Expr -> tx:Type -> t:Type 
        -> Prop (WellFormedEnv g)
        -> {p:HasType | prop p = HasType g (ELam y e) (TFun x tx t) && signleSub p }
        -> {x == y} 
         @-}
lamNoSBindSameName :: Env -> Var -> Var -> Expr -> Type -> Type -> WellFormedEnv -> HasType -> () 
lamNoSBindSameName g y x e tx t g_wf (TLam _ _ _ _ _ _ _) = () 
lamNoSBindSameName g y x e tx t g_wf (TSub _ _ _ _ e_hastype_s sub _) 
  = case e_hastype_s of
     TLam _ _ _ _ _ _ _ -> 
       case sub of  
          SFun _ _ sx _ s _ _ _ -> lamNoSBindSameName g y x e sx s g_wf e_hastype_s
lamNoSBindSameName g y x e tx t g_wf _ = error "" 




{-@ lamNoSBind :: g:Env -> x:Var -> e:Expr -> tx:Type -> t:Type 
        -> Prop (WellFormedEnv g)
        -> {p:HasType | prop p ==  HasType g (ELam x e) (TFun x tx t) && signleSub p}
        -> Prop (HasType (EBind x tx g) e t) 
         @-}
lamNoSBind :: Env -> Var -> Expr -> Type -> Type -> WellFormedEnv -> HasType -> HasType 
lamNoSBind _ _ _ _ _ _ (TLam _ _ _ _ _ e_hastype_t _) = e_hastype_t 
lamNoSBind _ x e tx t g_wf ht@(TSub g ee s txt hastype s_issub_t txt_wf) 
  = case s_issub_t of 
      SFun _ _ sx tx s t tx_issub_sx s_issub_t -> 
        case txt_wf of 
          WFFun _ _ _ _ _ t_wf ->
            TSub (EBind x tx g) e s t  
              (Lemmata.Narrowing.hastype EEmp g x tx sx s e tx_issub_sx 
                (lamNoSBind g x e sx s g_wf hastype)
              )
              s_issub_t t_wf 
      SBnd _ _ _ _ _ _ -> 
          case hastype of 
              TLam _ _ _ _ _ _ _ -> error "Cannot Happen"
              TSub _ _ _ _ _ _ _ -> error "Cannot Happen"
      _ -> error "Cannot Happen" 
lamNoSBind _ _ _ _ _ _ _
  = error "Cannot Happen"


{-@ collapseSub :: g:Env -> e:Expr -> t:Type 
                -> Prop (WellFormedEnv g)
                -> ht:Prop (HasType g e t)
                -> {p:HasType | prop p == HasType g e t && signleSub p} 
                /  [subCount ht] @-}
collapseSub :: Env -> Expr -> Type -> WellFormedEnv -> HasType -> HasType 
collapseSub g e t g_wf (TSub _ _ s _ (TSub _ _ w _ e_hastype_w w_issub_s s_wf) s_issub_t t_wf)
  = collapseSub g e t g_wf 
      (TSub g e w t 
         e_hastype_w
         (subtypeTrans g w s t g_wf (typed g e w g_wf e_hastype_w) s_wf t_wf w_issub_s s_issub_t) 
         t_wf)
collapseSub _ _ _ _ ht = ht 

{-@ measure subCount @-}
subCount :: HasType -> Int 
{-@ subCount :: HasType -> Nat @-} 
subCount (TSub _ _ _ _ ht _ _) = 1 + subCount ht   
subCount _ = 0 

{-@ measure signleSub @-}
signleSub :: HasType -> Bool 
signleSub (TSub _ _ _ _ ht _ _) = noSub ht && signleSub ht  
signleSub _ = True 


{-@ measure noSub @-}
noSub :: HasType -> Bool 
noSub (TSub _ _ _ _ ht sub _) = False 
noSub _ = True 
