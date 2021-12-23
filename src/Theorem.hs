{-@ LIQUID "--reflection"        @-}
{-@ LIQUID "--ple"               @-}
{- LIQUID "--no-termination"    @-}
{-@ LIQUID "--max-case-expand=5" @-}
module Theorem where 

import Syntax 
import Propositions
import Expressions 
import Environments
import Types 
import Constants 
import Substitutions.Expressions 
import Substitutions.Types

import Helpers.ProofCombinators

import Lemmata.ValuesDontStep
import qualified Lemmata.Substitution
import Lemmata.Subtyping
import Lemmata.Narrowing
import Assumptions.Constants

soundness :: Expr -> Type -> HasType -> Expr -> Evals -> Either () (Expr, Step) 
{-@ soundness :: eo:Expr -> t:Type -> Prop (HasType EEmp eo t) 
              -> e:Expr -> Prop (Evals eo e)
              -> Either {v:() | isValue e} (Expr, Step)<{\e' p -> prop p = Step e e'}> @-}
soundness eo t eo_has_t e eo_evals_e = case eo_evals_e of 
    ERefl _ -> progress eo t eo_has_t 
    EStep _eo e1 eo_step_e1 _e e1_eval_e -> 
        soundness e1 t (preservation eo t eo_has_t e1 eo_step_e1) e e1_eval_e


progress :: Expr -> Type -> HasType -> Either () (Expr, Step)  
{-@ progress :: e:Expr -> t:Type -> ht:Prop (HasType EEmp e t) 
                 -> Either {v:() | isValue e} (Expr, Step)<{\e' p -> prop p = Step e e'}> 
                 / [hasTypeSize ht] @-}
progress (EApp e ex) _ (TApp _ _ _ t x tx e_hastype_txt ex_hastype_tx)
  = Right (progressApp e ex t x tx e_hastype_txt ex_hastype_tx)  
progress _ _ (TLam _ _ _ _ _ _)
  = Left () 
progress _ _ (TVar _ _ _ )
  = error "impossible" 
progress _ _ (TCon _ _)
  = Left () 
progress e _ (TSub _ _ s _ e_hastype_s _)
  = progress e s e_hastype_s  

{-@ progressApp :: e:Expr -> ex:Expr -> t:Type -> x:Var -> tx:Type 
                -> ht1: Prop (HasType EEmp e (TFun x tx t)) 
                -> ht2: Prop (HasType EEmp ex tx) 
                -> (Expr, Step)<{\e' p -> prop p = Step (EApp e ex) e'}> 
                /  [hasTypeSize ht1 + hasTypeSize ht2 ] @-}
progressApp :: Expr -> Expr -> Type -> Var -> Type -> HasType -> HasType -> (Expr,Step) 
progressApp e ex t x tx e_hastype_txt ex_hastype_tx 
  = case progress e (TFun x tx t) e_hastype_txt of 
      Left _ -> case progress ex tx ex_hastype_tx of 
                 Left _ -> case canonicalForm x tx t e e_hastype_txt of 
                             Left (x,ee) -> (Substitutions.Expressions.subst ee x ex, SAppEL x ee ex)  
                             Right p     -> (delta p ex, SAppEP p ex)  
                 Right (ex', ex_step_ex') -> (EApp e ex', SAppPR e ex ex' ex_step_ex') 
      Right (e',e_step_e') -> (EApp e' ex, SAppPL e e' ex e_step_e')   


{-@ canonicalForm :: x:Var -> tx:Type -> t:Type -> v:{Expr | isValue v } 
                  -> Prop (HasType EEmp v (TFun x tx t)) 
                  -> Either ((Var, Expr)<{\x e -> v == ELam x e}>) {p:EPrim | v == EPrim p } @-}
canonicalForm :: Var -> Type -> Type -> Expr -> HasType -> Either (Var,Expr) EPrim
canonicalForm _ _ _ (ELam x e) _ = Left (x,e)
canonicalForm _ _ _ (EPrim c)  _ = Right c 
canonicalForm _ _ _ _ _ = error ""

preservation :: Expr -> Type -> HasType -> Expr -> Step -> HasType 
{-@ preservation :: e:Expr -> t:Type -> hs:Prop (HasType EEmp e t) 
                 -> e':Expr -> Prop (Step e e') 
                 -> Prop (HasType EEmp e' t) 
                 /  [hasTypeSize hs] @-}
preservation e t (TSub _ _ s _ e_hastype_s s_issub_t) e' e_step_e' 
  = TSub EEmp e' s t (preservation e s e_hastype_s e' e_step_e') s_issub_t 
preservation e t (TCon _ _) e' e_step_e' 
  = values_dont_step e e' e_step_e'
preservation e t (TLam _ _ _ _ _ _) e' e_step_e' 
  = values_dont_step e e' e_step_e'
preservation (EVar x) t (TVar _ _ _) e' e_step_e' 
  = error "empty-environment" 
preservation (EApp e ex) (TEx _ _ t) (TApp EEmp _e _ex _t x tx e_hastype_txt ex_hastype_tx) e' e_step_e' 
  = preservationApp e ex t x tx e_hastype_txt ex_hastype_tx e' e_step_e'

{-@ preservationApp :: e:Expr -> ex:Expr -> t:Type -> x:Var -> tx:Type 
                    -> ht1:Prop (HasType EEmp e (TFun x tx t)) 
                    -> ht2:Prop (HasType EEmp ex tx) 
                    -> e':Expr 
                    -> Prop (Step (EApp e ex) e') 
                    -> Prop (HasType EEmp e' (TEx x tx t)) 
                    /  [hasTypeSize ht1 + hasTypeSize ht2 ] @-}
preservationApp :: Expr -> Expr -> Type -> Var -> Type -> HasType -> HasType -> Expr -> Step -> HasType
preservationApp e ex t x tx e_hastype ex_hastype _ (SAppPL _e e' _ex e_step_e')
  = TApp EEmp e' ex t x tx (preservation e (TFun x tx t) e_hastype e' e_step_e') ex_hastype 
preservationApp e ex t x tx e_hastype ex_hastype e' (SAppPR _ _ ex' ex_step_ex')
  = TApp EEmp e ex' t x tx e_hastype (preservation ex tx ex_hastype ex' ex_step_ex') 
preservationApp e@(ELam y ee){-(ELam x e)-} _ex t x tx e_hastype ex_hastype e' step@(SAppEL _x _ee ex) | x == y 
  = Lemmata.Substitution.expressions EEmp EEmp x ex tx ee t ex_hastype (
     inverseLam EEmp x ee tx t e_hastype)
preservationApp e@(ELam y ee){-(ELam x e)-} _ex t x tx e_hastype ex_hastype e' step@(SAppEL _x _ee ex)  =  inverseLam' EEmp y x ee tx t e_hastype ? error ""

preservationApp _ _ t x tx e_hastype ex_hastype e' (SAppEP p ex)
  = case inverseCon EEmp p (TFun x tx t) e_hastype of 
--       TCon _ _  -> primAss x tx t p ex EEmp ex_hastype
      SFun _g x sx _tx s _t tx_issub_sx s_issub_t
        -> exLemma x ex e' tx s t ex_hastype s_issub_t (
            assertProp (HasType EEmp e' (Substitutions.Types.subst s x ex)) (
              primAss x sx s p ex EEmp ( -- primtType p == TFun x sx s 
                assertProp (HasType EEmp ex sx) (TSub EEmp ex tx sx ex_hastype tx_issub_sx)
              )
            )
        )   

{-@ exLemma ::  x:Var -> ex:Expr -> e:Expr -> tx:Type -> s:Type -> t:Type 
             -> Prop (HasType EEmp ex tx)
             -> Prop (IsSubType (EBind x tx EEmp) s t)
             -> Prop (HasType EEmp e (Substitutions.Types.subst s x ex))
             -> Prop (HasType EEmp e (TEx x tx t)) @-}
exLemma :: Var -> Expr -> Expr -> Type -> Type -> Type -> HasType -> IsSubType -> HasType  -> HasType
exLemma x ex e tx s t ex_hastype_tx s_issub_t e_hastype_s 
  = assertProp (HasType EEmp e (TEx x tx t)) (
      TSub EEmp e (Substitutions.Types.subst s x ex) (TEx x tx t) e_hastype_s (
       assertProp (IsSubType EEmp (Substitutions.Types.subst s x ex) (TEx x tx t)) (
         SWit EEmp x tx ex (Substitutions.Types.subst s x ex) t ex_hastype_tx (
           Lemmata.Substitution.types EEmp EEmp x ex tx s t ex_hastype_tx s_issub_t
         )  
       )
     )
      )


{-@ inverseCon :: g:Env -> p:EPrim -> t:Type 
               -> Prop (HasType g (EPrim p) t) 
               -> Prop (IsSubType g (primType p) t ) @-}
inverseCon :: Env -> EPrim -> Type -> HasType -> IsSubType
inverseCon g p t (TCon _ _ ) = subtypeId g t 
inverseCon g p t (TSub _ _ s _t p_hastype_s s_subtype_t) 
  = subtypeTrans g (primType p) s t (inverseCon g p s p_hastype_s) s_subtype_t  




{-@ inverseLam' :: g:Env -> y:Var -> x:Var -> e:Expr -> tx:Type -> t:Type 
           -> Prop (HasType g (ELam y e) (TFun x tx t))
           -> {  x == y} @-}
inverseLam' :: Env -> Var -> Var -> Expr -> Type -> Type -> HasType -> () 
inverseLam' g y x e tx t (TLam _ _ _ _ _ _) = () 
inverseLam' g y x e tx t (TSub _ _ _ _ e_hastype_s (SFun _ _ sx _ s _ _ _)) = 
  inverseLam' g y x e sx s e_hastype_s  

{-@ inverseLam :: g:Env -> x:Var -> e:Expr -> tx:Type -> t:Type 
           -> ht:Prop (HasType g (ELam x e) (TFun x tx t))
           -> Prop (HasType (EBind x tx g) e t) / [hasTypeSize ht] @-}
inverseLam :: Env -> Var -> Expr -> Type -> Type -> HasType -> HasType 
inverseLam g x e tx t (TLam _g _x _e _tx _t e_hastype_t) 
  = e_hastype_t
inverseLam g _x e tx t (TSub _ _e ss _ e_hastype_s (
      SFun _g x sx _tx s _t tx_issub_sx s_issub_t
  ))
  = TSub (EBind x tx g) e s t (
      assertProp (HasType (EBind x tx g) e s) (
        narrowing EEmp g x tx sx s e tx_issub_sx (
          assertProp (HasType (EBind x sx g) e s)
           (inverseLam g x e sx s 
           (assertProp (HasType g (ELam x e) (TFun x sx s)) e_hastype_s)
           )
        )
      )) s_issub_t
    

