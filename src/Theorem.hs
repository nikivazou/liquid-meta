{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
module Theorem where 

import Syntax 
import Propositions
import Expressions 
import Environments
import Types 
import Constants 
import Substitutions 

import Lemmata.ValuesDontStep
import Lemmata.Substitution
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
progress (EApp e ex) _ (TApp _ _ _ t tx e_hastype_txt ex_hastype_tx)
  = Right (progressApp e ex t tx e_hastype_txt ex_hastype_tx)  
progress _ _ (TLam _ _ _ _ _ _)
  = Left () 
progress _ _ (TVar _ _ _ )
  = error "impossible" 
progress _ _ (TCon _ _)
  = Left () 

{-@ progressApp :: e:Expr -> ex:Expr -> t:Type -> tx:Type 
                -> ht1: Prop (HasType EEmp e (TFun tx t)) 
                -> ht2: Prop (HasType EEmp ex tx) 
                -> (Expr, Step)<{\e' p -> prop p = Step (EApp e ex) e'}> 
                /  [hasTypeSize ht1 + hasTypeSize ht2 ] @-}
progressApp :: Expr -> Expr -> Type -> Type -> HasType -> HasType -> (Expr,Step) 
progressApp e ex t tx e_hastype_txt ex_hastype_tx 
  = case progress e (TFun tx t) e_hastype_txt of 
      Left _ -> case progress ex tx ex_hastype_tx of 
                 Left _ -> case canonicalForm tx t e e_hastype_txt of 
                             Left (x,ee) -> (subst ee x ex, SAppEL x ee ex)  
                             Right p     -> (delta p ex, SAppEP p ex)  
                 Right (ex', ex_step_ex') -> (EApp e ex', SAppPR e ex ex' ex_step_ex') 
      Right (e',e_step_e') -> (EApp e' ex, SAppPL e e' ex e_step_e')   


{-@ canonicalForm :: tx:Type -> t:Type -> v:{Expr | isValue v } 
                  -> Prop (HasType EEmp v (TFun tx t)) 
                  -> Either ((Var, Expr)<{\x e -> v == ELam x e}>) {p:EPrim | v == EPrim p } @-}
canonicalForm :: Type -> Type -> Expr -> HasType -> Either (Var,Expr) EPrim
canonicalForm _ _ (ELam x e) _ = Left (x,e)
canonicalForm _ _ (EPrim c)  _ = Right c 
canonicalForm _ _ _ _ = error ""

preservation :: Expr -> Type -> HasType -> Expr -> Step -> HasType 
{-@ preservation :: e:Expr -> t:Type -> hs:Prop (HasType EEmp e t) 
                 -> e':Expr -> Prop (Step e e') 
                 -> Prop (HasType EEmp e' t) 
                 /  [hasTypeSize hs] @-}
preservation e t (TCon _ _) e' e_step_e' 
  = values_dont_step e e' e_step_e'
preservation e t (TLam _ _ _ _ _ _) e' e_step_e' 
  = values_dont_step e e' e_step_e'
preservation (EVar x) t (TVar _ _ _) e' e_step_e' 
  = error "empty-environment" 
preservation (EApp e ex) t (TApp EEmp _e _ex _t tx e_hastype_txt ex_hastype_tx) e' e_step_e' 
  = preservationApp e ex t tx e_hastype_txt ex_hastype_tx e' e_step_e'


{-@ preservationApp :: e:Expr -> ex:Expr -> t:Type -> tx:Type 
                    -> ht1:Prop (HasType EEmp e (TFun tx t)) 
                    -> ht2:Prop (HasType EEmp ex tx) 
                    -> e':Expr 
                    -> Prop (Step (EApp e ex) e') 
                    -> Prop (HasType EEmp e' t) 
                    /  [hasTypeSize ht1 + hasTypeSize ht2 ] @-}
preservationApp :: Expr -> Expr -> Type -> Type -> HasType -> HasType -> Expr -> Step -> HasType
preservationApp e ex t tx e_hastype ex_hastype _ (SAppPL _e e' _ex e_step_e')
  = TApp EEmp e' ex t tx (preservation e (TFun tx t) e_hastype e' e_step_e') ex_hastype 
preservationApp e ex t tx e_hastype ex_hastype e' (SAppPR _ _ ex' ex_step_ex')
  = TApp EEmp e ex' t tx e_hastype (preservation ex tx ex_hastype ex' ex_step_ex') 
preservationApp _ _ t tx e_hastype ex_hastype e' (SAppEL x e ex)
  = case e_hastype of 
      TLam _ _ _ _ _ e_hastype'  -> 
        substitution_lemma EEmp EEmp x ex tx e t ex_hastype e_hastype'
preservationApp _ _ t tx e_hastype ex_hastype e' (SAppEP p ex)
  = case e_hastype of 
      TCon _ _  -> primAss tx t p ex EEmp ex_hastype


