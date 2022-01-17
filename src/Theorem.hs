{-@ LIQUID "--reflection"        @-}
{-@ LIQUID "--ple"               @-}
{-@ LIQUID "--max-case-expand=5" @-}
module Theorem where 

import Syntax 
import Propositions
import Expressions 
import Environments
import Types 
import Unrefine
import Constants 
import Substitutions.Expressions 
import Substitutions.Environment 
import Substitutions.Types

import Helpers.ProofCombinators

import WellFormed (wellformedTFunArg, wellformedTFunRes)
import Lemmata.ValuesDontStep
import Lemmata.CanonicalForm
import Lemmata.WellFormedTyped (typed)
import qualified Lemmata.Substitution
import qualified Lemmata.Inversion
import Lemmata.Subtyping
import qualified Lemmata.Narrowing
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
progress _ _ (TLam _ _ _ _ _ _ _)
  = Left () 
progress _ _ (TVar _ _)
  = error "impossible" 
progress _ _ (TCon _ _)
  = Left () 
progress e _ (TSub _ _ s _ e_hastype_s _ _)
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
                 Left _ -> case Lemmata.CanonicalForm.lam x tx t e e_hastype_txt of 
                             Left (x,ee) -> (Substitutions.Expressions.subst ee x ex, SAppEL x ee ex)  
                             Right p     -> (delta p ex, SAppEP p ex)  
                 Right (ex', ex_step_ex') -> (EApp e ex', SAppPR e ex ex' ex_step_ex') 
      Right (e',e_step_e') -> (EApp e' ex, SAppPL e e' ex e_step_e')   




preservation :: Expr -> Type -> HasType -> Expr -> Step -> HasType 
{-@ preservation :: e:Expr -> t:Type -> hs:Prop (HasType EEmp e t) 
                 -> e':Expr -> Prop (Step e e') 
                 -> Prop (HasType EEmp e' t) 
                 /  [hasTypeSize hs] @-}
preservation e t p@(TSub _ _ s _ e_hastype_s s_issub_t _) e' e_step_e' 
  = TSub EEmp e' s t (preservation e s e_hastype_s e' e_step_e') s_issub_t 
         (typed EEmp e t WFEEmp p)
preservation e t (TCon _ _) e' e_step_e' 
  = values_dont_step e e' e_step_e'
preservation e t (TLam _ _ _ _ _ _ _) e' e_step_e' 
  = values_dont_step e e' e_step_e'
preservation (EVar x) t (TVar _ _) e' e_step_e' 
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
  = TSub EEmp e' t' tex (
    assertProp (HasType EEmp e' t') (
      Lemmata.Substitution.expressions EEmp EEmp x ex tx ee t 
        -- (wf_emp (EBind x tx EEmp) xtx_wf)
        xtx_wf
        ex_hastype 
        (Lemmata.Inversion.lam EEmp x ee tx t WFEEmp e_hastype)
    )
  ) (assertProp (IsSubType EEmp t' tex) (
    SWit EEmp x tx ex t' t ex_hastype (subtypeId EEmp t' tt_wf)
  )) tex_wf
   where 
     e' = Substitutions.Expressions.subst ee x ex
     t' = Substitutions.Types.subst t x ex 
     tex = TEx x tx t 
     tx_wf  = assertProp (IsWellFormed EEmp tx) (typed EEmp ex tx WFEEmp ex_hastype) 
     t_wf   = assertProp (IsWellFormed (EBind x tx EEmp) t) (
                 wellformedTFunRes EEmp x tx t (typed EEmp e (TFun x tx t) WFEEmp e_hastype)
                 ) 
     xtx_wf = assertProp (WellFormedEnv (EBind x tx EEmp)) (WFFBnd EEmp x tx tx_wf WFEEmp) 
     tt_wf  = assertProp (IsWellFormed EEmp t') (Lemmata.Substitution.wellformedness EEmp EEmp x ex tx t xtx_wf ex_hastype t_wf) 
     tex_wf = assertProp (IsWellFormed EEmp tex) (WFEx EEmp x tx t tx_wf t_wf) 
preservationApp e@(ELam y ee){-(ELam x e)-} _ex t x tx e_hastype ex_hastype e' step@(SAppEL _x _ee ex)  
  = Lemmata.Inversion.lamSameName EEmp y x ee tx t WFEEmp e_hastype ? error ""

preservationApp e _ t x tx e_hastype ex_hastype e' (SAppEP p ex)
  = case Lemmata.Inversion.prim EEmp p (TFun x tx t) WFEEmp e_hastype of 
      SFun _g x sx _tx s _t tx_issub_sx s_issub_t
        -> exLemma x ex e' tx s t ex_hastype (typed EEmp e (TFun x tx t) WFEEmp e_hastype) 
            (assertProp (IsWellFormed (EBind x tx EEmp) s) (
              Lemmata.Narrowing.iswellformed EEmp EEmp x tx sx s tx_issub_sx 
                 (assertProp (IsWellFormed (EBind x sx EEmp) s) (
                   wellformedTFunRes EEmp x sx s (primWellFormed EEmp p WFEEmp)
                 ))
            ) )
             s_issub_t (
            assertProp (HasType EEmp e' (Substitutions.Types.subst s x ex)) (
              primAss x sx s p ex EEmp ( -- primtType p == TFun x sx s 
                assertProp (HasType EEmp ex sx) (
                  TSub EEmp ex tx sx ex_hastype tx_issub_sx 
                   (assertProp (IsWellFormed EEmp sx) (
                     wellformedTFunArg EEmp x sx s (primWellFormed EEmp p WFEEmp)
                   )))
              )
            )
        )   
      _ -> noTEx p ? error "impossible"

{-@ exLemma ::  x:Var -> ex:Expr -> e:Expr -> tx:Type -> s:Type -> t:Type 
             -> Prop (HasType EEmp ex tx)
             -> Prop (IsWellFormed EEmp (TFun x tx t))
             -> Prop (IsWellFormed (EBind x tx EEmp) s)
             -> Prop (IsSubType (EBind x tx EEmp) s t)
             -> Prop (HasType EEmp e (Substitutions.Types.subst s x ex))
             -> Prop (HasType EEmp e (TEx x tx t)) @-}
exLemma :: Var -> Expr -> Expr -> Type -> Type -> Type -> HasType -> IsWellFormed -> IsWellFormed -> IsSubType -> HasType  -> HasType
exLemma x ex e tx s t ex_hastype_tx txt_wf s_wf s_issub_t e_hastype_s 
  = assertProp (HasType EEmp e (TEx x tx t)) (
      TSub EEmp e (Substitutions.Types.subst s x ex) (TEx x tx t) e_hastype_s (
       assertProp (IsSubType EEmp (Substitutions.Types.subst s x ex) (TEx x tx t)) (
         SWit EEmp x tx ex (Substitutions.Types.subst s x ex) t ex_hastype_tx (
           Lemmata.Substitution.subtyping EEmp EEmp x ex tx s t 
            xtx_g_wf 
            ex_hastype_tx 
            (assertProp (IsWellFormed (eAppend EEmp (EBind x tx EEmp)) s) s_wf)
            t_wf
            s_issub_t
         )  
       )
     ) (assertProp (IsWellFormed EEmp (TEx x tx t)) (WFEx EEmp x tx t tx_wf t_wf))
      )
  where 
    xtx_g_wf = assertProp (WellFormedEnv (eAppend EEmp (EBind x tx EEmp))) (
                 WFFBnd EEmp x tx (typed EEmp ex tx WFEEmp ex_hastype_tx) WFEEmp
               )
    t_wf = assertProp (IsWellFormed (eAppend EEmp (EBind x tx EEmp)) t) (wellformedTFunRes EEmp x tx t txt_wf)
    tx_wf = typed EEmp ex tx WFEEmp ex_hastype_tx