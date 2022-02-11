{-@ LIQUID "--reflection"        @-}
{-@ LIQUID "--ple"               @-}
{-@ LIQUID "--max-case-expand=5" @-}
module Theorem where 

import Syntax 
import Propositions
import Expressions 
import Primitives

import Lemmata.CanonicalForms
import qualified Lemmata.Primitives 
import Lemmata.Substitution 
import Lemmata.ValuesDontStep 

import Helpers.ProofCombinators




soundness :: Expr -> Type -> Expr -> HasType -> Evals -> Either () (Expr, Step) 
{-@ soundness :: eo:{Expr | lc eo } -> t:Type -> e:Expr
              -> Prop (HasType EEmp eo t) 
              -> Prop (Evals eo e)
              -> Either {v:() | isValue e} (Expr, Step)<{\e' p -> prop p = Step e e'}> @-}
soundness eo t e eo_has_t eo_evals_e = case eo_evals_e of 
    ERefl _ -> progress eo t eo_has_t 
    EStep _eo e1 _e eo_step_e1 e1_eval_e -> 
        soundness e1 t e (preservation eo t eo_has_t e1 eo_step_e1) e1_eval_e




progress :: Expr -> Type -> HasType -> Either () (Expr, Step)  
{-@ progress :: e:Expr -> t:Type -> ht:Prop (HasType EEmp e t) 
                 -> Either {v:() | isValue e} (Expr, Step)<{\e' p -> prop p = Step e e'}> 
                 / [hasTypeSize ht] @-}
progress _ _ (TVar _ _)     = error "impossible" 
progress e _ (TCon _ _)     = Left ()  
progress e _ (TLam _ _ _ _ _ _)   = Left () 
progress _ _ (TApp _ e ex t tx e_hastype ex_hastype) 
  = case progress e (TFun tx t) e_hastype of 
       Left _ -> case progress ex tx ex_hastype of 
                   Left _ -> case canonicalForm e tx t e_hastype of 
                                Left ee -> Right (open ee ex, SAppEL ee ex tx) 
                                Right p -> primUnique EEmp p (TFun tx t) e_hastype  
                                         ? Right (delta p ex, SAppEP p ex)
                   Right  (ex', ex_step_ex') -> Right (EApp e ex', SAppPR e ex ex' ex_step_ex')  
       Right (e', e_step_e') -> Right (EApp e' ex,SAppPL e e' ex e_step_e')




preservation :: Expr -> Type -> HasType -> Expr -> Step -> HasType 
{-@ preservation :: e:{Expr | lc e} -> t:Type -> hs:Prop (HasType EEmp e t) 
                 -> e':Expr -> Prop (Step e e') 
                 -> Prop (HasType EEmp e' t) 
                 /  [hasTypeSize hs] @-}
preservation v _ (TLam _ _ _ _ _ _) e v_step_e 
  = values_dont_step v e v_step_e
preservation _ _ (TVar _ _) _ _ 
  = error "impossible"
preservation v _ (TCon _ _) e v_step_e 
  = values_dont_step v e v_step_e
preservation _ _ (TApp _ _ _ t tx e_hastype ex_hastype) e' eex_step_e' 
  = case eex_step_e' of 
      SAppPL e e' ex e_step_e' -> 
        TApp EEmp e' ex t tx (preservation e (TFun tx t) e_hastype e' e_step_e') ex_hastype
      SAppPR e ex ex' ex_step_ex' -> 
        TApp EEmp e ex' t tx e_hastype (preservation ex tx ex_hastype ex' ex_step_ex') 
      SAppEL e ex _ -> case e_hastype of 
                         TLam _ _ _ _ x ee_hastype -> 
                            assert (eAppend EEmp (EBind x tx EEmp) == (EBind x tx EEmp)) ?
                            assert (open e ex == e') ?
                            substitution EEmp EEmp x ex e t tx ee_hastype ex_hastype
                         _ -> error "impossible"
      SAppEP p ex -> primUnique EEmp p (TFun tx t) e_hastype ? 
                     Lemmata.Primitives.preservation ex t tx p ex_hastype
       