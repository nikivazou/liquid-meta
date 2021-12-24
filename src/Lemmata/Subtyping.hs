{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{- LIQUID "--fast"       @-}
{-@ LIQUID "--no-termination"        @-}

module Lemmata.Subtyping where 

import Syntax 
import Propositions
import Environments 
import WellFormed

import Substitutions.Types 
import Substitutions.Expressions 
import Substitutions.Implies 
import Helpers.ProofCombinators 

import Lemmata.Narrowing.Subtype 
import Lemmata.Weakening 
import Lemmata.Substitution

import Data.Set 
import Types 

subtypeId :: Env -> Type -> IsWellFormed -> IsSubType
{-@ subtypeId :: g:Env -> t:Type -> Prop (IsWellFormed g t) -> Prop (IsSubType g t t) / [typeSize t] @-}
subtypeId g (TBase b (Predicate x p)) _
  = SBase g b p p (
      -- assertProp (Implies (EBind x (TBase b top) g) p (Substitutions.Expressions.subst p x (EVar x))) (
        (IRefl (EBind x (TBase b top) g) (
          Substitutions.Expressions.substId p x ? p)
        ))
      -- )
subtypeId g (TFun x tx t) t_wf 
  = case t_wf of 
     WFFun _ _ _ _ tx_wf t_wf -> 
       SFun g x tx tx t t (subtypeId g tx tx_wf) (subtypeId (EBind x tx g) t t_wf) 
subtypeId g (TEx x tx t) t_wf 
  = case t_wf of 
     WFEx _ _ _ _ tx_wf t_wf ->   
       SBnd g x tx t (wellformed g tx tx_wf ? TEx x tx t) (
         -- assertProp (IsSubType (EBind x tx g) t (TEx x tx t)) (
           SWit (EBind x tx g) x tx (EVar x) t t 
             (TVar (EBind x tx g) x tx) (
             -- assertProp (IsSubType (EBind x tx g) t (Substitutions.Types.subst t x (EVar x))) (
                 subtypeId (EBind x tx g) (Substitutions.Types.substId t x ? t) t_wf
             -- )  
                )
         --   )
       )

subtypeTrans :: Env -> Type -> Type -> Type -> IsWellFormed -> IsWellFormed -> IsWellFormed -> IsSubType -> IsSubType -> IsSubType
{-@ subtypeTrans :: g:Env -> t:Type -> w:Type -> s:Type 
              -> Prop (IsWellFormed g t)
              -> Prop (IsWellFormed g w)
              -> Prop (IsWellFormed g s)
              -> st1: Prop (IsSubType g t w) 
              -> st2: Prop (IsSubType g w s)
              -> Prop (IsSubType g t s) @-}
subtypeTrans g t _ _ t_wf w_wf s_wf t_issub_w  (SWit _ x sx ex w s ex_hastype_sx w_issub_s)
  = SWit g x sx ex t s ex_hastype_sx (
        subtypeTrans g t w (Substitutions.Types.subst s x ex) t_wf w_wf
            (wellformedTEx g x sx s ex ex_hastype_sx s_wf) 
             t_issub_w w_issub_s
    )
subtypeTrans g _ _ _ _ _ _ (SBase _ b p1 p2 p1_implies_p2) w_issub_s 
  = case w_issub_s of 
     SBase _ _ _ p3 p2_implies_p3 -> SBase g b p1 p3 (
         ITrans (EBind pvar (TBase b top) g) 
            p1 p2 p3 p1_implies_p2 p2_implies_p3
       ) 
subtypeTrans g _ _ _ t_wf w_wf ss_wf (SFun _ x tx wx t w wx_issub_tx t_issub_w_with_wx) w_issub_s 
  = case w_issub_s of 
     SFun _ _ wx sx w s sx_issub_wx w_issub_s_with_sx -> 
       case ss_wf of 
         WFFun _ _ _ _ sx_wf s_wf -> 
          let sx_issub_tx = subtypeTrans g sx wx tx 
                              sx_wf
                              (wellformedTFunArg g x wx w w_wf)
                              (wellformedTFunArg g x tx t t_wf)
                              sx_issub_wx wx_issub_tx  in 
          SFun g x tx sx t s sx_issub_tx (
          --  assertProp (IsSubType (EBind x sx g) t s) (
             subtypeTrans (EBind x sx g) t w s 
                (wellformedTFunRes g x tx t sx sx_issub_tx t_wf) 
                (wellformedTFunRes g x wx w sx sx_issub_wx w_wf) 
                s_wf (
              -- assertProp (IsSubType (eAppend EEmp (EBind x sx g)) t w) 
                (narrowing EEmp g x sx wx t w sx_issub_wx t_issub_w_with_wx) 
              ) w_issub_s_with_sx
          --  )
          )
subtypeTrans _ _ _ _ t_wf w_wf s_wf (SWit g x wx ex t w ex_hastype_wx t_subtype_w) w_issub_s 
  = case w_issub_s of 
     SBnd _ _ _ _ s w_subtype_s -> 
       subtypeTrans g t (Substitutions.Types.subst w x ex) s t_wf (wellformedTEx g x wx w ex ex_hastype_wx w_wf) s_wf
         t_subtype_w
         (Substitutions.Types.subst s x ex ? 
         Lemmata.Substitution.types EEmp g x ex wx w s ex_hastype_wx w_subtype_s)
subtypeTrans _ (TEx x tx t) _ s (WFEx _ _ _ _ tx_wf t_wf) w_wf s_wf (SBnd g _ _ _ w t_issub_w) w_issub_s -- | not (member x (freeVars s))
  = -- assertProp (IsSubType g (TEx x tx t) s) (
      SBnd g x tx t (wellformed g s s_wf ? s) ( -- NV: Yeah! Set theory good example! 
        subtypeTrans (EBind x tx g) t w s 
          t_wf
          (wfWeakening EEmp g x tx w w_wf)
          (wfWeakening EEmp g x tx s s_wf)
          t_issub_w (weakening EEmp g x tx w s w_issub_s) 
      )
    -- )
 