{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--ple"            @-}

module Lemmata.Substitution where 

import Syntax 
import Propositions
import Constants
import Expressions 
import Environments
import Types 
import Unrefine
import Assumptions.Constants 

import WellFormed
import Lemmata.Weakening
import qualified Lemmata.Narrowing
import Substitutions.Expressions 
import Substitutions.Types 
import Substitutions.Environment 
import SystemF.Properties

import Helpers.ProofCombinators
import Data.Set 

{-@ wellformedness :: g1:Env -> g2:{Env | intersection (dom g1) (dom g2) == empty} 
                   -> x:{Var | not (member x (union (dom g1) (dom g2)))} 
                   -> ex:Expr -> tx:Type -> t:Type 
                   -> Prop (WellFormedEnv (eAppend g1 (EBind x tx g2)))
                   -> Prop (HasType g2 ex tx)
                   -> wf:Prop (IsWellFormed (eAppend g1 (EBind x tx g2)) t) 
                   -> Prop (IsWellFormed (eAppend (Substitutions.Environment.subst g1 x ex) g2) 
                                         (Substitutions.Types.subst t x ex)) 
                   / [isWellFormedSize wf] @-}
wellformedness :: Env -> Env -> Var -> Expr -> Type -> Type -> WellFormedEnv -> HasType -> IsWellFormed -> IsWellFormed 
wellformedness g1 g2 y ey ty _ wf ey_hastype_ty (WFBs _ b p x p_hastype_bool)
  = (not (member x (dom g))) 
  ? (not (member pvar (dom g2)))
  ? wellformed' g2 ey ty (wellFormedPostFix g1 g2 y ty wf) ey_hastype_ty 
  ? Substitutions.Expressions.substFlip p pvar (EVar x) y ey 
  ? uenvSubst g1 y ey 
  ? uenvAppend (Substitutions.Environment.subst g1 y ey) g2 
  ? uenvAppend g1 (EBind y ty g2) -- NV: REST CAN TAKE CARE OF THESE! 
  ? WFBs g' b p' x (
      SystemF.Properties.substitution 
                      (UEBind x (FTBase b) (uenv g1)) 
                      (uenv g2) y ey (utype ty) 
                      pe (FTBase TBool)
                      (uhastype g2 ey ty ey_hastype_ty)
                      p_hastype_bool
     )
  where 
   p'  = Substitutions.Expressions.subst p y ey
   g'  = eAppend (Substitutions.Environment.subst g1 y ey) g2
   ug  = UEBind x (FTBase b) (Unrefine.uenv g)
   pe  = Substitutions.Expressions.subst p pvar (EVar x)
   g   = eAppend g1 (EBind y ty g2)

wellformedness g1 g2 y ey ty _ wf ey_hastype_ty (WFFun _ x tx t tx_wf t_wf)
  = WFFun g' x tx' t' 
      (wellformedness g1 g2 y ey ty tx wf ey_hastype_ty tx_wf)
      (wellformedness (EBind x tx g1) g2 y ey ty t (
        WFFBnd (eAppend g1 (EBind y ty g2)) x tx tx_wf wf)
        ey_hastype_ty t_wf)
  where 
   g'  = eAppend (Substitutions.Environment.subst g1 y ey) g2
   t'  = Substitutions.Types.subst t y ey
   tx' = Substitutions.Types.subst tx y ey

wellformedness g1 g2 y ey ty _ wf ey_hastype_ty (WFEx  _ x tx t tx_wf t_wf)
  = WFEx g' x tx' t' 
      (wellformedness g1 g2 y ey ty tx wf ey_hastype_ty tx_wf)
      (wellformedness (EBind x tx g1) g2 y ey ty t (
        WFFBnd (eAppend g1 (EBind y ty g2)) x tx tx_wf wf)
        ey_hastype_ty t_wf)
  where 
   g'  = eAppend (Substitutions.Environment.subst g1 y ey) g2
   t'  = Substitutions.Types.subst t y ey
   tx' = Substitutions.Types.subst tx y ey

{-@ subtyping :: g1:Env -> g2:{Env | intersection (dom g1) (dom g2) == empty} 
                -> x:{Var | not (member x (union (dom g1) (dom g2)))} 
                -> ex:Expr -> tx:Type -> s:Type -> t:Type 
                -> Prop (WellFormedEnv (eAppend g1 (EBind x tx g2)))
                -> Prop (HasType g2 ex tx)
                -> Prop (IsWellFormed (eAppend g1 (EBind x tx g2)) s)
                -> Prop (IsWellFormed (eAppend g1 (EBind x tx g2)) t)
                -> st:Prop (IsSubType (eAppend g1 (EBind x tx g2)) s t)
                -> Prop (IsSubType (eAppend (Substitutions.Environment.subst g1 x ex) g2) 
                                   (Substitutions.Types.subst s x ex) 
                                   (Substitutions.Types.subst t x ex)) 
                / [isSubTypeSize st] @-}
subtyping :: Env -> Env -> Var -> Expr -> Type -> Type -> Type -> WellFormedEnv -> HasType -> IsWellFormed -> IsWellFormed -> IsSubType -> IsSubType  
subtyping g1 g2 y ey ty s t wf ey_hastype_ty _ _ (SBase _ b p1 p2 p1_implies_p2) 
  = SBase g' b p1' p2' (ISubst g1 g2 b y ty ey p1 p2 ey_hastype_ty p1_implies_p2)  
  where 
   p1' = Substitutions.Expressions.subst p1 y ey
   p2' = Substitutions.Expressions.subst p2 y ey
   g'  = eAppend (Substitutions.Environment.subst g1 y ey) g2
   s'  = Substitutions.Types.subst s y ey 
   t'  = Substitutions.Types.subst t y ey 
subtyping g1 g2 y ey ty _ _ wf ey_hastype_ty ss_wf tt_wf (SFun _ x sx tx s t tx_issub_sx s_issub_t) 
  = case ss_wf of 
      WFFun _ _ _ _ sx_wf s_wf -> 
        case tt_wf of 
          WFFun _ _ _ _ tx_wf t_wf -> 
            (not (member x (dom (eAppend g1 (EBind y ty g2)))))
            ? SFun g' x sx' tx' s' t' 
                (subtyping g1 g2 y ey ty tx sx wf ey_hastype_ty tx_wf sx_wf tx_issub_sx)
                (subtyping (EBind x tx g1) g2 y ey ty s t 
                  (pushBindWFFBnd g1 g2 x tx y ty tx_wf wf)
                  ey_hastype_ty 
                  (Lemmata.Narrowing.iswellformed EEmp 
                    (eAppend g1 (EBind y ty g2)) 
                    x tx sx s tx_issub_sx s_wf) 
                  t_wf s_issub_t) 
  where 
   tx' = Substitutions.Types.subst tx y ey
   sx' = Substitutions.Types.subst sx y ey
   t'  = Substitutions.Types.subst t  y ey
   s'  = Substitutions.Types.subst s  y ey
   g'  = eAppend (Substitutions.Environment.subst g1 y ey) g2
subtyping g1 g2 y ey ty _ _ wf ey_hastype_ty s_wf tt_wf (SWit _ x tx ex s t ex_hastype_tx s_issub_t) 
  = case tt_wf of 
     WFEx _ _ _ _ tx_wf t_wf -> 
       wellformed' g ex tx wf ex_hastype_tx ?  
       wellformed' g2 ey ty (wellFormedPostFix g1 g2 y ty wf) ey_hastype_ty ? 
       assert (x /= y) ? 
       assert (isSubsetOf (Expressions.freeVars ex) (dom g)) ? 
       assert (not (member x (dom g)) ) ? 
       assert (not (member x (Expressions.freeVars ey))) ?
       wellformed (EBind x tx g) t t_wf ? 
       assert (intersection (dom (EBind x tx g)) (Types.boundVars t) == empty) ? 
       assert (member y (dom (EBind x tx g))) ? 
       assert (not (member y (Types.boundVars t))) ? 
--        assert (not (member y (Expressions.freeVars ex)))?
       Substitutions.Types.substFlip t x ex y ey ? 
       SWit g' x tx' ex' s' t' 
        (expressions g1 g2 y ey ty ex tx wf ey_hastype_ty ex_hastype_tx)
        (subtyping g1 g2 y ey ty s t_xex wf ey_hastype_ty s_wf (
            wellformedness EEmp g x ex tx t (
              wf_sub_wit g1 g2 x tx y ty tx_wf wf 
            ) ex_hastype_tx t_wf
          ) s_issub_t)
  where 
   tx' = Substitutions.Types.subst tx y ey
   ex' = Substitutions.Expressions.subst ex y ey
   t'  = Substitutions.Types.subst t y ey
   t_xex  = Substitutions.Types.subst t x ex
   s'  = Substitutions.Types.subst s y ey
   g'  = eAppend (Substitutions.Environment.subst g1 y ey) g2
   g   = eAppend g1 (EBind y ty g2)

subtyping g1 g2 y ey ty ss _ wf ey_hastype_ty ss_wf t_wf (SBnd _ x sx s t s_issub_t) 
  = case ss_wf of 
     WFEx _ _ _ _ sx_wf s_wf -> 
      -- assert (not (member x (dom (eAppend g1 (EBind y ty g2))))) ? 
      -- assert (x /= y) ? 
      wellformed' g2 ey ty (wellFormedPostFix g1 g2 y ty wf) ey_hastype_ty ?
      -- assert (isSubsetOf (Expressions.freeVars ey) (dom g2)) ? 
      -- assert (not (member x (Expressions.freeVars ey))) ? 
      -- assert (not (member x (Types.freeVars t'))) ? 
      -- assert (isSubsetOf (Types.freeVars t') (Types.freeVars t `union` Expressions.freeVars ey)) ? 
         SBnd g' x sx' s' t' (
              subtyping (EBind x sx g1) g2 y ey ty s t 
                (pushBind g1 (EBind y ty g2) x sx (WFFBnd g x sx sx_wf wf)) 
                ey_hastype_ty 
                -- (assertProp (IsWellFormed (eAppend (EBind x sx g1) (EBind y ty g2)) s) 
                s_wf
                -- ) 
                -- (assertProp (IsWellFormed (eAppend (EBind x sx g1) (EBind y ty g2)) s) (pushBind' g1 (EBind y ty g2) x sx s s_wf)) 
                (Lemmata.Weakening.wellFormed EEmp (eAppend g1 (EBind y ty g2)) x sx t t_wf)
                --- (wellFormed' g1 g2 y ty x sx t sx_wf t_wf)
                s_issub_t
         )
  where   
   g'  = eAppend (Substitutions.Environment.subst g1 y ey) g2
   s'  = Substitutions.Types.subst s  y ey
   sx' = Substitutions.Types.subst sx y ey
   ss' = Substitutions.Types.subst ss y ey
   t'  = Substitutions.Types.subst t  y ey
   g   = eAppend g1 (EBind y ty g2)

{-@ expressions :: g1:Env -> g2:{Env | intersection (dom g1) (dom g2) == empty} 
                -> x:{Var | not (member x (union (dom g1) (dom g2)))} 
                -> ex:Expr -> tx:Type -> e:Expr -> t:Type 
                -> Prop (WellFormedEnv (eAppend g1 (EBind x tx g2)))
                -> Prop (HasType g2 ex tx)
                -> ht:Prop (HasType (eAppend g1 (EBind x tx g2)) e t) 
                -> Prop (HasType (eAppend (Substitutions.Environment.subst g1 x ex) g2) 
                                 (Substitutions.Expressions.subst e x ex) 
                                 (Substitutions.Types.subst       t x ex)) 
                / [hasTypeSize ht] @-}
expressions :: Env -> Env -> Var -> Expr -> Type -> Expr -> Type -> WellFormedEnv -> HasType -> HasType -> HasType 
expressions g1 g2 y ey ty e _ wf ey_hastype_ty (TSub _ _ s t e_hastype_s s_subtype_t t_wf)
  = TSub g' e' s' t' 
      (expressions g1 g2 y ey ty e s wf ey_hastype_ty e_hastype_s)
      (subtyping   g1 g2 y ey ty s t wf ey_hastype_ty 
                   s_wf 
                   t_wf 
                   s_subtype_t)  
      (wellformedness g1 g2 y ey ty t wf ey_hastype_ty t_wf)
  where 
   s_wf = (typed (eAppend g1 (EBind y ty g2)) e s wf e_hastype_s)
   e' = Substitutions.Expressions.subst e y ey
   g' = eAppend (Substitutions.Environment.subst g1 y ey) g2
   s' = Substitutions.Types.subst s y ey
   t' = Substitutions.Types.subst t y ey
expressions g1 g2 y ey ty _ _ g_wf ey_hastype_ty (TApp _ e ex t x tx e_hastype_txt ex_hastype_tx)
  = wellformedFun (eAppend g1 (EBind y ty g2)) e x tx t g_wf e_hastype_txt
  ? TApp g' e' ex' t' x tx' 
      (expressions g1 g2 y ey ty e  (TFun x tx t)  g_wf ey_hastype_ty e_hastype_txt) 
      (expressions g1 g2 y ey ty ex tx g_wf ey_hastype_ty ex_hastype_tx) 
  where 
   e'  = Substitutions.Expressions.subst e y ey
   ex' = Substitutions.Expressions.subst ex y ey
   g'  = eAppend (Substitutions.Environment.subst g1 y ey) g2
   tx' = Substitutions.Types.subst tx y ey
   t'  = Substitutions.Types.subst  t y ey
expressions g1 g2 y ey ty _ s g_wf ey_hastype_ty (TLam g x e tx t e_hastype_t tx_wf)
  = -- assert (not (member x (dom (eAppend g1 (EBind y ty g2)))))
    TLam g' x e' tx' t' 
        (expressions (EBind x tx g1) g2 y ey ty e t 
           (pushBind g1 (EBind y ty g2) x tx (WFFBnd (eAppend g1 (EBind y ty g2)) x tx tx_wf 
           g_wf)) 
           ey_hastype_ty e_hastype_t
        ) 
        (wellformedness g1 g2 y ey ty tx g_wf ey_hastype_ty tx_wf)
  where 
   e'  = Substitutions.Expressions.subst e y ey
   g'  = eAppend (Substitutions.Environment.subst g1 y ey) g2
   tx' = Substitutions.Types.subst tx y ey
   t'  = Substitutions.Types.subst  t y ey
expressions g1 g2 y ey ty _ t wf ey_hastype_ty (TVar _ x)
  = exprVar g1 g2 y ey ty x t wf ey_hastype_ty
expressions g1 g2 y ey _ _ t _ _ (TCon _ p)
  = primTypeNoFree p 
  ? {- assert -} (t' == t ) 
  ? TCon g' p 
  where 
    g' = eAppend (Substitutions.Environment.subst g1 y ey) g2
    t' = Substitutions.Types.subst (primType p) y ey

{-@ exprVar :: g1:Env -> g2:{Env | intersection (dom g1) (dom g2) == empty} 
            -> x:{Var | not (member x (union (dom g1) (dom g2)))} 
            -> ex:Expr -> tx:Type -> e:{Var | member e (dom (eAppend g1 (EBind x tx g2)))} 
            -> t:{Type | t == lookupEnv (eAppend g1 (EBind x tx g2)) e} 
            -> Prop (WellFormedEnv (eAppend g1 (EBind x tx g2)))
            -> Prop (HasType g2 ex tx)
            -> Prop (HasType (eAppend (Substitutions.Environment.subst g1 x ex) g2) 
                             (Substitutions.Expressions.subst (EVar e) x ex) 
                             (Substitutions.Types.subst t x ex)) @-}
exprVar :: Env -> Env -> Var -> Expr -> Type -> Var -> Type -> WellFormedEnv -> HasType -> HasType 
exprVar g1 g2 y ey ty x t wf ey_hastype_ty 
  | x == y 
  = lookupLemma g1 g2 y ty 
  ? wellformed' g2 ey ty (wellFormedPostFix g1 g2 y ty wf) ey_hastype_ty
  ? {- assert -} (t' == ty)
  ? {- assert -} (e' == ey)
  ? weakeningTypeEnv g1' g2 ey ty ey_hastype_ty
  | member x (dom g1)
  = lookupSubst g1 (EBind y ty g2) g2 x t y ey 
  ? TVar g' x
  | otherwise
  = {- assert -} (member x (dom (eAppend g1 (EBind y ty g2))))
  ? lookupNoSubst g1 g2 x t y ty   
  ? wellformed' g2 (EVar x) t (wellFormedPostFix g1 g2 y ty wf) (TVar g2 x) 
  ? weakeningTypeEnv g1' g2 (EVar x) t  (TVar g2 x) 
  where 
    g1'   = Substitutions.Environment.subst g1 y ey
    g'    = eAppend (Substitutions.Environment.subst g1 y ey) g2
    e'    = Substitutions.Expressions.subst (EVar x) y ey
    t'    = Substitutions.Types.subst       t y ey