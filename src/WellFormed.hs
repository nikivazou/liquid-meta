{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module WellFormed where 

import Syntax
import Unrefine
import Propositions
import Environments 
import Substitutions.Types
import Substitutions.Environment
import Substitutions.Expressions

import qualified Lemmata.Weakening
import Lemmata.Unrefine (uwellformed)
import Helpers.ProofCombinators
import Assumptions.Constants

import Data.Set 
import Types 
import qualified Expressions 


wellFormedPostFix :: Env -> Env -> Var -> Type -> WellFormedEnv -> WellFormedEnv 
{-@ wellFormedPostFix :: g1:Env -> g2:Env -> y:Var -> ty:Type 
                      -> Prop (WellFormedEnv (eAppend g1 (EBind y ty g2)))
                      -> Prop (WellFormedEnv g2) @-}
wellFormedPostFix g1 g2 y ty wf
  = case wellFormedAppend g1 (EBind y ty g2) wf of 
       WFFBnd _ _ _ _ wf' -> wf' 


wellFormedAppend :: Env -> Env -> WellFormedEnv -> WellFormedEnv 
{-@ wellFormedAppend :: g1:Env -> g2:Env 
                      -> Prop (WellFormedEnv (eAppend g1 g2))
                      -> Prop (WellFormedEnv g2) @-}
wellFormedAppend EEmp g2 wf = wf 
wellFormedAppend (EBind x tx g1) g2 (WFFBnd _ _ _ _ wf) 
  = wellFormedAppend g1 g2 wf   



{-@ wf_sub_wit :: g1:Env -> g2:{Env | intersection (dom g1) (dom g2) == empty} 
               -> x:{Var | not (member x (union (dom g1) (dom g2)))} 
               -> tx:Type 
               -> y:{Var | x /= y && not (member y (union (dom g1) (dom g2)))} 
               -> ty:{Type | not (member x (dom (eAppend g1 (EBind y ty g2))))} 
               -> Prop (IsWellFormed (eAppend g1 (EBind y ty g2)) tx)
               -> Prop (WellFormedEnv (eAppend g1 (EBind y ty g2))) 
               -> Prop (WellFormedEnv (eAppend EEmp (EBind x tx (eAppend g1 (EBind y ty g2))))) @-}
wf_sub_wit :: Env -> Env -> Var -> Type -> Var -> Type -> IsWellFormed -> WellFormedEnv -> WellFormedEnv 
wf_sub_wit g1 g2 x tx y ty tx_wf wf 
  = WFFBnd (eAppend g1 (EBind y ty g2)) x tx tx_wf wf 

pushBindWFFBnd :: Env -> Env -> Var -> Type -> Var -> Type -> IsWellFormed -> WellFormedEnv -> WellFormedEnv 
{-@ pushBindWFFBnd :: g1:Env -> g2:{Env | intersection (dom g1) (dom g2) == empty} -> x:Var -> tx:Type
                   -> y:{Var | not (member y (union (dom g1) (dom g2)))}
                   -> ty:{Type | not (member x (dom (eAppend g1 (EBind y ty g2))))} 
                   -> Prop (IsWellFormed (eAppend g1 (EBind y ty g2)) tx)
                   -> Prop (WellFormedEnv (eAppend g1 (EBind y ty g2)))
                   -> Prop (WellFormedEnv (eAppend (EBind x tx g1) (EBind y ty g2))) @-}
pushBindWFFBnd g1 g2 x tx y ty tx_wf wf 
  = pushBind g1 (EBind y ty g2) x tx 
             (WFFBnd (eAppend g1 (EBind y ty g2)) x tx tx_wf wf)

pushBind :: Env -> Env -> Var -> Type -> WellFormedEnv -> WellFormedEnv 
{-@ pushBind :: g1:Env -> g2:Env -> x:Var -> tx:Type
             -> Prop (WellFormedEnv (EBind x tx (eAppend g1 g2)))
             -> Prop (WellFormedEnv (eAppend (EBind x tx g1) g2)) @-}
pushBind g1 g2 x tx wf = wf

wellformed' :: Env -> Expr -> Type -> WellFormedEnv -> HasType -> ()
{-@ wellformed' :: g:Env -> e:Expr -> t:Type -> Prop (WellFormedEnv g) -> Prop (HasType g e t) 
                -> { isSubsetOf (Types.freeVars t) (dom g) && isSubsetOf (Expressions.freeVars e) (dom g) } @-}
wellformed' g e t g_wf ht 
  = wellformed g t (typed g e t g_wf ht)
  ? typedFreeVars g e t ht

typedFreeVars :: Env -> Expr -> Type -> HasType -> ()
{-@ typedFreeVars :: g:Env -> e:Expr -> t:Type -> Prop (HasType g e t) 
                -> { isSubsetOf (Expressions.freeVars e) (dom g) } @-}
typedFreeVars _ _ _ (TApp g e ex t x tx e_hastype ex_hastype_tx) 
  = typedFreeVars g e (TFun x tx t) e_hastype
  ? typedFreeVars g ex tx ex_hastype_tx
typedFreeVars _ _ _ (TLam g x e tx t e_hastype _) 
  = typedFreeVars (EBind x tx g) e t e_hastype 
typedFreeVars _ _ _ (TVar _ _) = () 
typedFreeVars _ _ _ (TCon _ _) = () 
typedFreeVars _ _ _ (TSub g e s _ e_hastype _ _) 
  = typedFreeVars g e s e_hastype

wellformed :: Env -> Type -> IsWellFormed -> ()
{-@ wellformed :: g:Env -> t:Type -> Prop (IsWellFormed g t) 
               -> { isSubsetOf (Types.freeVars t) (dom g) && intersection (dom g) (Types.boundVars t) == empty } @-}
wellformed _ t (WFBs g b p x p_hastype_bool)
  = uwellformed 
       (UEBind x (FTBase b) (Unrefine.uenv g)) 
       (Substitutions.Expressions.subst p pvar (EVar x)) 
       (FTBase TBool) p_hastype_bool
wellformed _ _ (WFFun g x tx t tx_wf t_wf) 
  = wellformed g tx tx_wf
  ? wellformed (EBind x tx g) t t_wf
wellformed _ _ (WFEx  g x tx t tx_wf t_wf) 
  = wellformed g tx tx_wf
  ? wellformed (EBind x tx g) t t_wf
 
{-@ wellformedFun :: g:Env -> e:Expr -> x:Var -> tx:Type -> t:Type 
                  -> Prop (WellFormedEnv g)
                  -> Prop (HasType g e (TFun x tx t))
                  -> { not (member x (dom g)) } @-}
wellformedFun :: Env -> Expr -> Var -> Type -> Type -> WellFormedEnv -> HasType -> ()
wellformedFun g e x tx t g_wf e_hastype 
  = case typed g e (TFun x tx t) g_wf e_hastype of  
      WFFun _ _ _ _ _ _ -> ()


wellformedTFunArg :: Env -> Var -> Type -> Type -> IsWellFormed -> IsWellFormed 
{-@ wellformedTFunArg :: g:Env -> x:Var -> tx:Type -> t:Type 
                 -> Prop (IsWellFormed g (TFun x tx t))
                 -> Prop (IsWellFormed g tx) @-}
wellformedTFunArg _ _ _ _ (WFFun _ _ _ _ wf _) = wf

wellformedTFunRes :: Env -> Var -> Type -> Type  -> IsWellFormed -> IsWellFormed 
{-@ wellformedTFunRes :: g:Env -> x:Var -> tx:Type -> t:Type 
                 -> Prop (IsWellFormed g (TFun x tx t))
                 -> Prop (IsWellFormed (EBind x tx g) t) @-}
wellformedTFunRes _ _ _ _ (WFFun _ _ _ _ _ wf) = wf




typed :: Env -> Expr -> Type -> WellFormedEnv -> HasType -> IsWellFormed
{-@ typed :: g:Env -> e:Expr -> t:Type 
          -> Prop (WellFormedEnv g)
          -> Prop (HasType g e t) 
          -> Prop (IsWellFormed g t) @-}
typed _ _ _ g_wf (TApp g e ex t x tx e_hastype ex_hastype_tx) 
  = case typed g e (TFun x tx t) g_wf e_hastype of 
      WFFun _ _ _ _ _ t_wf -> 
        WFEx g x tx t (typed g ex tx g_wf ex_hastype_tx) t_wf
typed _ _ _ g_wf (TLam g x e tx t e_hastype_t tx_wf) 
  = WFFun g x tx t tx_wf 
     (typed (EBind x tx g) e t (WFFBnd g x tx tx_wf g_wf) e_hastype_t)
typed _ _ _ g_wf (TVar g x) = undefined 
typed _ _ _ g_wf (TCon g p) = primWellFormed g p g_wf  
typed _ _ _ _ (TSub _ _ _ _ _ _ t_wf) = t_wf 


lookupWellFormed :: Env -> Var -> WellFormedEnv -> IsWellFormed 
{-@ lookupWellFormed :: g:Env -> y:{Var | member y (dom g)} 
                     -> Prop (WellFormedEnv g)
                     -> Prop (IsWellFormed g (lookupEnv g y)) @-}
lookupWellFormed gg@(EBind x tx g) y (WFFBnd _ _ _ tx_wf wf)
  | x == y    = Lemmata.Weakening.wellFormed EEmp g x tx tx tx_wf
  | otherwise = Lemmata.Weakening.wellFormed EEmp g x tx (lookupEnv gg y) (lookupWellFormed g y wf)  