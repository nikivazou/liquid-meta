{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module Lemmata.Weakening where 

import Syntax 
import Propositions 
import Environments
import Data.Set
import qualified Types 
import Unrefine 
import Substitutions.Expressions

import Helpers.ProofCombinators

{-@ wellFormed :: g1:Env -> g2:{Env | intersection (dom g1) (dom g2) == empty} 
               -> y:{Var | not (member y (dom g1)) && not (member y (dom g2)) } 
               -> ty:Type -> t:Type 
               -> Prop (IsWellFormed (eAppend g1 g2) t)
               -> Prop (IsWellFormed (eAppend g1 (EBind y ty g2)) t)
  @-}
wellFormed :: Env -> Env -> Var -> Type -> Type -> IsWellFormed -> IsWellFormed
wellFormed _ _ _ _ _ (WFBs g b p x p_hastype_bool) = undefined 
wellFormed _ _ _ _ _ (WFFun g x tx t tx_wf t_wf) = undefined 
wellFormed g1 g2 y ty (TEx _ _ _) (WFEx g x tx t tx_wf t_wf) 
  = undefined   

{-@ weakeningTypeEnv :: g1:Env -> g2:{Env | intersection (dom g1) (dom g2) == empty }  -> e:Expr -> t:Type
              -> Prop (HasType g2 e t)
              -> Prop (HasType (eAppend g1 g2) e t) @-} 
weakeningTypeEnv :: Env -> Env -> Expr -> Type -> HasType -> HasType
weakeningTypeEnv = undefined 

{-@ weakening :: g1:Env -> g2:Env -> x:Var -> tx:Type -> s:Type -> t:Type
              -> Prop (IsSubType (eAppend g1 g2) s t)
              -> Prop (IsSubType (eAppend g1 (EBind x tx g2)) s t) @-} 
weakening :: Env -> Env -> Var -> Type -> Type -> Type -> IsSubType -> IsSubType
weakening = undefined 