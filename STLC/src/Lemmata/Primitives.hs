
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module Lemmata.Primitives where 

import Syntax 
import Propositions
import Expressions 
import Primitives

import Lemmata.CanonicalForms
import Helpers.ProofCombinators

{-@ preservation :: v:{Expr | isValue v} -> t:Type -> tx:Type 
                 -> p:{EPrim | primType p == TFun tx t}
                 -> Prop (HasType EEmp v tx)
                 -> Prop (HasType EEmp (delta p v) t) @-}
preservation :: Expr -> Type -> Type -> EPrim -> HasType -> HasType 
preservation v _ _ PNot v_hastype 
  = case canonicalBool v v_hastype of 
      (b,_) -> case delta PNot (EPrim (PBool b)) of
                EPrim p -> TCon EEmp p 
preservation v t tx PAdd v_hastype 
  = case canonicalInt v v_hastype of 
      (n,_) -> case delta PAdd (EPrim (PInt n)) of
                EPrim (PIAdd n) -> TCon EEmp (PIAdd n) 
preservation v _ _ (PIAdd n) v_hastype 
  = case canonicalInt v v_hastype of 
      (m,_) -> case delta (PIAdd n) (EPrim (PInt m)) of
                 EPrim p -> TCon EEmp p 
preservation _ _ _ (PBool _) _ = error "imposible" 
preservation _ _ _ (PInt  _) _ = error "imposible" 
                    
