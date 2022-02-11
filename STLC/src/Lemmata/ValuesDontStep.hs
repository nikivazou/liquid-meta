{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module Lemmata.ValuesDontStep where 

import Syntax 
import Propositions
import Expressions 
import Primitives

import Helpers.ProofCombinators

values_dont_step :: Expr -> Expr -> Step -> a 
{-@ values_dont_step :: v:{Expr | isValue v } -> e:Expr -> Prop (Step v e) -> {v:a | false } @-}
values_dont_step v e step@(SAppPL e1 _ e2 _) 
  = assertProp (Step v e) step ?
    error "values_dont_step"
values_dont_step v e step@(SAppPR e1 _ e2 _) 
  = assertProp (Step v e) step ?
    error "values_dont_step"
values_dont_step v e step@(SAppEL _ _ _) 
  = assertProp (Step v e) step ?
    error "values_dont_step"
values_dont_step v e step@(SAppEP _ _) 
  = assertProp (Step v e) step ?
    error "values_dont_step"