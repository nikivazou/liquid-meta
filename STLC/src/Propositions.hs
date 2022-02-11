{-# LANGUAGE GADTs        #-}
{-@ LIQUID "--reflection" @-}
module Propositions where

import Syntax 
import Expressions
import Primitives
import Data.Set 



-- Define Proposition as the predicates you want to reason about.  

data Proposition 
  = HasType Env  Expr Type -- g |- e :: t 
  | Step    Expr Expr      -- e ->  e'
  | Evals   Expr Expr      -- e ->* e'





-- Define `Prop P` to turn `P` in to a refinement type.  

{-@ type Prop P = {w:_ | prop w = P } @-}
{-@ measure prop :: a -> Proposition @-}

-- If `w::Prop p`, there should be a proof that `prop w = p`.
-- Because `prop` is uninterpreted, 
-- this proof comes from axiomatization. 



-- | Step Axiomatization (small step semantics). 
-- | Prop (Step e e') defines e -> e'

{-@ 
data Step where 
  SAppPL :: e1:Expr -> e1':Expr -> e2:Expr 
         -> Prop (Step e1 e1')          
         -> Prop (Step (EApp e1 e2) (EApp e1' e2)) 
  SAppPR :: e1:Expr -> e2:Expr -> e2':Expr 
         -> Prop (Step e2 e2')
         -> Prop (Step (EApp e1 e2) (EApp e1 e2')) 
  SAppEL :: e:Expr -> ex:Expr -> tx:Type 
         -> Prop (Step (EApp (ELam tx e) ex) (open e ex)) 
  SAppEP :: p:EPrim -> v:{Expr | isValue v } 
         -> Prop (Step (EApp (EPrim p) v) (Primitives.delta p v)) 
  @-}





-- | Evals Axiomatization (transitive closure of step). 
-- | Prop (Evals e e') defines e ->* e'

{-@ 
data Evals where 
  ERefl :: e:Expr -> Prop {Evals e e}
  EStep :: e1:{Expr | lc e1 } -> e2:{Expr | lc e2} -> e3:Expr
        -> Prop (Step  e1 e2)
        -> Prop (Evals e2 e3) 
        -> Prop (Evals e1 e3)  
  @-}


-- | Hastype Axiomatization (typing rules). 
-- | Prop (HasType g e t) defines g |- e : t

{-@ data HasType where 
     TApp :: g:Env -> e:Expr -> ex:Expr -> t:Type -> tx:Type 
          -> Prop (HasType g e (TFun tx t)) 
          -> Prop (HasType g ex tx)
          -> Prop (HasType g (EApp e ex) t) 
     TLam :: g:Env -> e:Expr -> tx:Type -> t:Type 
          -> x:{Var | not (member x (dom g)) && not (member x (freeVars e))} 
          -> Prop (HasType (EBind x tx g) (open e (EFVar x)) t) 
          -> Prop (HasType g (ELam tx e) (TFun tx t)) 
     TVar :: g:Env -> x:{Var | member x (dom g)} 
          -> Prop (HasType g (EFVar x) (Syntax.lookupEnv g x))
     TCon :: g:Env -> p:EPrim
          -> Prop (HasType g (EPrim p) (Primitives.primType p))
 @-}




-- Proof Debugging 

{-@ assertProp :: p:Proposition  -> Prop p -> Prop p @-}
assertProp :: Proposition -> a -> a 
assertProp _ x = x 


-- | Measure for termination proofs 

hasTypeSize :: HasType -> Int  
{-@ hasTypeSize :: HasType -> {v:Int | 0 < v } @-}
{-@ measure hasTypeSize @-}
hasTypeSize (TCon _ _)               = 1 
hasTypeSize (TVar _ _)               = 1 
hasTypeSize (TLam _ _ _ _ _ ht)      = hasTypeSize ht  + 1 
hasTypeSize (TApp _ _ _ _ _ ht1 ht2) = hasTypeSize ht1 + hasTypeSize ht2 + 1 


-- Haskell Definitions 

data Step where 
  SAppPL :: Expr  -> Expr -> Expr -> Step -> Step 
  SAppPR :: Expr  -> Expr -> Expr -> Step -> Step 
  SAppEL :: Expr  -> Expr -> Type -> Step 
  SAppEP :: EPrim -> Expr -> Step 
  


data HasType where 
     TApp :: Env -> Expr -> Expr -> Type -> Type -> HasType -> HasType -> HasType
     TLam :: Env -> Expr -> Type -> Type -> Var -> HasType -> HasType
     TVar :: Env -> Var ->  HasType
     TCon :: Env -> EPrim -> HasType 







data Evals where 
  ERefl :: Expr -> Evals 
  EStep :: Expr -> Expr -> Expr -> Step -> Evals -> Evals  


