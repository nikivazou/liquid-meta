{-@ LIQUID "--reflection"        @-}
{-@ LIQUID "--ple"               @-}
module Lemmata.CanonicalForms where 

import Syntax 
import Propositions
import Expressions 
import Primitives


{-@ primUnique :: g:Env -> p:EPrim -> t:Type 
               -> Prop (HasType g (EPrim p) t)
               -> {t == primType p} @-}
primUnique :: Env -> EPrim -> Type -> HasType -> () 
primUnique _ _ _ (TCon _ _) = ()
primUnique _ _ _ _ = () 

{-@ canonicalForm :: e:{Expr | isValue e} 
                  -> tx:Type -> t:Type 
                  -> Prop (HasType EEmp e (TFun tx t)) 
                  -> Either {ee:Expr | e == ELam tx ee } {p:EPrim | EPrim p == e} @-}
canonicalForm :: Expr -> Type -> Type -> HasType -> Either Expr EPrim
canonicalForm _ _ _ (TLam _ e tx t x _) = Left  e
canonicalForm _ _ _ (TCon _ p)          = Right p 
canonicalForm _ _ _ _                   = error "impossible"


{-@ canonicalBool :: v:{Expr | isValue v} 
                  -> Prop (HasType EEmp v (TPrim TBool)) 
                  -> (b::Bool, {p:() | v == (EPrim (PBool b))}) @-}
canonicalBool :: Expr -> HasType -> (Bool,())
canonicalBool _ (TCon _ (PBool b)) = (b,()) 
canonicalBool _ _                  = error "impossible" 

{-@ canonicalInt :: v:{Expr | isValue v} 
                  -> Prop (HasType EEmp v (TPrim TInt)) 
                  -> (n::Int, {p:() | v == (EPrim (PInt n))}) @-}
canonicalInt :: Expr -> HasType -> (Int,())
canonicalInt _ (TCon _ (PInt n)) = (n,()) 
canonicalInt _ _                  = error "impossible" 
