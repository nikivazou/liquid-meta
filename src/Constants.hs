{-@ LIQUID "--reflection" @-}

module Constants where 

import Syntax 
import Types 

{-@ measure delta :: EPrim -> Expr -> Expr @-}
{-@ delta :: p:EPrim -> e:Expr -> {r:Expr | r = delta p e } @-}
delta :: EPrim -> Expr -> Expr 
delta _ e = undefined -- SAFE undefined 

{-@ measure primType :: EPrim -> Type @-}
{-@ assume primType :: p:EPrim -> {t:Type | t = primType p } @-}
primType :: EPrim -> Type 
primType (PBool _) = TBase (TPrim TBool) (Predicate 0 (EPrim (PBool True)))
primType (PInt _)  = TBase (TPrim TInt ) (Predicate 0 (EPrim (PBool True)))
