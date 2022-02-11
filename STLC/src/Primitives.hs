{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module Primitives where

import Syntax 

{-@ reflect primType @-}
primType :: EPrim -> Type 
primType (PBool _) = TPrim TBool
primType (PInt _)  = TPrim TInt
primType PNot      = TFun (TPrim TBool) (TPrim TBool)
primType PAdd      = TFun (TPrim TInt) (TFun (TPrim TInt) (TPrim TInt))
primType (PIAdd _) = TFun (TPrim TInt) (TPrim TInt)

{-@ reflect delta @-}
{-@ delta :: p:{EPrim | isTFun (primType p) } 
          -> Expr 
          -> Expr @-}
delta :: EPrim -> Expr  -> Expr 
delta PNot (EPrim (PBool b))     = EPrim (PBool (not b))
delta PAdd (EPrim (PInt n))      = EPrim (PIAdd n)
delta (PIAdd n) (EPrim (PInt m)) = EPrim (PInt (n + m))
delta _ e = e

