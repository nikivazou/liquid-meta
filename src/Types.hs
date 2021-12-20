{-@ LIQUID "--reflection" @-}
module Types where

import Syntax 

{-@ reflect primType @-}
primType :: EPrim -> Type 
primType (PBool _) = TBase (TPrim TBool)
primType (PInt _)  = TBase (TPrim TInt ) 