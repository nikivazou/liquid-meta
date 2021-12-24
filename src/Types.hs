module Types where

import Syntax 
import Data.Set 
import qualified Expressions

{-@ measure freeVars @-}
freeVars :: Type -> Set Var
freeVars (TBase b (Predicate x e)) = difference (Expressions.freeVars e) (singleton x)
freeVars (TFun x tx t) = freeVars tx `union` difference (freeVars t) (singleton x)
freeVars (TEx  x tx t) = freeVars tx `union` difference (freeVars t) (singleton x)

