module Types where

import Syntax 
import Data.Set 
import qualified Expressions


{-@ measure isTEx @-} 
isTEx :: Type -> Bool 
isTEx (TEx _ _ _) = True 
isTEx _ = False 

{-@ measure freeVars @-}
freeVars :: Type -> Set Var
freeVars (TBase b (Predicate x e)) = difference (Expressions.freeVars e) (singleton x)
freeVars (TFun x tx t) = freeVars tx `union` difference (freeVars t) (singleton x)
freeVars (TEx  x tx t) = freeVars tx `union` difference (freeVars t) (singleton x)


{-@ measure boundVars @-}
boundVars :: Type -> Set Var
boundVars (TBase b (Predicate x e)) = Expressions.boundVars e `union` singleton x 
boundVars (TFun x tx t) = boundVars tx `union` boundVars t `union` singleton x
boundVars (TEx  x tx t) = boundVars tx `union` boundVars t `union` singleton x
