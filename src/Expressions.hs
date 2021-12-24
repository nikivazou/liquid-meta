module Expressions where 

import Syntax 
import Data.Set 

{-@ measure freeVars @-}
freeVars :: Expr -> Set Var 
freeVars (EApp e1 e2) = freeVars e1 `union` freeVars e2
freeVars (ELam x e)   = difference (freeVars e) (singleton x)
freeVars (EVar x)     = singleton x 
freeVars (EPrim _)    = empty

isValue :: Expr -> Bool 
{-@ measure isValue @-}
isValue (EApp _ _) = False 
isValue (ELam _ _) = True 
isValue (EVar _)   = False 
isValue (EPrim _)  = True 