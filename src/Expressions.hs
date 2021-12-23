module Expressions where 

import Syntax 

isValue :: Expr -> Bool 
{-@ measure isValue @-}
isValue (EApp _ _) = False 
isValue (ELam _ _) = True 
isValue (EVar _)   = False 
isValue (EPrim _)  = True 