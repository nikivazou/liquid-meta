{-@ LIQUID "--reflection" @-}

module Expressions where 

import Syntax 

{-@ measure isValue @-}
isValue :: Expr -> Bool 
isValue (EPrim _)  = True 
isValue (ELam _ _) = True 
isValue (EVar _)   = False
isValue (EApp _ _) = False 

{-@ measure isEApp @-}
isEApp :: Expr -> Bool
isEApp (EPrim _)  = False 
isEApp (ELam _ _) = False 
isEApp (EVar _)   = False
isEApp (EApp _ _) = True 
