{-@ LIQUID "--reflection" @-}

module Substitutions.Types where 

import Syntax 

{-@ reflect subst @-}
subst :: Type -> Var -> Expr -> Type 
subst t _ _ = t 