{-@ LIQUID "--reflection" @-}

module Constants where 

import Syntax 
import Types 

{-@ measure delta :: EPrim -> Expr -> Expr @-}
{-@ delta :: p:EPrim -> e:Expr -> {r:Expr | r = delta p e } @-}
delta :: EPrim -> Expr -> Expr 
delta _ e = undefined 
