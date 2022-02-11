{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local"  @-}

module Substitutions.Environment where 

import Syntax 
import qualified Substitutions.Types       as T
import qualified Expressions as E  
import qualified Substitutions.Expressions as E  
import Environments
import Data.Set 

{-@ inline subable @-}
subable :: Expr -> Env -> Bool 
subable ex g = E.disjoined (boundVars g) (E.freeVars ex)


{-@ reflect subst @-}
{-@ subst :: g:Env -> Var  -> ex:{Expr | subable ex g } 
          -> {o:Env | dom o == dom g} @-}
subst :: Env -> Var -> Expr -> Env 
subst EEmp _ _            = EEmp 
subst (EBind x tx g) y ey = EBind x (T.subst tx y ey) (subst g y ey)  


{-@ ple lookupSubst @-}
{-@ lookupSubst :: g1:Env -> g2:Env -> g3:Env -> x:{Var | member x (dom g1)} 
                -> t:{Type | lookupEnv (eAppend g1 g2) x == t } 
                -> y:Var -> ey:Expr
                -> {lookupEnv (eAppend (subst g1 y ey) g3) x == Substitutions.Types.subst t y ey } @-}
lookupSubst :: Env -> Env -> Env -> Var -> Type -> Var -> Expr -> () 
lookupSubst g1@(EBind x' t' g1') g2 g3 x t y ey 
  | x == x' 
  = ()
  | otherwise
  = lookupSubst g1' g2 g3 x t y ey

