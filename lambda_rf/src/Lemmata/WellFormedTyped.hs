{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module Lemmata.WellFormedTyped where 

import Syntax
import Environments
import Substitutions.Expressions 
import Unrefine
import Propositions
import qualified Lemmata.Weakening 
import Data.Set 
import qualified WellFormed

typed :: Env -> Expr -> Type -> WellFormedEnv -> HasType -> IsWellFormed
{-@ typed :: g:Env -> e:Expr -> t:Type 
          -> Prop (WellFormedEnv g)
          -> Prop (HasType g e t) 
          -> Prop (IsWellFormed g t) @-}
typed = WellFormed.typed 

