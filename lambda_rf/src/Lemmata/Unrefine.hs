{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module Lemmata.Unrefine where 

import Syntax
import Propositions
import Environments
import Constants
import Unrefine 
import Expressions
import qualified Expressions as E
import Substitutions.Expressions
import Substitutions.Types

import Data.Set

import Helpers.ProofCombinators 



uwellformed :: UEnv -> Expr -> FType -> HasTypeF -> ()
{-@ uwellformed :: g:UEnv -> e:Expr -> t:FType -> Prop (HasTypeF g e t) 
               -> { intersection (udom g) (E.boundVars e) == empty } @-}
uwellformed _ _ _ (FTLam g x e tx t e_hastype)
  = uwellformed (UEBind x tx g) e t e_hastype 
uwellformed _ _ _ (FTApp g e ex tx t e_hastype ex_hastype_tx) 
  = uwellformed g e (FTFun tx t) e_hastype
  ? uwellformed g ex tx ex_hastype_tx 
uwellformed _ _ _ (FTVar _ _) = () 
uwellformed _ _ _ (FTCon _ _) = () 



{-@ unrefine :: g:Env -> e:Expr -> t:Type 
             -> Prop (HasType g e t)
             -> Prop (HasTypeF (uenv g) e (utype t)) @-}
unrefine :: Env -> Expr -> Type -> HasType -> HasTypeF 
unrefine _ _ _ (TVar g x)
  = ulookup g x ? FTVar (uenv g) x 
unrefine _ _ _ (TApp g e ex t x tx e_hastype_txt ex_hastype_tx)
  = FTApp (uenv g) e ex (utype tx) (utype t) 
      (unrefine g e (TFun x tx t) e_hastype_txt)
      (unrefine g ex tx ex_hastype_tx)
unrefine _ _ _ (TLam g x e tx t e_hastype_t _)
  = FTLam (uenv g) x e (utype tx) (utype t) 
      (unrefine (EBind x tx g) e t e_hastype_t)
unrefine _ _ _ (TCon g p)
  = assert (primUType p == utype (primType p)) 
  ? FTCon (uenv g) p  
unrefine _ _ _ (TSub g e s t e_hastype_s s_issub_t _) 
  = subtyping g s t s_issub_t 
  ? unrefine g e s e_hastype_s   


{-@ subtyping :: g:Env -> s:Type -> t:Type
              -> Prop (IsSubType g s t)
              -> { utype s == utype t } @-}
subtyping :: Env -> Type -> Type -> IsSubType -> () 
subtyping _ _ _ (SBase g b _ _ _) 
  = ()
subtyping _ _ _ (SFun g x sx tx s t tx_issub_sx s_issub_t)
  = subtyping g tx sx tx_issub_sx
  ? subtyping (EBind x tx g) s t s_issub_t 
subtyping _ _ _ (SWit g x tx ex s t ex_hastype_tx s_issub_t)
  = subtyping g s (Substitutions.Types.subst t x ex) s_issub_t
  ? usubst t x ex 
  where 
    t' = Substitutions.Types.subst t x ex
subtyping _ _ _ (SBnd g x sx s t s_issub_t)
  = subtyping (EBind x sx g) s t (s_issub_t)

ulookup :: Env -> Var -> () 
{-@ ulookup :: g:Env -> x:{Var | member x (dom g)} 
            -> { lookupUEnv (uenv g) x == utype (lookupEnv g x) } @-}
ulookup EEmp _          = ()
ulookup (EBind y _ g) x 
  | x == y    = () 
  | otherwise = ulookup g x  


{-@ usubst :: t:Type -> x:Var -> ex:Expr
          -> { utype t == utype (Substitutions.Types.subst t x ex) } @-}
usubst :: Type -> Var -> Expr -> () 
usubst (TBase (TPrim _) (Predicate y _)) x _ |  x == y  
  = ()
usubst (TBase (TPrim _) (Predicate y _)) _ _  
  = () 
usubst (TFun y tx t) x ex | x == y 
  = usubst tx x ex ? usubst t x ex 
usubst (TFun _ tx t) x ex 
  = usubst tx x ex ? usubst t x ex 
usubst (TEx  x tx t) y ex | x == y  
  = usubst tx y ex ? usubst t y ex  
usubst (TEx  x tx t) y ex 
  = usubst tx y ex ? usubst t y ex  