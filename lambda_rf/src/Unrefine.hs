{-@ LIQUID "--reflection" @-}
module Unrefine where 
import Syntax 

{-@ reflect utype @-}
utype :: Type -> FType 
utype (TBase (TPrim p) _) = FTBase p 
utype (TFun _ t1 t2)      = FTFun (utype t1) (utype t2) 
utype (TEx  _ _  t)       = utype t  

{-@ reflect uenv @-}
{-@ uenv :: g:Env -> {u:UEnv | udom u == dom g } @-} 
uenv :: Env -> UEnv 
uenv EEmp = UEEmp
uenv (EBind x t e) = UEBind x (utype t) (uenv e) 


              