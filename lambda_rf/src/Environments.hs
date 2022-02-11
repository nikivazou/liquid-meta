{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local"  @-}

module Environments where 
import Syntax 
import qualified Types
import Data.Set 

import Helpers.ProofCombinators 

{-@ measure boundVars @-}
boundVars :: Env -> Set Var 
boundVars EEmp = empty 
boundVars (EBind x tx g) = union (Types.boundVars tx) (boundVars g)


{-@ reflect inEnv @-}
inEnv :: Var -> Type -> Env -> Bool 
inEnv _ _  EEmp = False 
inEnv x t (EBind x' t' g)
  = if x == x' && t == t' then True else inEnv x t g 


{-@ reflect lookupEnv @-}
lookupEnv :: Env -> Var -> Type 
{-@ lookupEnv :: g:Env -> {x:Var | member x (dom g)} -> Type  @-} 
lookupEnv (EBind x t g) y
  | x == y = t 
  | otherwise = lookupEnv g y 


{-@ reflect fresh @-}
{-@ fresh :: g:Env -> {x:Var | not (member x (dom g))} @-}
fresh :: Env -> Var 
fresh g = case domList g of 
           [] -> 1 
           xs -> case maxList xs of 
                   (m,ls) -> freshList' m ls  


{-@ reflect domList @-}
{-@ domList :: g:Env -> {v:[Var] | dom g == fromList v } @-}
domList :: Env -> [Var]
domList EEmp          = []
domList (EBind x _ g) = x:domList g 

{-@ reflect freshList' @-}
{-@ freshList' :: x:Int -> xs:[{v:Int | v <= x}] -> {v:Int | v == x+1 && not (member v (fromList xs))}  @-}
freshList' :: Int -> [Int] -> Int 
freshList' x [] = x + 1 
freshList' x (y:ys) = freshList' x ys  


{-@ reflect maxList @-}
maxList :: Ord a => [a] -> (a,[a])
{-@ maxList :: i:{[a] | 0 < len i } -> (m::a, {o:[{v:a | v <= m }] | o == i} )@-}
maxList [x] = (x,[x])
maxList (x:xs) = case maxList xs of 
    (m,ys) -> if m < x then (x,x:ys) else (m,x:ys)


{-@ reflect lookupUEnv @-}
lookupUEnv :: UEnv -> Var -> FType 
{-@ lookupUEnv :: g:UEnv -> y:{Var | member y (udom g)} -> FType  @-} 
lookupUEnv (UEBind x t g) y
  | x == y = t 
  | otherwise = lookupUEnv g y 

{-@ reflect eAppend @-}
eAppend :: Env -> Env -> Env 
{-@ eAppend :: g1:Env -> g2:{Env | intersection (dom g1) (dom g2) == empty } 
            -> {g:Env | dom g == union (dom g1) (dom g2) } @-}
eAppend (EBind x t g1) g2 = EBind x t (eAppend g1 g2)
eAppend EEmp           g  = g 


{-@ ple lookupLemma @-}
lookupLemma :: Env -> Env -> Var -> Type -> () 
{-@ lookupLemma :: g1:Env -> g2:{Env | intersection (dom g1) (dom g2) == empty} 
                -> x:{Var | not (member x (union (dom g1) (dom g2)))} -> tx:Type 
                -> { lookupEnv (eAppend g1 (EBind x tx g2))  x == tx } @-}
lookupLemma EEmp _ _ _ = ()
lookupLemma (EBind y ty g1) g2 x tx | x == y = ()
lookupLemma (EBind y ty g1) g2 x tx | x /= y = lookupLemma g1 g2 x tx 


{-@ ple pullBind @-}
pullBind :: Env -> Env -> Var -> Type -> ()
{-@ pullBind :: g1:Env -> g2:Env -> x:Var -> tx:Type
             -> { EBind x tx (eAppend g1 g2) == eAppend (EBind x tx g1) g2 } @-}
pullBind EEmp g2 _ _ 
  = ()
pullBind (EBind _ _ g1) g2 x tx 
  = pullBind g1 g2 x tx 



{-@ ple lookupNoSubst @-}
{-@ lookupNoSubst :: g1:Env -> g2:Env -> x:{Var | not (member x (dom g1))} 
                -> t:Type 
                -> y:{Var | x /= y} -> ty:{Type | lookupEnv (eAppend g1 (EBind y ty g2)) x == t}
                -> { lookupEnv g2 x == t } @-}
lookupNoSubst :: Env -> Env ->  Var -> Type -> Var -> Type -> () 
lookupNoSubst EEmp g2 x t y _ 
  = ()
lookupNoSubst (EBind _ _ g1) g2 x t y ty
  = lookupNoSubst g1 g2 x t y ty 
