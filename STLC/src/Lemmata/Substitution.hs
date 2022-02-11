{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module Lemmata.Substitution where 

import Syntax 
import Propositions
import Expressions 
import Primitives

import Data.Set 
import Helpers.ProofCombinators

{-@ substitution :: g1:Env -> g2:{Env | intersection (dom g1) (dom g2) == empty} 
                 -> x:{Var | not (Data.Set.member x (union (dom g1) (dom g2)))} 
                 -> ex:{Expr | lc ex } 
                 -> e:{Expr | not (member x (freeVars e))} 
                 -> t:Type -> tx:Type  
                 -> Prop (HasType (eAppend g1 (EBind x tx g2)) (open e (EFVar x)) t)
                 -> Prop (HasType g2 ex tx)
                 -> Prop (HasType (eAppend g1 g2) (open e ex) t) @-}
substitution :: Env -> Env -> Var -> Expr -> Expr -> Type -> Type -> HasType -> HasType -> HasType
substitution g1 g2 x ex e t tx e_hastype_t ex_hastype_tx 
  = substitution_intro e ex x 
  ? substitution_lemma g1 g2 (open e (EFVar x)) ex x t tx ex_hastype_tx e_hastype_t


{-@ substitution_intro :: e:Expr -> ex:Expr 
                       -> x:{Var | not (member x (freeVars e))} 
                       -> { open e ex = subst (open e (EFVar x)) x ex } @-}
substitution_intro :: Expr -> Expr -> Var -> () 
substitution_intro (EApp e1 e2) ex x 
  = substitution_intro e1 ex x ? substitution_intro e2 ex x  
substitution_intro (ELam tx e) ex x
  = substitution_intro' e ex x 1 
substitution_intro (EFVar y) ex x
  = () 
substitution_intro (EBVar y) ex x
  = () 
substitution_intro (EPrim _) ex x
  = () 



{-@ substitution_intro' :: e:Expr -> ex:Expr 
                       -> x:{Var | not (member x (freeVars e))} 
                       -> i:BVar
                       -> { substBound e i ex = subst (substBound e i (EFVar x)) x ex } @-}
substitution_intro' :: Expr -> Expr -> Var -> BVar -> () 
substitution_intro' (EApp e1 e2) ex x i
  = substitution_intro' e1 ex x i ? substitution_intro' e2 ex x i 
substitution_intro' (ELam tx e) ex x i
  = substitution_intro' e ex x (i+1)   
substitution_intro' (EFVar y) ex x i 
  = () 
substitution_intro' (EBVar y) ex x _
  = () 
substitution_intro' (EPrim _) ex x _
  = () 


{-@ substitution_lemma :: g1:Env -> g2:{Env | disjoined (dom g1) (dom g2)  } 
                       -> e:Expr -> ex:{Expr | lc ex} 
                       -> x:{Var | not (member x (dom g1)) && not (member x (dom g2))}
                       -> t:Type -> tx:Type  
                       -> Prop (HasType g2 ex tx)
                       -> Prop (HasType (eAppend g1 (EBind x tx g2)) e t)
                       -> Prop (HasType (eAppend g1 g2) (subst e x ex) t) @-}
substitution_lemma :: Env -> Env -> Expr -> Expr -> Var -> Type -> Type -> HasType -> HasType -> HasType
substitution_lemma g1 g2 _ ex x _ tx ex_hastype_tx (TVar _ y) | x == y 
  = lookupVarSame g1 g2 x tx  
  ? weaken g1 g2 ex tx ex_hastype_tx
substitution_lemma g1 g2 _ ex x _ tx ex_hastype_tx (TVar _ y) 
  = assert (member y (dom (eAppend g1 (EBind x tx g2))))
  ? lookupVarDiff g1 g2 x tx y 
  ? TVar (eAppend g1 g2) y
substitution_lemma g1 g2 _ ex x _ tx ex_hastype_tx (TLam _ e sy s y e_hastype)
  = assert (not (member y (dom (eAppend g1 (EBind x tx g2)))))
  ? substOpen e y x ex 
  ? hasTypeFV g2 ex tx ex_hastype_tx
  ? TLam (eAppend g1 g2) (subst e x ex) sy s y 
         (substitution_lemma (EBind y sy g1) g2 (open e (EFVar y)) ex x s tx ex_hastype_tx e_hastype)
substitution_lemma g1 g2 _ _ _ _ _ _ (TCon _ p)
  = TCon (eAppend g1 g2) p 
substitution_lemma g1 g2 _ ex x _ tx ex_hastype_tx (TApp _ u ux s sx u_hastype ux_hastype)
  = TApp (eAppend g1 g2) (subst u x ex) (subst ux x ex) s sx 
         (substitution_lemma g1 g2 u  ex x (TFun sx s) tx ex_hastype_tx u_hastype )
         (substitution_lemma g1 g2 ux ex x sx          tx ex_hastype_tx ux_hastype)



{-@ substOpen :: e:Expr -> eo:Var -> x:{Var | eo /= x} -> ex:{Expr | lc ex } 
              -> {subst (open e (EFVar eo)) x ex == open (subst e x ex) (EFVar eo)} @-}
substOpen :: Expr -> Var -> Var -> Expr -> () 
substOpen e eo x ex = substOpenBound e 0 eo x ex 

{-@ substOpenBound :: e:Expr -> i:BVar ->  eo:Var 
                   -> x:{Var | x /= eo } 
                   -> ex:{Expr | lc ex } 
                   -> {subst (substBound e i (EFVar eo)) x ex == substBound (subst e x ex) i (EFVar eo)} @-}
substOpenBound :: Expr -> BVar -> Var -> Var -> Expr -> () 
substOpenBound (EApp e1 e2) i ei x ex  
  = substOpenBound e1 i ei x ex  
  ? substOpenBound e2 i ei x ex  
substOpenBound (ELam t e) i ei x ex  
  = substOpenBound e (i+1) ei x ex  
substOpenBound (EFVar y) i ei x ex | y == x
  =   subst (substBound (EFVar y) i (EFVar ei)) x ex 
  === const (subst (EFVar y) x ex) (lc_Id ex i ei)  
  ===  ex 
  === substBound ex i (EFVar ei)
  === substBound (subst (EFVar y) x ex) i (EFVar ei)
  *** QED 
substOpenBound (EFVar y) i ei x ex 
  = () 
substOpenBound (EBVar y) i ei x ex | y == i   
  = ()
substOpenBound (EBVar y) i ei x ex  
  = () 
substOpenBound (EPrim _) i ei x ex  
  = () 


{-@ lc_Id :: e:{Expr | lc e} -> i:BVar -> y:Var 
          -> {substBound e i (EFVar y) == e } @-}
lc_Id :: Expr -> BVar -> Var -> () 
lc_Id e i y = lc_id_at 0 e i y  


{-@ lc_id_at :: k:Nat -> e:{Expr | lc_at k e} -> i:{BVar | i >= k} -> y:Var 
          -> {substBound e i (EFVar y) == e } @-}
lc_id_at :: Int -> Expr -> BVar -> Var -> () 
lc_id_at _ (EBVar _) _ _ = () 
lc_id_at k (ELam _ e) i y = lc_id_at (k+1) e (i+1) y 
lc_id_at _ (EFVar _) _ _ = () 
lc_id_at k (EApp e1 e2) i y = lc_id_at k e1 i y ? lc_id_at k e2 i y 
lc_id_at _ (EPrim _) _ _ = () 

{-@ hasTypeFV :: g:Env -> e:Expr -> t:Type -> Prop (HasType g e t)
              -> { isSubsetOf (freeVars e) (dom g) } @-}
hasTypeFV :: Env -> Expr -> Type -> HasType -> ()
hasTypeFV _ _ _ (TApp g e ex t tx e_hastype ex_hastype) 
  = hasTypeFV g e (TFun tx t) e_hastype
  ? hasTypeFV g ex tx ex_hastype 
hasTypeFV _ _ _ (TLam g e tx t x e_hastype) 
  = hasTypeFV (EBind x tx g) (open e (EFVar x)) t e_hastype
hasTypeFV _ _ _ (TVar _ _) = () 
hasTypeFV _ _ _ (TCon _ _) = () 

{-@ lookupVarSame :: g1:Env -> g2:{Env | disjoined (dom g1) (dom g2) } 
                  -> x:{Var | not (member x (union (dom g1) (dom g2)))} -> tx:Type 
                  -> {lookupEnv (eAppend g1 (EBind x tx g2)) x == tx } @-}
lookupVarSame :: Env -> Env -> Var -> Type -> () 
lookupVarSame EEmp g2 x tx = () 
lookupVarSame (EBind y _ g1) g2 x tx 
  | x == y    = () 
  | otherwise = lookupVarSame g1 g2 x tx 


{-@ lookupVarDiff :: g1:Env -> g2:{Env | disjoined (dom g1) (dom g2)} 
                  -> x:{Var | not (member x (union (dom g1) (dom g2)))} -> tx:Type 
                  -> y:{Var | x /= y && member y (union (dom g1) (dom g2))} 
                  -> {lookupEnv (eAppend g1 (EBind x tx g2)) y == lookupEnv (eAppend g1 g2) y} @-}
lookupVarDiff :: Env -> Env -> Var -> Type -> Var -> () 
lookupVarDiff EEmp _ _ _ _ = ()
lookupVarDiff (EBind z tz g1) g2 x tx y 
  | y == z    = () 
  | otherwise = lookupVarDiff g1 g2 x tx y 


{-@ lookupVarApp :: g1:Env -> g2:{Env | disjoined (dom g1) (dom g2)} 
                  -> x:{Var | not (member x (union (dom g1) (dom g2)))} -> tx:Type 
                  -> y:{Var |  member y (union (dom g1) (dom g2)) } 
                  -> {lookupEnv (eAppend g1 (EBind x tx g2)) y == lookupEnv (eAppend g1 g2) y} @-}
lookupVarApp :: Env -> Env -> Var -> Type -> Var -> () 
lookupVarApp EEmp _ _ _ _ = ()
lookupVarApp (EBind z tz g1) g2 x tx y
  | z == y    = () 
  | otherwise = lookupVarApp g1 g2 x tx y  


{-@ weaken :: g1:Env -> g2:{Env | disjoined (dom g1) (dom g2) }
           -> e:Expr -> t:Type 
           -> Prop (HasType g2 e t)
           -> Prop (HasType (eAppend g1 g2) e t) @-}
weaken :: Env -> Env -> Expr -> Type -> HasType -> HasType 
weaken EEmp g2 e t e_hastype = e_hastype
weaken (EBind y ty g1) g2 e t e_hastype
  = weakening EEmp (eAppend g1 g2) e t y ty 
              (weaken g1 g2 e t e_hastype)


{-@ weakening :: g1:Env -> g2:{Env | disjoined (dom g1) (dom g2) }
              -> e:Expr -> t:Type 
              -> x:{Var | not (member x (dom g1)) && not (member x (dom g2)) } 
              -> tx:Type
              -> dt:Prop (HasType (eAppend g1 g2) e t)
              -> Prop (HasType (eAppend g1 (EBind x tx g2)) e t) / [hasTypeSize dt] @-}
weakening :: Env -> Env -> Expr -> Type -> Var -> Type -> HasType -> HasType 
weakening g1 g2 _ _ y ty (TVar _ x)  
  = assert (member x (dom (eAppend g1 g2)))
  ? lookupVarApp g1 g2 y ty x 
  ? TVar (eAppend g1 (EBind y ty g2)) x 
weakening g1 g2  _ _ x tx (TCon _ p) 
  = TCon (eAppend g1 (EBind x tx g2)) p 
weakening g1 g2 _ _ y ty (TApp _ e ex t tx e_hastype ex_hastype)
  = TApp (eAppend g1 (EBind y ty g2)) e ex t tx 
         (weakening g1 g2 e (TFun tx t) y ty e_hastype)         
         (weakening g1 g2 ex tx y ty ex_hastype)
weakening g1 g2 _ _ y ty (TLam _ e tx t x e_hastype)
  = let z = fresh (union (singleton x) (union (dom (eAppend g1 (EBind y ty g2))) (freeVars e))) in 
      openSubst e x x z ? 
      assert (subst (open e (EFVar x)) x (EFVar z) == open (subst e x (EFVar z)) (EFVar z)) ? 
      assert (eAppend EEmp (EBind x tx (eAppend g1 g2)) == (EBind x tx (eAppend g1 g2))) ? 
      TLam (eAppend g1 (EBind y ty g2)) e tx t z 
           (assertProp (HasType (EBind z tx (eAppend g1 (EBind y ty g2))) 
                                (open e (EFVar z)) t)
             (weakening (EBind z tx g1) g2 (open e (EFVar z)) t y ty 
                (renaming EEmp (eAppend g1 g2) x z tx (open e (EFVar x)) t 
                 (assertProp (HasType (EBind x tx (eAppend g1 g2)) (open e (EFVar x)) t) e_hastype))
           )) 


{-@ openSubst :: e:Expr -> u:Var -> x:Var -> ex:Var 
              -> {subst (open e (EFVar u)) x (EFVar ex) == open (subst e x (EFVar ex) ) (subst (EFVar u) x (EFVar ex) ) } @-}
openSubst :: Expr -> Var -> Var -> Var -> () 
openSubst e u x ex = openSubstBounded e u x ex 0 

{-@ openSubstBounded :: e:Expr -> u:Var -> x:Var -> ex:Var -> i:BVar
              -> {subst (substBound e i (EFVar u)) x (EFVar ex) == substBound (subst e x (EFVar ex)) i (subst (EFVar u) x (EFVar ex) ) } @-}
openSubstBounded :: Expr -> Var -> Var -> Var -> BVar -> () 
openSubstBounded (EApp e1 e2) u x ex i 
  = openSubstBounded e1 u x ex i 
  ? openSubstBounded e2 u x ex i 
openSubstBounded (ELam t e) u x ex i 
  = openSubstBounded e u x ex (i+1) 
openSubstBounded (EFVar _) _ _ _ _ 
  = () 
openSubstBounded (EBVar _) _ _ _ _ 
  = () 
openSubstBounded (EPrim _) _ _ _ _
  =  () 

{-@ type HasTypeN N G E T = {p:HasType |  prop p = HasType G E T && hasTypeSize p == N } @-}
{-@ renaming :: g1:Env -> g2:{Env | disjoined (dom g1) (dom g2)} 
             -> x:{Var | not (member x (dom g1)) && not (member x (dom g2))} 
             -> y:{Var | x /= y && not (member y (dom g1)) && not (member y (dom g2))} 
             -> tx:Type -> e:Expr -> t:Type 
             -> dt:Prop (HasType (eAppend g1 (EBind x tx g2)) e t)
             -> HasTypeN (hasTypeSize dt) (eAppend g1 (EBind y tx g2)) (subst e x (EFVar y)) t  
             / [hasTypeSize dt] @-}
renaming :: Env -> Env -> Var -> Var -> Type -> Expr -> Type -> HasType -> HasType 
renaming g1 g2 x y tx _ _ (TApp _ e ex s sx e_hastype ex_hastype) 
  = TApp (eAppend g1 (EBind y tx g2)) (subst e x (EFVar y)) (subst ex x (EFVar y)) s sx 
       (renaming g1 g2 x y tx e (TFun sx s) e_hastype)
       (renaming g1 g2 x y tx ex sx ex_hastype)
renaming g1 g2 x y tx _ _ (TLam _ e sx s z e_hastype)
  = let w = fresh (union (singleton y) 
                  (union (singleton z) 
                  (union (dom (eAppend g1 (EBind x tx g2))) (freeVars e)))) in
    assert (disjoined (dom g1) (dom (EBind y tx g2))) ? 
    assert (eAppend (EBind w sx g1) (EBind y tx g2) == EBind w sx (eAppend g1 (EBind y tx g2))) ? 
    assert (EBind w sx (eAppend g1 (EBind x tx g2)) == eAppend EEmp (EBind w sx (eAppend g1 (EBind x tx g2)))) ? 
    openSubst e z z w ?
    assert (subst (open e (EFVar z)) z (EFVar w) == open (subst e z (EFVar w)) (subst (EFVar z) z (EFVar w))) ? 
    assert (subst e z (EFVar w) == e) ? 
    assert (open e (EFVar w) == subst (open e (EFVar z)) z (EFVar w)) ?
    openSubst e w x y ?
    assert (subst (open e (EFVar w)) x (EFVar y) == open (subst e x (EFVar y)) (subst (EFVar w) x (EFVar y) )) ? 
    assert (open (subst e x (EFVar y)) (EFVar w) == subst (open e (EFVar w)) x (EFVar y)) ? 
    TLam (eAppend g1 (EBind y tx g2)) e' sx s w (
        assertProp (
          HasType (EBind w sx (eAppend g1 (EBind y tx g2))) (open e' (EFVar w)) s) (
            renaming (EBind w sx g1) g2 x y tx (open e (EFVar w)) s  (
           assertProp (HasType (EBind w sx (eAppend g1 (EBind x tx g2))) (open e (EFVar w)) s) (
           assertProp (HasType (eAppend EEmp (EBind w sx (eAppend g1 (EBind x tx g2)))) 
                                (subst (open e (EFVar z)) z (EFVar w)) s) (
            renaming EEmp (eAppend g1 (EBind x tx g2)) z w sx (open e (EFVar z)) s 
           (assertProp (
          HasType (EBind z sx (eAppend g1 (EBind x tx g2))) (open e (EFVar z)) s) e_hastype) 
         )))
        ))
    where e' = subst e x (EFVar y)    
renaming g1 g2 x y tx _ _ (TVar _ z) | x == z 
  = assert (not (member z (union (dom g1) (dom g2))))
  ? lookupVarSame g1 g2 x tx 
  ? lookupVarSame g1 g2 y tx 
  ? TVar (eAppend g1 (EBind y tx g2)) y 
renaming g1 g2 x y tx _ _ (TVar _ z) 
  = assert (member z (dom (eAppend g1 (EBind x tx g2))))
  ? assert (member z (dom (eAppend g1 (EBind y tx g2))))
  ? lookupVarDiff g1 g2 x tx z 
  ? lookupVarDiff g1 g2 y tx z 
  ? TVar (eAppend g1 (EBind y tx g2)) z
renaming g1 g2 x y tx _ _ (TCon _ p)
  = TCon (eAppend g1 (EBind y tx g2)) p  


fresh :: Set Int  -> Int 
{-@ fresh :: s:Set Int -> {x:Int | not (member x s)} @-}
fresh s = freshI (toList s) 0 [] 

{-@ freshI :: xs:[Int] -> j:Int -> old:[{v:Int |  v < j}]
           -> {i:Int | not (member i (listElts xs)) && not (member i (listElts old)) } @-} 
freshI :: [Int]  -> Int -> [Int] -> Int 
freshI js i old 
  = if i `isElem` js then freshI (remove i js) (i+1) (i:old) else const i (lessNoMem i old) 

{-@ lessNoMem :: i:Int -> is:[{v:Int | v < i}] -> {not (member i (listElts is))} @-}
lessNoMem :: Int -> [Int] -> () 
lessNoMem _ []     = () 
lessNoMem i (_:is) = lessNoMem i is 

{-@ remove :: i:Int 
           -> js:[Int]
           -> {o:[Int] | (if (member i (listElts js)) then (len o < len js) else (len o == len js)) && listElts o == difference (listElts js) (singleton i) } @-}
remove :: Int -> [Int] -> [Int]
remove _ [] = [] 
remove i (j:js) = if i == j then remove i js else j:remove i js 

isElem :: Int -> [Int] -> Bool
{-@ isElem :: i:Int -> is:[Int] -> {b:Bool | b <=> member i (listElts is)} @-}
isElem i []     = False
isElem i (j:js) = if i == j then True else isElem i js 