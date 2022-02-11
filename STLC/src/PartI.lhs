> module PartI where 
> import Data.Set 




Refinements On Data Types: from safe indexing to metatheory
------------------------------------------------------------
by Niki Vazou, IMDEA
at FP-Talk, Chalmers 
 








Goal: Metatheory in Liquid Haskell 
----------------------------------

Part I:  Liquid Haskell Overview 
Part II: Liquid Haskell Novel Feature 






What is Liquid Haskell?
-----------------------

Liquid Haskell: Refinement Type Checker for Haskell

Haskell Type: `Int` 
Refined Type: `{i:Int | 0 /= i}`



Why? 

 {-@ test :: {i:Int | 0 /= i} -> Int @-} 
 test :: Int -> Int  

 test i = 42 `div` i






Liquid Haskell's Refined Types 
-------------------------------

`{v:a | p}`

`p` containts: 
  - SMT decidable theories: boolean, equality, linear arithmetic, sets,... 
     e.g., `{v:Bool | false }`
  - variables, e.g., `x:Int -> {v:Int | x < v }`
  - some Haskell functions (namely: `measures` & `reflect`) 





Measures: Functions on one ADT 
-------------------------------

> data Map k v = MEmp | MBind k v (Map k v)

> {-@ measure msize @-} 
> {-@ msize :: Map k v -> {i:Int | 0 <= i } @-} 
> msize :: Map k v -> Int 
> msize MEmp          = 0 
> msize (MBind _ _ g) = 1 + msize g 




Reasoning on Measures is Fully Automatic! 
------------------------------------------

> {-@ testMap :: {g:Map Int Int | msize g = 3 } @-}
> testMap :: Map Int Int 
> testMap = MBind 1 1 (MBind 2 2 (MBind 3 3 MEmp))


> {-@ mhead :: g:{Map k v | 0 < msize g} -> (k,v) @-}
> mhead :: Map k v -> (k,v)
> mhead (MBind k v _) = (k,v)






Measures for automatic "light" verification  
--------------------------------------------

+ Fully automatic Verification 

- Small expressiveness

□ Application: Remove runtime indexing checks, 
               e.g., lists, Bytestring, ...





Multiple Measures
-----------------

  data Map k v = EEmp | MBind k v (Map k v)

> {-@ measure keys @-} 
> keys :: Ord k => Map k v -> Set k  
> keys MEmp          = empty 
> keys (MBind k _ g) = union (singleton k) (keys g) 



> mAppend :: Ord k => Map k v -> Map k v -> Map k v 
> {-@ mAppend :: Ord k => m1:Map k v -> m2:Map k v 
>             -> {m:Map k v | keys m == union (keys m1) (keys m2)} @-}
> mAppend MEmp           m2 = m2 
> mAppend (MBind k v m1) m2 = MBind k v (mAppend m1 m2)






Measures for Data Invariants
----------------------------

Invariant: "A type environment is unique-key map."

> data Env = EEmp | EBind Var Type Env 
> {-@ data Env = EEmp 
>              | EBind { eVar  :: Var 
>                      , eType :: Type
>                      , eTail :: {g:Env | not (member eVar (dom g))} 
>                      } @-}



> envTest :: Env 
> envTest = EBind xx tInt (EBind yy tBool EEmp)






Every `Env` should satisfy these invariants!  
--------------------------------------------

> {-@ ignore eAppend @-}
> {-@ eAppend :: g1:Env -> g2:Env 
>             -> {g:Env | dom g == union (dom g1) (dom g2) } @-} 
> eAppend :: Env -> Env -> Env 
> eAppend EEmp           g2 = g2 
> eAppend (EBind x t g1) g2 = EBind x t (eAppend g1 g2)


Q: Can we put `eAppend` in the refinements? 
A: No! 

 {-@ emptyAppend :: {eAppend EEmp EEmp = EEmp} @-}

> emptyAppend :: () 
> emptyAppend = () 


 {-@ reflect eAppend       @-}
 {-@ LIQUID "--reflection" @-}



 {-@ LIQUID "--ple"        @-}




What else can you prove about reflected functions?
------------------------------------------------

Quite Interesting Theorems! 






\dontbegin{code}
  {-@ lookupVarDiff :: g1:Env -> g2:{Env | disjoined (dom g1) (dom g2)} 
                    -> x:{Var | not (member x (union (dom g1) (dom g2)))} 
                    -> tx:Type 
                    -> y:{Var | x /= y && member y (union (dom g1) (dom g2))} 
                    -> {  lookupEnv (eAppend g1 (EBind x tx g2)) y
                       == lookupEnv (eAppend g1             g2)  y } @-}
  lookupVarDiff :: Env -> Env -> Var -> Type -> Var -> () 
  lookupVarDiff EEmp _ _ _ _ = ()
  lookupVarDiff (EBind z _ g1) g2 x tx y 
    | y == z    = () 
    | otherwise = lookupVarDiff g1 g2 x tx y 
\dontend{code}




How interesting? Let's prove metatheory!
----------------------------------------

Soundness: "Well Typed Programs cannot get stuck." 

If eo:t and eo ->* e, then 
- isValue e _or_
- ∃e', e -> e'.  





Metatheory in Liquid Haskell: Naïve Attempt 
--------------------------------------------

Step 1: Define reflected functions for hasType, step, etc. 
Step 2: Encode Soundness as a Refinement Type 
Step 3: Prove it!   





Step 1: Define reflected functions for hasType, step, etc. 
----------------------------------------------------------

hasType  :: Env -> Expr -> Type 
isValue  :: Expr -> Bool 
step     :: Expr -> Expr 
eval     :: Expr -> Expr 


Problem: `eval` (the transitive closure of step)
         cannot be defined as a terminating function! 
Solution: Inductive Predicates! (Part II)





Part I: Summary
----------------

- Measures: Functions on one ADT 
   - verification: fully automatic
   - proved: Safe Indexing on Bytestring 

- Reflects: Terminating Haskell functions 
   - verification: explicit proofs
   - proved: Non interference of LIO (5447 Loc)

- Next Goal: Prove Soundness! 










> {-@ reflect lookupEnv @-}
> {-@ lookupEnv :: g:Env -> {x:Var | member x (dom g)} -> Type @-}
> lookupEnv :: Env -> Var -> Type 
> lookupEnv (EBind y ty g) x
>    | x == y = ty 
>    | otherwise = lookupEnv g x






> {-@ measure dom @-}
> dom :: Env -> Set Var 
> dom EEmp = empty 
> dom (EBind x _ g) = singleton x `union` dom g


> {-@ inline disjoined @-}
> disjoined :: Ord a => Set a -> Set a -> Bool 
> disjoined s1 s2 = intersection s1 s2 == empty 

> type Var  = Int 
> data Type = Type  

> -- Some types 
> tInt, tBool :: Type 
> tInt  = Type 
> tBool = Type 

> -- Some variables 
> {-@ reflect xx @-}
> {-@ reflect yy @-}
> {-@ reflect zz @-}
> xx, yy, zz :: Var 
> xx = 1 
> yy = 2 
> zz = 3 


