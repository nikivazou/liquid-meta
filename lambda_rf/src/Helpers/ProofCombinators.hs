module Helpers.ProofCombinators where 

infixl 3 ?
{-@ (?) :: forall <p :: a -> Bool> . a<p> -> b -> b @-}
(?) :: a -> b -> b 
x ? y = y 


infixl 3 ===
{-@ (===) :: x:a -> y:{a | x == y} -> {v:a | v == x && v == y } @-}
(===) :: a -> a -> a 
x === y = y 

infixl 3 ***
data QED = QED 
x *** QED = () 

assert :: Bool -> ()
{-@ assert :: {b:Bool | b } -> {b} @-} 
assert _ = () 

assume :: Bool -> ()
{-@ assume assume :: b:Bool -> {b} @-} 
assume _ = () 

use :: Bool -> () -> Bool 

{-@ assume use :: b:Bool -> {v:() | b} -> {r:Bool | r} @-}
use x _ = x 

infixl 3 ??
(??) :: a -> b -> a 
(??) x _ = x 

