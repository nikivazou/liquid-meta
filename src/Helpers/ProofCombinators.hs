module Helpers.ProofCombinators where 

{-@ (?) :: forall <p :: a -> Bool> . a<p> -> b -> b @-}
(?) :: a -> b -> b 
x ? y = y 


{-@ (===) :: x:a -> y:{a | x == y} -> a @-}
(===) :: a -> a -> a 
x === y = y 

data QED = QED 
x *** QED = x 

assert :: Bool -> ()
{-@ assert :: {b:Bool | b } -> {b} @-} 
assert _ = () 



