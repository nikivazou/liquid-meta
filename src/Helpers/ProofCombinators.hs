module Helpers.ProofCombinators where 

x ? y = y 

assert :: Bool -> ()
{-@ assert :: {b:Bool | b } -> {b} @-} 
assert _ = () 



