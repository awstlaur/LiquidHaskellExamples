{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--prune-unsorted" @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--total-Haskell" @-}

module REMProof where

import Prelude
import Language.Haskell.Liquid.ProofCombinators

{-@ type NonZeroNat = {v:Nat | v /= 0} @-}

{-@ remainder :: Nat -> NonZeroNat -> Nat @-}
remainder :: Int -> Int -> Int
remainder x y | x == 0    = 0
              | x > y     = remainder (x - y) y
              | otherwise = x

{-@ reflect remainder @-}

{-@ type RemDecreases = x:Nat -> y:NonZeroNat -> {remainder x y <= x} @-}

{-@ remDecreases :: RemDecreases @-}
remDecreases :: Int -> Int -> Proof
remDecreases x y
    | x == 0
    = remainder 0 y
    ==. 0
    <.  0
    *** QED
    
    | x > y
    = remainder x y
    ==. remainder (x - y) y
    <.  (x - y)             ∵ remDecreases (x - y) y
    <.  x
    *** QED
    
    | otherwise
    = remainder x y
    ==. x
    <.  x
    *** QED

{-@ predicate Divides x y = (rem x y == 0) @-}


