{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--prune-unsorted" @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--total-Haskell" @-}

module REMProof where

import Prelude hiding(gcd)
import Language.Haskell.Liquid.ProofCombinators

{-@ type NonZeroNat = {v:Nat | v /= 0} @-}

{-@ remainder :: x:Nat -> y:NonZeroNat -> Nat / [x, y] @-}
remainder :: Int -> Int -> Int
remainder x y | x > y     = remainder (x - y) y
              | otherwise = x

{-@ reflect remainder @-}

{-@ remNonincreasing :: x:Nat -> y:NonZeroNat -> {remainder x y <= x} @-}
remNonincreasing :: Int -> Int -> Proof
remNonincreasing x y
    | x > y
    = remainder x y
    <=. (x - y)         ∵ remNonincreasing (x - y) y
    *** QED

    | otherwise
    = remainder x y
    *** QED

{-@ remDecreasing :: x:Nat -> y:{y:NonZeroNat | x > y} -> {remainder x y < x} @-}
remDecreasing :: Int -> Int -> Proof
remDecreasing x y
    = remainder x y
    <=.  (x - y)         ∵ remNonincreasing (x - y) y
    *** QED

{-@ gcd :: a:Nat -> b:Nat -> Nat @-}
gcd  :: Int -> Int -> Int
gcd  x y | x == 0    = y
         | y == 0    = x
         | x == y    = x
         | x > y     = gcd (remainder x y) y
         | x < y     = gcd x (remainder y x)
         | otherwise = 0

{-@ reflect gcd @-}
