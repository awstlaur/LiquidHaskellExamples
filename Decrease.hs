{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--prune-unsorted" @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--total-Haskell" @-}

module Decrease where

import Language.Haskell.Liquid.ProofCombinators

{-@ type NonZeroNat = {v:Nat | v /= 0} @-}

{-@ subtract1 :: NonZeroNat -> Nat @-}
subtract1 :: Int -> Int
subtract1 x  = x - 1

{-@ reflect subtract1 @-}

{-@ subtract1IsMinus1 :: x:NonZeroNat -> {subtract1 x == x - 1} @-}
subtract1IsMinus1 :: Int -> Proof
subtract1IsMinus1 x
    = subtract1 x
    *** QED

{-@ recur :: x:NonZeroNat -> Nat / [x] @-}
recur :: Int -> Int
recur x | x == 1    = 0
        | otherwise = recur (x - 1) + 1

{-@ reflect recur @-}

{-@ recurIsMinus1 :: x:NonZeroNat -> {recur x == x - 1} @-}
recurIsMinus1 :: Int -> Proof
recurIsMinus1 x
    | x == 1
    = recur 1
    *** QED
    
    | otherwise
    =   recur x
    ==. recur (x - 1) + 1
    ==. ((x - 1) - 1) + 1   ∵ recurIsMinus1 (x - 1)
    *** QED
    
{-@ recurIsSubtract1 :: x:NonZeroNat -> {recur x == subtract1 x} @-}
recurIsSubtract1 :: Int -> Proof
recurIsSubtract1 x
    = recur x
    ==. x - 1               ∵ recurIsMinus1 x
    ==. subtract1 x         ∵ subtract1IsMinus1 x
    *** QED
