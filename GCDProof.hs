{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--prune-unsorted" @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--total-Haskell" @-}

{-
    THIS DOES NOT WORK YET
-}

module GCDProof where

import Prelude hiding (gcd)
import Language.Haskell.Liquid.ProofCombinators

-- | Definitions

-- definitions of remainder and gcd' were modified from
-- goto.ucsd.edu/~rjhala/liquid/haskell/blog/blog/2013/12/14/gcd.lhs/

{-@ remainder :: a:Nat -> b:{v:Nat| 0 < v} -> {v:Nat | v < b} / [a, b] @-}
remainder :: Int -> Int -> Int
remainder a b
  | a < b = a
  | otherwise = remainder (a - b) b

{-@ reflect remainder @-}

{-@ gcd' :: a:Nat -> b:{v:Nat | v < a} -> Nat / [a,b] @-}
gcd' :: Int -> Int -> Int
gcd' a b
    | b == 0    = a
    | otherwise = gcd' b (remainder a b)

{-@ reflect gcd' @-}

{-@ gcd :: a:Nat -> b:Nat -> Nat / [a, b] @-}
gcd :: Int -> Int -> Int
gcd a b
    | a < b     = gcd' b a
    | a > b     = gcd' a b
    | otherwise = a

{-@ reflect gcd @-}

-- | Propositions

{-@ type GCDCongruence = i:Nat -> j:Nat -> {i == j => gcd i == gcd j} @-}

-- | TODO
{-@ gcdCongruence :: {true} @-}
gcdCongruence :: Int -> Int -> Proof
gcdCongruence _ _ = trivial *** QED

{-@ type GCDIdempotent = x:Nat -> {gcd x x == x} @-}

{-@ gcdIdem :: GCDIdempotent @-}
gcdIdem :: Int -> Proof
gcdIdem x
    = gcd x x
    *** QED
    
{-@ type GCDCommutative = x:Nat -> y:{Nat | true } -> {gcd x y == gcd y x} @-}

-- | TODO
{-@ gcdComm :: {true} @-}
gcdComm :: Int -> Int -> Proof
gcdComm x y = trivial *** QED
