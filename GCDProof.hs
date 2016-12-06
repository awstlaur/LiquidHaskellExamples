{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--prune-unsorted" @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--total-Haskell" @-}

module GCDProof where

import Prelude hiding (gcd)
import Language.Haskell.Liquid.ProofCombinators

-- | Definitions -------------------------------------------------------------

{-@ type NonZeroNat = {v:Nat | v /= 0} @-}

-- definitions of remainder and gcd' were modified from
-- the definitions of mod and gcd (respectively) found at
-- goto.ucsd.edu/~rjhala/liquid/haskell/blog/blog/2013/12/14/gcd.lhs/

{-@ remainder :: x:Nat -> y:NonZeroNat -> {v:Nat | v < y} / [x, y] @-}
remainder :: Int -> Int -> Int
remainder x y
    | x < y = x
    | otherwise = remainder (x - y) y

{-@ reflect remainder @-}

{-@ gcd' :: x:Nat -> y:{v:Nat | v < x} -> NonZeroNat / [x, y] @-}
gcd' :: Int -> Int -> Int
gcd' x y
    | y == 0    = x
    | otherwise = gcd' y (remainder x y)

{-@ reflect gcd' @-}

{-@ gcd :: x:Nat -> y:Nat -> Nat / [x, y] @-}
gcd :: Int -> Int -> Int
gcd x y
    | x < y     = gcd' y x
    | x > y     = gcd' x y
    | otherwise = x

{-@ reflect gcd @-}

-- | Simple Propositions -------------------------------------------------------

{-@ type GCDCongruence =
    x0:Nat -> y0:Nat -> x1:Nat -> y1:Nat -> 
        {x0 == x1 && y0 == y1 => gcd x0 y0 == gcd x1 y1} 
@-}

-- | LiquidHaskell can derive this for uninterpreted functions!
{-@ gcdCongruence :: GCDCongruence @-}
gcdCongruence :: Int -> Int -> Int -> Int -> Proof
gcdCongruence _ _ _ _ = trivial *** QED

{-@ type GCDIdempotent = x:Nat -> {gcd x x == x} @-}

-- | LiquidHaskell knows that this hits the `otherwise` case!
{-@ gcdIdempotent :: GCDIdempotent @-}
gcdIdempotent :: Int -> Proof
gcdIdempotent x
    = gcd x x
    *** QED

{-@ type GCDCommutative = x:Nat -> y:Nat -> {gcd x y == gcd y x} @-}

-- | Our symmetric definition makes this easy!
{-@ gcdCommutative :: GCDCommutative @-}
gcdCommutative :: Int -> Int -> Proof
gcdCommutative x y
    =   gcd  x y
    ==. gcd  y x
    *** QED

-- | More Interesting Propositions ---------------------------------------------

{-@ predicate Divides Y X = remainder X Y == 0 @-}

{-@ dividesImpliesGCD' ::
    x:Nat -> y:{v:NonZeroNat | v < x} -> {Divides y x => gcd' x y == y}
@-}
dividesImpliesGCD' :: Int -> Int -> Proof
dividesImpliesGCD' x y
    =   gcd' x y
    ==. gcd' y (remainder x y)
    ==. gcd' y 0
    ==. y
    *** QED

{-@ type DividesImpliesGCD =
    x:Nat -> y:{v:NonZeroNat | v < x} -> {Divides y x => gcd x y == y}
@-}

{-@ dividesImpliesGCD :: DividesImpliesGCD @-}
dividesImpliesGCD x y
    =   gcd x y
    ==. y           ? dividesImpliesGCD' x y
    *** QED

-- | TODO: Prove this.
{-@ type GCDDivides = x:Nat -> y:Nat -> {Divides (gcd x y) x} @-}

-- {-@ gcdDivides :: GCDDivides @-}
-- gcdDivides :: Int -> Int -> Proof
-- gcdDivides x y = trivial *** QED

-- | TODO: Prove this.
{-@ type GCDAssociative =
    x:Nat -> y:Nat -> z:Nat -> {gcd x (gcd y z) == gcd (gcd x y) z}
@-}
