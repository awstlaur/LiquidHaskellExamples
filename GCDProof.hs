{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--prune-unsorted" @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--total-Haskell" @-}

module GCDProof where

import Prelude hiding (gcd)
import Language.Haskell.Liquid.ProofCombinators

{-@ todo :: {true} @-}
todo = trivial *** QED

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

-- | Propositions ------------------------------------------------------------

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

-- | Division is important in number theory!
{-@ predicate Divides Y X = remainder X Y == 0 @-}

{-@ type DividesImpliesGCD =
    x:Nat -> y:NonZeroNat -> {Divides y x => gcd x y == y}
@-}

-- | In order to write a proof of type DividesImpliesGCD,
-- | first we'll establish a couple lemmas.

-- | Lemma: If y divides x, and x is strictly smaller than y,
-- | then x must be zero.
{-@ dividesSmallerImpliesZero ::
    x:Nat -> y:NonZeroNat -> {x < y && Divides y x => x == 0}
@-}
dividesSmallerImpliesZero :: Int -> Int -> Proof
dividesSmallerImpliesZero x y
    = remainder x y             -- | Liquid Haskell unfolds this for us
    *** QED

-- | Lemma: Essentially the thing we want to prove, just for gcd' x y.
{-@ dividesImpliesGCD' ::
    x:Nat -> y:{v:NonZeroNat | v < x} -> {Divides y x => gcd' x y == y}
@-}
dividesImpliesGCD' :: Int -> Int -> Proof
dividesImpliesGCD' x y
    =   gcd' x y
    ==. gcd' y (remainder x y)
    ==. gcd' y 0                -- | Because y divides x
    ==. y
    *** QED

-- | Onto the main show! Each non-trivial case will use a Lemma.
{-@ dividesImpliesGCD :: DividesImpliesGCD @-}
dividesImpliesGCD x y
    | x < y
    =   gcd  x y
    ==. gcd' y x
    ==. gcd' y 0                ? dividesSmallerImpliesZero x y
    ==. y
    *** QED

    | x > y
    =   gcd  x y
    ==. gcd' x y
    ==. y                       ? dividesImpliesGCD' x y
    *** QED

    | otherwise
    = gcd x y
    ==. x
    *** QED

-- | Now let's go the other way.
{-@ type GCDImpliesDivides =
        x:Nat -> y:{v:NonZeroNat | v < x} -> {gcd' x y == y => Divides y x}
@-}

-- | TODO: figure this out!
{-@ gcdImpliesDivides :: {true} @-}
gcdImpliesDivides :: Int -> Int -> Proof
gcdImpliesDivides x y = todo
    -- =   y
    -- ==. gcd' x y
    -- ==. gcd' y (remainder x y)
    -- ==. gcd' y 0
    -- ==. y
    -- *** QED

-- | As a corollary, for POSITIVE Nats,
-- | y divides x if and only if gcd x y equals y.
{-@ type GCDIffDivides =
    x:NonZeroNat -> y:NonZeroNat -> {Divides y x <=> gcd x y == y}
@-}

{-@ gcdIffDivides :: {true} @-}
gcdIffDivides :: Int -> Int -> Proof
gcdIffDivides x y = todo

-- | More interesting stuff --------------------------------------------------

{-@ type GCDDivides = x:Nat -> y:Nat -> {Divides (gcd x y) x} @-}

{-@ gcdDivides :: {true} @-}
gcdDivides :: Int -> Int -> Proof
gcdDivides x y = todo

{-@ type GCDAssociative =
    x:Nat -> y:Nat -> z:Nat -> {gcd x (gcd y z) == gcd (gcd x y) z}
@-}

{-@ gcdAssociative :: {true} @-}
gcdAssociative :: Int -> Int -> Int -> Proof
gcdAssociative x y z = todo
