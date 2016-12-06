{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--prune-unsorted" @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--total-Haskell" @-}

module TakeMaxCycleZip where

import Prelude hiding (gcd)
import Language.Haskell.Liquid.ProofCombinators

{-@ todo :: {true} @-}
todo = trivial *** QED

-- | Mod and Divides ---------------------------------------------------------

{-@ type NonZeroNat = {v:Nat | v /= 0} @-}

-- definition of remainder was modified from the definition of mod found at
-- goto.ucsd.edu/~rjhala/liquid/haskell/blog/blog/2013/12/14/gcd.lhs/

{-@ remainder :: x:Nat -> y:NonZeroNat -> {v:Nat | v < y} / [x, y] @-}
remainder :: Int -> Int -> Int
remainder x y
    | x < y = x
    | otherwise = remainder (x - y) y

{-@ reflect remainder @-}

{-@ predicate Divides Y X = remainder X Y == 0 @-}

-- | Cycle Zip ---------------------------------------------------------------

-- define a notion of infinity
{-@ measure inf :: Int @-}
{-@ invariant {v:Int | v < inf} @-}

-- cycle produces an infinite list
{-@ cycle ::
    {v:[a] | (len v) > 0 } ->
    {v:[a] | (len v) = inf }
@-}

-- zip up two lists by repeating their elements over and over
{-@ cycleZip ::
    {v:[a]     | (len v) > 0 } ->
    {v:[b]     | (len v) > 0 } ->
    {v:[(a,b)] | (len v) = inf }
@-}
cycleZip :: [a] -> [b] -> [(a,b)]
cycleZip x y = zip (cycle x) (cycle y)

-- | Taking from Cycle Zip ---------------------------------------------------

-- if `take n` acts on an infinite list, then the output is always of length n
{-@ take :: n:Int -> l:[a] -> {v:[a] | (len l == inf) ==> (len v == n) } @-}


-- | In R, a binary operation can only "safely" lift to act on different
-- | non-empty containers if the min length divides the max length.
-- | E.g., these are fine
-- |    c(1,2) * c(3,4,5,6) --> c(3,8,5,12)
-- |    c(3,3,3) * c(2,1,2) --> c(6,3,6)
-- | But these are warnings:
-- |    c(1,2) * c(3,2,1) --> c(3 4 1)
-- |    c(1,2,3,4,5,6,7) * c(1,2,3,4,5) --> 1  4  9 16 25  6 14

{-@ predicate ValidInputLists A B
        = Divdes (len A) (len B) || Divides (len B) (len A)
@-}

-- | TODO: this.

{-@ takeLcmCycleZip ::
    x:{v:[a]   | (len v) > 0 } ->
    y:{v:[b]   | (len v) > 0 } ->
    {v:[(a,b)] | (len v) = lcmLH (len x) (len y) }
@-}
takeLcmCycleZip :: [a] -> [b] -> [(a,b)]
takeLcmCycleZip x y = take (lcm (length x) (length y)) $ cycleZip x y













