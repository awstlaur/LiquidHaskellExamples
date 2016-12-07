{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--prune-unsorted" @-}
{-@ LIQUID "--totality"       @-}
{-@ LIQUID "--total-Haskell"  @-}

module TakeMaxCycleZip where

import Prelude hiding (max)

import Language.Haskell.Liquid.Prelude(safeZipWith)
import Language.Haskell.Liquid.ProofCombinators

-- | General Types ----------------------------------------------------------

{-@ type NonZeroNat     = {v:Nat | v /= 0}      @-}

{-@ type NonEmptyList a = {v:[a] | (len v) > 0} @-}

{-@ type ListN a N      = {v:[a] | len v == N}  @-}

-- | Remainder, Divides, Max -------------------------------------------------

-- definition of remainder was modified from the definition of mod found at
-- goto.ucsd.edu/~rjhala/liquid/haskell/blog/blog/2013/12/14/gcd.lhs/
{-@ remainder :: x:Nat -> y:NonZeroNat -> {v:Nat | v < y} / [x, y] @-}
remainder :: Int -> Int -> Int
remainder x y
    | x < y = x
    | otherwise = remainder (x - y) y

{-@ reflect remainder @-}

{-@ max :: x:Int -> y:Int -> {v:Int | x == v || y == v} / [x, y] @-}
max :: Int -> Int -> Int
max x y
    | x > y     = x
    | otherwise = y

{-@ reflect max @-}

-- | Cycle Zip ---------------------------------------------------------------

-- define a notion of infinity
{-@ measure inf :: Int @-}
{-@ invariant {v:Int | v < inf} @-}

-- cycle produces an infinite list
{-@ cycle ::
        {v:[a] | (len v) > 0 } -> {v:[a] | (len v) = inf }
@-}

-- zip up two lists by repeating their elements over and over
{-@ cycleZip ::
        NonEmptyList a -> NonEmptyList b -> {v:[(a,b)] | (len v) = inf }
@-}
cycleZip :: [a] -> [b] -> [(a,b)]
cycleZip x y = safeZipWith (,) (cycle x) (cycle y)

-- | Taking from Cycle Zip ---------------------------------------------------

-- | In R, a binary operation can only "safely" lift to act on different
-- | non-empty containers if the min length divides the max length.
-- | E.g., these are fine
-- |    c(1,2) * c(3,4,5,6)             --> 3 8 5 12
-- |    c(3,3,3) * c(2,1,2)             --> 6 3 6
-- | But these are warnings:
-- |    c(1,2) * c(3,2,1)               --> 3 4 1
-- |    c(1,2,3,4,5,6,7) * c(1,2,3,4,5) --> 1 4 9 16 25 6 14

{-@ predicate Divides Y X = remainder X Y == 0 @-}

{-@ predicate ValidInput A B
        = Divides (len A) (len B) || Divides (len B) (len A)
@-}

{-@ predicate ValidResult A B C
        = ValidInput A B && (len C) == max (len A) (len B)
@-}

{-@ takeMaxCycleZip ::
        x:NonEmptyList a -> y:{v:NonEmptyList b | ValidInput x v} ->
            {v:[(a,b)] | ValidResult x y v}
@-}
takeMaxCycleZip :: [a] -> [b] -> [(a,b)]
takeMaxCycleZip x y = take (max (length x) (length y)) $ cycleZip x y
-- takeMaxCycleZip = takeMaxCycleZipWith (,)

-- | Applications ------------------------------------------------------------

{-@ proof1 :: {remainder 3 3 == 0} @-}
proof1 = remainder 3 3 ==. remainder 0 3 *** QED

{-@ list1A :: ListN Int 3 @-}
list1A = [1,2,3] :: [Int]

{-@ list1B :: ListN Int 3 @-}
list1B = [4,5,6] :: [Int]

check1AB = takeMaxCycleZip list1A list1B
check1BA = takeMaxCycleZip list1B list1A

{-@ proof2 :: {remainder 14 2 == 0} @-}
proof2
    =   remainder 14 2
    ==. remainder 12 2
    ==. remainder 10 2
    ==. remainder  8 2
    ==. remainder  6 2
    ==. remainder  4 2
    ==. remainder  2 2
    ==. remainder  0 2
    ==. 0 *** QED

{-@ list2A :: ListN Int 2 @-}
list2A = [55,2] :: [Int]

{-@ list2B :: ListN Int 14 @-}
list2B = [1,2,3,4,5,6,7,8,9,10,11,12,13,14] :: [Int]

check2AB = takeMaxCycleZip list2A list2B
check2BA = takeMaxCycleZip list2B list2A

-- | zip becomes zipWith -----------------------------------------------------

-- zip up two lists by repeating their elements over and over
{-@ cycleZipWith ::
        (a -> b-> c) ->
            NonEmptyList a -> NonEmptyList b -> {v:[c] | (len v) = inf }
@-}
cycleZipWith :: (a -> b -> c) -> [a] -> [b] -> [c]
cycleZipWith f x y = safeZipWith f (cycle x) (cycle y)

{-@ takeMaxCycleZipWith ::
        (a -> b-> c) ->
            x:NonEmptyList a -> y:{v:NonEmptyList b | ValidInput x v} ->
                {v:[c] | ValidResult x y v}
@-}
takeMaxCycleZipWith :: (a -> b -> c) -> [a] -> [b] -> [c]
takeMaxCycleZipWith f x y = take (max (length x) (length y)) $ cycleZipWith f x y

checkWith1AB = takeMaxCycleZipWith (*) list1A list1B
checkWith1BA = takeMaxCycleZipWith (*) list1B list1A
checkWith2AB = takeMaxCycleZipWith (*) list2A list2B
checkWith2BA = takeMaxCycleZipWith (*) list2B list2A
