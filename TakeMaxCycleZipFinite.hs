{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--prune-unsorted" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--exact-data-cons" @-}

module TakeMaxCycleZipFinite where

import Prelude hiding (max, length, zip)

import Language.Haskell.Liquid.Prelude(liquidAssert, liquidError, safeZipWith)
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

{- length :: x:[a] -> {v:Int | v == len x}  @-}
{-@ measure len @-}
len :: [a] -> Int
len [] = 0
len (x:xs) = 1 + len xs

{-@ reflect zip @-}
zip :: [a] -> [b] -> [(a,b)]
zip _ [] = []
zip [] _ = []
zip (x:xs) (y:ys) = (x,y) : (zip xs ys)

-- | Skipping infinity

{-@ cycleTakeHelper ::
        full:NonEmptyList a ->
        curr:{v:[a] | len v <= len full} ->
        n:Nat -> 
        ListN a n
@-}
cycleTakeHelper :: [a] -> [a] -> Int -> [a]
cycleTakeHelper _ _ 0     = []
cycleTakeHelper full [] n = cycleTakeHelper full full n
cycleTakeHelper full (x:xs) n = x : (cycleTakeHelper full xs (n - 1))

{-@ reflect cycleTakeHelper @-}

{-@ cycleTake :: l:NonEmptyList a -> n:NonZeroNat -> ListN a n @-}
cycleTake :: [a] -> Int -> [a]
cycleTake l n = cycleTakeHelper l l n

{-@ reflect cycleTake @-}

-- | Taking from "Cycle Zip" ---------------------------------------------------

{-@ predicate Divides Y X = remainder X Y == 0 @-}

{-@ predicate ValidInput A B
        = Divides (len A) (len B) || Divides (len B) (len A)
@-}

{-@ predicate ValidResult A B C
        = ValidInput A B && (len C) == max (len A) (len B)
@-}

{-@ takeMaxCycleZipHelper ::
        x:NonEmptyList a -> y:{v:NonEmptyList b | len x <= len v} ->
            ListN (a,b) (len y)
@-}
takeMaxCycleZipHelper :: [a] -> [b] -> [(a,b)]
takeMaxCycleZipHelper x y =
    let x' = cycleTake x (len y)
    in
        zip x' y

{-@ reflect takeMaxCycleZipHelper @-}

{-@ flipTupleList :: l:[(b,a)] -> {v:[(a,b)] | len l == len v} @-}
flipTupleList :: [(b,a)] -> [(a,b)]
flipTupleList [] = []
flipTupleList ((x,y):xs) = (y,x) : flipTupleList xs

{- takeMaxCycleZip ::
        x:NonEmptyList a -> y:{v:NonEmptyList b | ValidInput x v} ->
            {v:[(a,b)] | ValidResult x y v}
@-}
{-@ takeMaxCycleZip ::
    x:NonEmptyList a -> y:NonEmptyList b -> [(a,b)] 
@-}
-- {v:[(a,b)] | len v == max (len x) (len y)}
takeMaxCycleZip :: [a] -> [b] -> [(a,b)]
takeMaxCycleZip x y
    | len x <= len y = takeMaxCycleZipHelper x y
    | otherwise = flipTupleList (takeMaxCycleZipHelper y x)

{- reflect takeMaxCycleZip @-}

{- takeMaxCycleZipProof ::
    x:NonEmptyList a -> y:NonEmptyList b -> {len (takeMaxCycleZip x y) == max (len x) (len y)}
@-}
takeMaxCycleZipProof :: [a] -> [b] -> Proof
takeMaxCycleZipProof x y = trivial *** QED

-- | Asserts -----------------------------------------------------------------

check = liquidAssert $ len (cycleTake [1,2,3] 16) == 16
