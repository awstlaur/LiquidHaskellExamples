{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--no-termination" @-}

-- | TODO: Prove that take <infinite list> n always produces an LList of sz n

import Prelude hiding(map,concat,take,cycle,max)

import Language.Haskell.Liquid.Prelude hiding(safeZipWith)
import Language.Haskell.Liquid.ProofCombinators

{-@ type LListN a N = {v:LList a | (sz v) = N} @-}

{-@ type NonEmptyLList a = {v:LList a | (sz v) > 0} @-}

{-@ type NonZeroNat     = {v:Nat | v /= 0}      @-}

{-@ data LList [sz] a = Nil | Cons {hd :: a, tl :: LList a} @-}
data LList a = Nil | Cons a (LList a) deriving (Eq)

{-@ measure sz @-}
sz :: LList a -> Int
sz Nil         = 0
sz (Cons x xs) = 1 + sz xs

{-@ invariant {v:LList a | sz v >= 0} @-}

{- reflect map @-}
{- map :: (a -> b) -> x:(LList a) -> {y:(LList b) | sz x == sz y} @-}
{-@ map :: (a -> b) -> LList a -> LList b @-}
map :: (a -> b) -> LList a -> LList b
map _ Nil         = Nil
map f (Cons x xs) = Cons (f x) (map f xs)

{-@ append :: LList a -> LList a -> LList a @-}
append :: LList a -> LList a -> LList a
append Nil l = l
append l Nil = l
append (Cons x xs) l = Cons x (append xs l)

{-@ concat :: LList (LList a) -> LList a @-}
concat :: LList (LList a) -> LList a
concat Nil = Nil
concat (Cons l ls) = append l (concat ls)

{-@ measure inf :: Int @-}
{-@ invariant {v:Int | v < inf} @-}

-- some stuff from:
-- github.com/ucsd-progsys/liquidhaskell/blob/develop/tests/todo/InfiniteLists.hs

{-@ cycle :: NonEmptyLList a -> (LListN a inf) @-}
cycle :: LList a -> LList a
cycle Nil = liquidError "cycle: empty list"
cycle xs  = xs' where xs' = append xs xs'

-- TODO
{- take :: xs:(LList a) -> n:{v:Nat | v < sz xs } -> {l:(LList a) | sz xs == inf => sz l == n } @-}
{-@ take :: xs:(LList a) -> {v:Nat | v < sz xs } -> (LList a) @-}
take :: (LList a) -> Int -> (LList a)
take Nil _ = liquidError "take: Nil"
take _ 0 = Nil
take (Cons x xs) i = Cons x (take xs (i - 1))

{- cycletake :: n:Nat -> (NonEmptyLList a) -> (LListN a n) -}
{-@ cycletake :: Nat -> (NonEmptyLList a) -> LList a @-}
cycletake :: Int -> LList a -> LList a
cycletake n l = take (cycle l) n

-- modified from Language.Haskell.Liquid.Prelude.safeZipWith
{-@ assert safeZipWith ::
    (a -> b -> c) ->
        xs : (LList a) -> ys:{v:(LList b) | sz(v) = sz(xs)} ->
            {v : (LList c) | sz(v) = sz(xs)}
@-}
safeZipWith :: (a->b->c) -> (LList a)->(LList b)->(LList c)
safeZipWith f (Cons a as) (Cons b bs) = Cons (f a b) (safeZipWith f as bs)
safeZipWith _ Nil     Nil     = Nil
safeZipWith _ _ _ = error "safeZipWith: cannot happen!"

{-@ cycleZip :: NonEmptyLList a -> NonEmptyLList b -> LListN (a,b) inf @-}
cycleZip :: (LList a) -> (LList b) -> (LList (a,b))
cycleZip x y = safeZipWith (,) (cycle x) (cycle y)

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

{-@ predicate Divides Y X = remainder X Y == 0 @-}

{-@ predicate ValidInput A B
        = Divides (sz A) (sz B) || Divides (sz B) (sz A)
@-}

{-@ predicate ValidResult A B C
        = ValidInput A B && (sz C) == max (sz A) (sz B)
@-}

-- TODO
{- takeMaxCycleZip ::
        x:NonEmptyLList a -> y:{v:NonEmptyLList b | ValidInput x v} ->
            {v:(LList (a,b)) | ValidResult x y v}
-}
{-@ takeMaxCycleZip ::
        NonEmptyLList a -> NonEmptyLList b -> (LList (a,b))
@-}
takeMaxCycleZip :: LList a -> LList b -> LList (a,b)
takeMaxCycleZip x y = take (cycleZip x y) (max (sz x) (sz y))

{-@ cycleZipWith ::
        (a -> b-> c) ->
            NonEmptyLList a -> NonEmptyLList b -> (LListN c inf)
@-}
cycleZipWith :: (a -> b -> c) -> (LList a) -> (LList b) -> (LList c)
cycleZipWith f x y = safeZipWith f (cycle x) (cycle y)

-- TODO
{- takeMaxCycleZipWith ::
        (a -> b-> c) ->
            x:NonEmptyLList a -> y:{v:NonEmptyLList b | ValidInput x v} ->
                {v:(LList c) | ValidResult x y v}
-}
{-@ takeMaxCycleZipWith ::
        (a->b->c) ->
            NonEmptyLList a -> NonEmptyLList b -> (LList c)
@-}
takeMaxCycleZipWith :: (a -> b -> c) -> (LList a) -> (LList b) -> (LList c)
takeMaxCycleZipWith f x y = take (cycleZipWith f x y) (max (sz x) (sz y))

foo = liquidAssert True
