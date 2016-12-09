-- taken and modified from:
-- github.com/ucsd-progsys/liquidhaskell/blob/develop/docs/slides/BOS14/hs/end/04_Streams.hs

module Streams where

import Prelude hiding (take, repeat, cycle)

import Language.Haskell.Liquid.Prelude
import Language.Haskell.Liquid.ProofCombinators

-------------------------------------------------------------------------
-- | Lists 
-------------------------------------------------------------------------
 
data List a = N | C { x :: a, xs :: List a }

-- | Associate an abstract refinement with the _tail_ xs

{-@ data List a <p :: List a -> Prop>
      = N | C { x  :: a
              , xs :: List <p> a <<p>>
              }
  @-}

{-@ Lazy size @-}
{-@ measure size @-}

{-@ size :: List a -> Nat @-}
size :: List a -> Int
size (N)      = 0
size (C x xs) = (1 + size xs)

{-@ predicate Cons L = (size L > 0) @-}

{-@ type CList a = {xs:List a | Cons xs} @-}
{-@ type NList a N = {xs:List a | size xs == N} @-}

-------------------------------------------------------------------------
-- | Infinite Streams
-------------------------------------------------------------------------

-- | Infinite List = List where _each_ tail is a `cons` ...

{-@ type Stream a = {xs: List <{\v -> Cons v}> a | Cons xs} @-}

-------------------------------------------------------------------------
-- | Creating an Infinite Stream
-------------------------------------------------------------------------

{-@ Lazy repeat @-}
                 
{-@ repeat :: a -> Stream a @-}
repeat     :: a -> List a
repeat x = x `C` repeat x

{-@ Lazy cycleHelper @-}

{-@ cycleHelper :: CList a -> List a -> Stream a @-}
cycleHelper     :: List a  -> List a -> List a
cycleHelper N _        = liquidError "cycle: empty list"
cycleHelper l (C y ys) = y `C` (cycleHelper l ys)
cycleHelper l N        = cycleHelper l l

{-@ cycle :: CList a -> Stream a @-}
cycle     :: List a  -> List a
cycle xs  = cycleHelper xs xs

-------------------------------------------------------------------------
-- | Using an Infinite Stream
-------------------------------------------------------------------------
{-@ take :: n:Nat -> Stream a -> NList a n @-}
take     :: Int   -> List a   -> List a
take 0 _        = N
take n (C x xs) = x `C` take (n-1) xs
take _ N        = liquidError "take: never happens"

{-@ cycleTake :: n:Nat -> CList a -> NList a n @-}
cycleTake     :: Int   -> List a     -> List a
cycleTake n l = take n (cycle l)

-------------------------------------------------------------------------
-- | Interface with Haskell Lists
-------------------------------------------------------------------------

{-@ fromHList :: l:[a] -> (NList a (len l)) @-}
fromHList     :: [a]   -> List a
fromHList []     = N
fromHList (x:xs) = x `C` fromHList xs

{-@ Lazy toHList @-}

{-@ toHList :: l:List a -> {v:[a] | size l == len v} @-}
toHList :: List a -> [a]
toHList N        = []
toHList (C x xs) = x : toHList xs

{-@ cycleTakeHList :: n:Nat -> {v:[a] | len v > 0} -> {v:[a] | len v == n} @-}
cycleTakeHList     :: Int   -> [a]    -> [a]
cycleTakeHList n l = toHList (cycleTake n (fromHList l))
-------------------------------------------------------------------------
-- | Tests
-------------------------------------------------------------------------

{-@ inf0 :: Stream Int @-}
inf0 :: List Int
inf0 = repeat 0

{-@ inf1 :: Stream Int @-}
inf1 :: List Int
inf1 = cycle (C 1 N)

{-@ svtn :: {v:List Int | size v == 17} @-}
svtn :: List Int
svtn = (take 17 inf0)

check0 = liquidAssert $ size (take 23 (repeat 9))                          == 23
check1 = liquidAssert $ size (take 7 (cycle (C 1 N)))                      == 7
check2 = liquidAssert $ size (cycleTake 11 (C 1 N))                        == 11
check3 = liquidAssert $ size (cycleTake 13 (fromHList [1]))                == 13
check4 = liquidAssert $ length (cycleTakeHList 3 [1,3,4,7,6,2])            == 3
check5 = liquidAssert $ length (cycleTakeHList 95 [1,1,1,1,1,1,1,1,1,1,1]) == 95



