{-
    In-progress attempt at a class measure taking an abstract collection to a
    list of its elements
-}

{-# LANGUAGE FunctionalDependencies, FlexibleInstances #-}

{-@ LIQUID "--prune-unsorted" @-}
{-@ LIQUID "--total-Haskell" @-}

module Collects where

import Prelude hiding(length)
import qualified Prelude


data SomeRecord a = SomeRecord{
    elems :: [a]
  }

{- class measure lengthLH :: (Collects e ce) => x:[e] -> {v:Int | lengthLH x == len (toListLH x)} @-}
{- class measure lengthLH :: (Collects e ce) => [e] -> Int @-}
{-@ class measure toListLH :: (Collects e ce) => ce -> [e] @-}

{-@ class Collects e ce where
    length :: x:ce -> Nat
    toList :: x:ce -> {l:[e] | l == (toListLH x)}
@-}
class Collects e ce | ce -> e where
  length :: ce -> Int
  toList :: ce -> [e]

instance Collects e [e] where
  {-@ instance measure lengthLH :: [e] -> Int
      lengthLH []     = 0
      lengthLH (x:xs) = 1 + lengthLH xs
    @-}
  length []     = 0
  length (x:xs) = 1 + length xs

  {-@ instance measure toListLH :: [e] -> [e]
    @-}
  toList l = l

---toListLH ([])     = []
---toListLH (x:xs) = x:xs

{-
instance Container (SomeRecord a) where
  type (Elem (SomeRecord a)) = a

  {-@ elems :: x:(SomeRecord a)  -> {v:[a] | v == (toListLH x)} @-}

  {-@ instance measure toListLH :: (SomeRecord a) -> [a]
      toListLH (SomeRecord es) = es
  @-}
  toList = elems
-}
