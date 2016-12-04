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

{- class measure _length :: (Collects e ce) => x:[e] -> {v:Int | _length x == len (_toList x)} @-}
{- class measure _length :: (Collects e ce) => [e] -> Int @-}
{-@ class measure _toList :: (Collects e ce) => ce -> [e] @-}

{-@ class Collects e ce where
    length :: x:ce -> Nat
    toList :: x:ce -> {l:[e] | l == (_toList x)}
@-}
class Collects e ce | ce -> e where
  length :: ce -> Int
  toList :: ce -> [e]

instance Collects e [e] where
  {-@ instance measure _length :: [e] -> Int
      _length []     = 0
      _length (x:xs) = 1 + _length xs
    @-}
  length []     = 0
  length (x:xs) = 1 + length xs

  {-@ instance measure _toList :: [e] -> [e]
    @-}
  toList l = l

---_toList ([])     = []
---_toList (x:xs) = x:xs

{-
instance Container (SomeRecord a) where
  type (Elem (SomeRecord a)) = a

  {-@ elems :: x:(SomeRecord a)  -> {v:[a] | v == (_toList x)} @-}

  {-@ instance measure _toList :: (SomeRecord a) -> [a]
      _toList (SomeRecord es) = es
  @-}
  toList = elems
-}
