{-
    In-progress attempt at a class measure taking an abstract collection to a
    list of its elements
-}

{-# LANGUAGE FunctionalDependencies,
             FlexibleInstances,
             TypeFamilies #-}

{-@ LIQUID "--prune-unsorted" @-}
{-@ LIQUID "--total-Haskell" @-}

module Collects where

import Prelude hiding(length)
import qualified Prelude

-- | With Functional dependency -----------------------------------------------

data ListRecord a = ListRecord{
    elems :: [a]
  }

{-@ class measure length :: (Collects e ce) =>
    x:ce -> {v:Int | v == len (toList x)}
@-}

{-@ class measure toList :: (Collects e ce) => ce -> [e] @-}

{-@ class Collects e ce where
    length :: x:ce -> Nat
    toList :: x:ce -> {l:[e] | l == (toList x)}
@-}
class Collects e ce | ce -> e where
  length :: ce -> Int
  toList :: ce -> [e]

instance Collects e [e] where
  {-@ instance measure length :: [e] -> Int @-}
  length []     = 0
  length (x:xs) = 1 + length xs

  {-@ instance measure toList :: [e] -> [e] @-}
  toList l = l

instance Collects a (ListRecord a) where
  {-@ instance measure length :: (ListRecord a) -> Int @-}
  length (ListRecord [])     = 0
  length (ListRecord (x:xs)) = 1 + length xs

  {-@ instance measure toList :: (ListRecord a) -> [a] @-}
  toList = elems

 -- | With Type family -------------------------------------------------------

data ListRecordTF a = ListRecordTF{
    elemsTF :: [a]
  }

{-@ class measure lengthTF :: (CollectsTF ce) =>
    x:ce -> {v:Int | v == len (toListTF x)}
@-}

{-@ class measure toListTF :: (CollectsTF ce) => ce -> [Elem ce] @-}

{-@ class CollectsTF ce where
    lengthTF :: x:ce -> Nat
    toListTF :: x:ce -> {l:[Elem ce] | l == (toListTF x)}
@-}
class CollectsTF ce where
  type Elem ce
  lengthTF :: ce -> Int
  toListTF :: ce -> [Elem ce]

instance CollectsTF [e] where
  type (Elem [e]) = e
  {-@ instance measure lengthTF :: [e] -> Int @-}
  lengthTF []     = 0
  lengthTF (x:xs) = 1 + lengthTF xs

  {-@ instance measure toListTF :: [e] -> [Elem [e]] @-}
  toListTF l = l

instance CollectsTF (ListRecordTF a) where
  type (Elem (ListRecordTF a)) = a
  {-@ instance measure lengthTF :: (ListRecord a) -> Int @-}
  lengthTF (ListRecordTF [])     = 0
  lengthTF (ListRecordTF (x:xs)) = 1 + length xs

  {-@ instance measure toListTF :: (ListRecord a) -> [Elem (ListRecordTF a)] @-}
  toListTF = elemsTF
