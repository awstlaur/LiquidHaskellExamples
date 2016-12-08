{-
    In-progress attempt at a class measure taking an abstract collection to a
    list of its elements
-}

{-# LANGUAGE FunctionalDependencies,
             FlexibleInstances,
             TypeFamilies #-}

{-@ LIQUID "--prune-unsorted" @-}
{-@ LIQUID "--total-Haskell" @-}

module CollectsWithConstraint where

import Prelude hiding(length)
import qualified Prelude

import Language.Haskell.Liquid.Prelude(liquidAssert)

-- | With Functional dependency -----------------------------------------------

data ListRecord a = ListRecord{
    elems :: [a]
  }
  
class HasEmpty ce where
    empty :: ce
     
instance HasEmpty [e] where
    empty = []
     
instance HasEmpty (ListRecord a) where
    empty = ListRecord{elems = []}

{-@ class measure length :: (Collects e ce) =>
    x:ce -> {v:Int | v == len (toList x)}
@-}

{-@ class measure toList :: (Collects e ce) => ce -> [e] @-}

{-@ class (HasEmpty ce) => Collects e ce where
    length :: x:ce -> Nat
    toList :: x:ce -> {l:[e] | l == (toList x)}
    getEmpty :: ce
@-}
class (HasEmpty ce) => Collects e ce | ce -> e where
  length :: ce -> Int
  toList :: ce -> [e]

  getEmpty :: ce
  getEmpty = empty

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

class HasEmptyTF ce where
    emptyTF :: ce
     
instance HasEmptyTF [e] where
    emptyTF = []
     
instance HasEmptyTF (ListRecordTF a) where
    emptyTF = ListRecordTF{elemsTF = []}

{-@ class measure lengthTF :: (CollectsTF ce) =>
    x:ce -> {v:Int | v == len (toListTF x)}
@-}

{-@ class measure toListTF :: (CollectsTF ce) => ce -> [Elem ce] @-}

{-@ class (HasEmptyTF ce) => CollectsTF ce where
    lengthTF :: x:ce -> Nat
    toListTF :: x:ce -> {l:[Elem ce] | l == (toListTF x)}
    getEmptyTF :: ce
@-}
class (HasEmptyTF ce) => CollectsTF ce where
  type Elem ce
  lengthTF :: ce -> Int
  toListTF :: ce -> [Elem ce]
  getEmptyTF :: ce
  getEmptyTF = emptyTF

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

-- | CollectsTF as a constraint ----------------------------------------------

-- | TODO: Figure out bizarre error here.

{-@ class (CollectsTF ce) => Foo ce where
    getFoo :: ce -> {v:[Elem ce] | lengthTF v == 0}
@-}
class (CollectsTF ce) => Foo ce where
    getFoo :: ce -> [Elem ce]

instance Foo (ListRecordTF a) where
    getFoo _ = getEmptyTF

-- check = liquidAssert $ lengthTF (getFoo ListRecordTF{elemsTF = [1,2]}) == 0
