{-
    In-progress attempt at a class measure taking an abstract collection to a
    list of its elements
-}

{-# LANGUAGE FunctionalDependencies,
             FlexibleInstances,
             TypeFamilies #-}

{-@ LIQUID "--prune-unsorted" @-}
{-@ LIQUID "--total-Haskell" @-}

module CollectsAsAConstraint where

import Prelude hiding(length)
import qualified Prelude

import Language.Haskell.Liquid.Prelude(liquidAssert)

data ListRecord a = ListRecord{
    elems :: [a]
  }

class HasEmpty ce where
    empty :: ce
     
instance HasEmpty [e] where
    empty = []
     
instance HasEmpty (ListRecord a) where
    empty = ListRecord{elems = []}

{-@ class measure lengthCM :: (Collects ce) => ce -> Int @-}

{-@ class (HasEmpty ce) => Collects ce where
    length :: x:ce -> Nat
    getEmpty :: [Elem ce]
    listOf :: x:ce -> {v:[Elem ce] | len v == lengthCM x}
@-}
class (HasEmpty ce) => Collects ce where
  type Elem ce
  length :: ce -> Int  
  getEmpty :: [Elem ce]
  listOf :: ce -> [Elem ce]

instance Collects [e] where
  type (Elem [e]) = e
  
{-@ instance measure lengthCM :: [e] -> Int 
    lengthCM []     = 0
    lengthCM (x:xs) = 1 + lengthCM xs
@-}
  length []     = 0
  length (x:xs) = 1 + length xs
  

  listOf x = x
  
  getEmpty = empty


instance Collects (ListRecord a) where
  type (Elem (ListRecord a)) = a
  
  length x = length (elems x)
  
  listOf x = elems x
  
  getEmpty = case empty of
      ListRecord l -> l

-- | Collects as a constraint ----------------------------------------------

{-@ class (Collects ce) => Foo ce where
    getFoo :: ce -> {v:[Elem ce] | len v == 0}
@-}
class (Collects ce) => Foo ce where
    getFoo :: ce -> [Elem ce]
    getFoo _ = []

instance Foo [a]
instance Foo (ListRecord a)

check = liquidAssert $ length (getFoo ListRecord{elems = [1,2]}) == 0
