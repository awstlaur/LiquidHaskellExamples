-- | Measures of type s -> [t] seem to not work ??

data MList a = Nil | Cons a (MList a)

-- | m -> [s]

{-@ class measure listOf :: forall s. forall t. s -> [t] @-}

{-@ instance measure listOf :: MList a -> [a]
    listOf Nil = []
    listOf (Cons x xs) = x : listOf xs
@-}

-- | m -> MList s

{-@ class measure mListOf :: forall s. forall t. s -> MList t @-}

{-@ instance measure mListOf :: [a] -> (MList a)
    mListOf []     = Nil
    mListOf (x:xs) = Cons x (mListOf xs)
@-}

foo :: [a] -> MList a
foo []     = Nil
foo (x:xs) = Cons x (foo xs)
