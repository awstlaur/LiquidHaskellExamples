-- | https://github.com/ucsd-progsys/liquidhaskell/issues/889

{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--no-termination" @-}

import Language.Haskell.Liquid.ProofCombinators

{-@ type LListN a N = {v:LList a | (sz v) == N} @-}

{-@ data LList [sz] a = Nil | Cons {hd :: a, tl :: LList a} @-}
data LList a = Nil | Cons a (LList a)

{-@ measure sz @-}
sz :: LList a -> Int
sz Nil         = 0
sz (Cons x xs) = 1 + sz xs

{-@ invariant {v:LList a | sz v >= 0} @-}

{-@ measure inf :: Int @-}
{-@ invariant {v:Int | v < inf} @-}

-- | sz (Cons x xs) == inf => sz xs = inf
{-@ tailInfProof :: l:(LListN a inf) -> {sz (select_Cons_2 l) == inf} @-}
tailInfProof :: LList a -> Proof
tailInfProof l@(Cons x xs)
    =   sz l
    ==. 1 + sz xs
    *** QED

{-@ takeFromInfList :: xs:(LListN a inf) -> n:Nat -> (LListN a n) @-}
takeFromInfList :: (LList a) -> Int -> (LList a)
takeFromInfList _ 0           = Nil
takeFromInfList l@(Cons x xs) n = Cons x (takeFromInfList xs (n - 1))
