{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--prune-unsorted" @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--total-Haskell" @-}



module REMProof where

import Prelude
--import qualified Prelude

--import Language.Haskell.Liquid.ProofCombinators

{- die :: {v:_ | false} -> a @-}
--die msg = error msg

{- reflect die @-}

{-@ type NonZeroNat = {v:Nat | v /= 0} @-}


{-@ remainder :: Nat -> NonZeroNat -> Nat @-}
remainder :: Int -> Int -> Int
remainder x n | x == 0    = 0
        | x > n     = remainder (x - n) n
        | otherwise = x
---remainder x n | n == 0    = die "divide by zero"

-- this causes the crash
{-@ reflect remainder @-}


{-@ type RemDecreases = x:Nat -> y:Nat -> {rem x y <= x} @-}

{- remDecreases :: RemDecreases @-}
--remDecreases :: Int -> Int -> Proof
--remDecreases _ _ = trivial *** QED



{-@ predicate Divides x y = (rem x y == 0) @-}


