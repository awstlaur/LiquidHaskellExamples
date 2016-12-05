{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--prune-unsorted" @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--total-Haskell" @-}



module REMProof where

import Prelude hiding (rem)
--import qualified Prelude

--import Language.Haskell.Liquid.ProofCombinators

{- die :: {v:_ | false} -> a @-}
--die msg = error msg

{- reflect die @-}

{-@ type NonZeroNat = {v:Nat | v /= 0} @-}


{-@ rem :: Nat -> NonZeroNat -> Nat @-}
rem :: Int -> Int -> Int
rem x n | x == 0    = 0
        | x > n     = rem (x - n) n
        | otherwise = x
---rem x n | n == 0    = die "divide by zero"

-- this causes the crash
{-@ reflect rem @-}


{-@ type RemDecreases = x:Nat -> y:Nat -> {rem x y <= x} @-}

{- remDecreases :: RemDecreases @-}
--remDecreases :: Int -> Int -> Proof
--remDecreases _ _ = trivial *** QED



{-@ predicate Divides x y = (rem x y == 0) @-}


