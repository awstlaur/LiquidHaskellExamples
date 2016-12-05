{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--prune-unsorted" @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--total-Haskell" @-}

{-
    THIS DOES NOT WORK YET
-}

module GCDProof where

import Prelude hiding (gcd, rem)
import qualified Prelude

--import Language.Haskell.Liquid.Prelude
import Language.Haskell.Liquid.ProofCombinators

-- | Definitions

{-@ rem :: Nat -> Nat -> Nat @-}
rem = Prelude.rem


-- github.com/ucsd-progsys/liquidhaskell/blob/develop/tests/pos/GCD.hs
{-@ gcd :: a:Nat -> b:Nat -> Nat / [a, b] @-}
gcd  :: Int -> Int -> Int
gcd  a b | a == 0    = b
         | b == 0    = a
         | a == b    = a
         | a > b     = gcd (a - b) b
         | a < b     = gcd a (b - a)
         | otherwise = 0


-- | Refinement Reflection

{-@ reflect gcd @-}

-- | Step 1: Definition

{-@ type GCDCongruence :: i:Nat -> j:Nat -> {i == j => gcd i == gcd j} @-}

{-@ gcdCongruence :: GcdCongruence @-}
gcdCongruence :: Int -> Int -> Proof
gcdCongruence _ _ = trivial *** QED

-- | Step 2: Reflection

-- | Step 3: Application

{-@ type GCDNineSix = { gcd 9 6 == 3 } @-}

{-@ gcdNineSix :: GCDNineSix @-}
gcdNineSix :: Proof
gcdNineSix = [gcd 3 3, gcd 3 6, gcd 9 6] *** QED

{-@ gcdNineSixPretty :: GCDNineSix @-}
gcdNineSixPretty :: Proof
gcdNineSixPretty
    = gcd 9 6
    ==. gcd 3 6
    ==. gcd 3 3
    *** QED
    
{-@ gcdNineFifteen :: {gcd 9 15 == 3} @-}
gcdNineFifteen :: Proof
gcdNineFifteen
    =   gcd 9 15
    ==. gcd 9 6     
    ==. 3           ∵ gcdNineSix
    *** QED
    
-- | Props and Such

{-@ type GCDIdempotent = x:Nat -> {gcd x x == x} @-}

{-@ gcdIdem :: GCDIdempotent @-}
gcdIdem :: Int -> Proof
gcdIdem x
    = gcd x x
    *** QED
    
{-@ type GCDCommutative = x:Nat -> y:{Nat | true } -> {gcd x y == gcd y x} @-}

{-@ gcdComm :: GCDCommutative @-}
gcdComm :: Int -> Int -> Proof
gcdComm x y
    | x == 0
        = gcd 0 y 
        ==. y 
        ==. gcd y 0
        *** QED

    | y == 0
        = gcd x 0 
        ==. x
        ==. gcd 0 x
        *** QED
        
    | x < y
        = gcd x y
        ==. gcd x (y - x)
        ==. gcd (y - x) x   ∵ gcdComm x (y - x)
        ==. gcd y x         
        *** QED

    | x > y
        = gcd x y
        ==. gcd (x - y) y
        ==. gcd y (x - y)   ∵ gcdComm y (x - y)
        ==. gcd y x
        *** QED
    
    | otherwise
        = trivial
        *** QED