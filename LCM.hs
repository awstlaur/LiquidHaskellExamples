{-
    LCM remains uninterpreted in LH logic,
    but perhaps this is a start.

    Eventually, I'll want to use this to assert/prove something like
    lcm x y == max x y <==> (min x y) divides (max x y)
    and then apply this to takeLcmCycleZip
-}

{-@ LIQUID "--prune-unsorted" @-}
{-@ LIQUID "--total-Haskell" @-}

module LCM where
import Language.Haskell.Liquid.Prelude(liquidAssert)
import Prelude hiding(lcm)
import qualified Prelude

{-@ type NonNegInt = {v:Int | v >= 0} @-}

{-@ measure _lcm :: Int -> Int -> Int @-}

{-@ assume lcm :: x:NonNegInt -> y:NonNegInt -> {z:NonNegInt | z == _lcm x y} @-}
lcm :: Int -> Int -> Int
lcm = Prelude.lcm

-- define a notion of infinity
{-@ measure inf :: Int @-}
{-@ invariant {v:Int | v < inf} @-}

-- inform LH that cycle produces an infinite list
{-@ cycle ::
    {v:[a] | (len v) > 0 } ->
    {v:[a] | (len v) = inf }
@-}

-- zip up two lists by repeating their elements over and over
{-@ cycleZip ::
    {v:[a]     | (len v) > 0 } ->
    {v:[b]     | (len v) > 0 } ->
    {v:[(a,b)] | (len v) = inf }
@-}
cycleZip :: [a] -> [b] -> [(a,b)]
cycleZip x y = zip (cycle x) (cycle y)

-- if `take n` acts on an infinite list, then the output is always of length n
{-@ take :: n:Int -> l:[a] -> {v:[a] | (len l == inf) ==> (len v == n) } @-}

{-@ takeLcmCycleZip ::
    x:{v:[a]   | (len v) > 0 } ->
    y:{v:[b]   | (len v) > 0 } ->
    {v:[(a,b)] | (len v) = _lcm (len x) (len y) }
@-}
takeLcmCycleZip :: [a] -> [b] -> [(a,b)]
takeLcmCycleZip x y = take (lcm (length x) (length y)) $ cycleZip x y
