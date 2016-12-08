-- | https://github.com/ucsd-progsys/liquidhaskell/issues/885

{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}


import Prelude hiding(map)

{-@ reflect map @-}
map :: (a -> b) -> [a] -> [b]
map _ [] = []
map f (x:xs) = f x : map f xs
