-- | https://github.com/ucsd-progsys/liquidhaskell/issues/885

{-@ LIQUID "--higherorder" @-}

import Prelude hiding(map)

map :: (a -> b) -> [a] -> [b]
map _ [] = []
map f (x:xs) = f x : map f xs

{-@ reflect map @-}
