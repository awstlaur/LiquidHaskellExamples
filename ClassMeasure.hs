{-
  class measure over a Haskell typeclass
-}

{-@ LIQUID "--prune-unsorted" @-}
{-@ LIQUID "--total-Haskell" @-}

module ClassMeasure where

import Language.Haskell.Liquid.Prelude(liquidAssert)

{-@ class measure examine :: forall a. a -> Prop @-}

{-@ class Examinable s where
  examine :: forall a. x: s a -> {v:Bool | Prop v <=> examine x}
@-}
class Examinable s where
  examine :: s a -> Bool

instance Examinable Maybe where
  {-@ instance measure examine :: Maybe a -> Prop
        examine (Just _) = true
        examine Nothing  = false
    @-}
  examine (Just _) = True
  examine Nothing  = False

instance Examinable (Either l) where
  {-@ instance measure examine :: Either l a -> Prop
        examine (Right _) = true
        examine (Left  _) = false
    @-}
  examine (Right _) = True
  examine (Left  _) = False


checks = [
  liquidAssert $ examine (Just 0),
  liquidAssert $ not(examine Nothing),
  liquidAssert $ examine (Right 0),
  liquidAssert $ not(examine (Left 0))
  ]
