{-# LANGUAGE FlexibleInstances, UndecidableInstances #-}

class Functor f => CMonad f where
    join :: f (f a) -> f a
    returnC :: a -> f a

instance CMonad m => Monad m where
    x >>= f = join $ fmap f x
    return = returnC