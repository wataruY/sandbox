{-# LANGUAGE FlexibleInstances, UndecidableInstances #-}
import Prelude ()
import Control.Monad (Monad (..))
import Data.Functor (Functor (..))
import Control.Category (Category (..))
import Control.Applicative (Applicative (..))

instance Monad m => Functor m where
    fmap f x = x >>= return . f

instance Monad m => Applicative m where
    pure = return
    f <*> x = f >>= \ f' -> x >>= return . f'