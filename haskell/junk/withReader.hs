{-# LANGUAGE ScopedTypeVariables #-}
import Control.Monad.Reader
import Control.Arrow

withReader' :: (p -> q) ->
               Reader q a -> Reader p a
withReader' f qa = reader $ \ (x::p) -> runReader qa $ f x
                   