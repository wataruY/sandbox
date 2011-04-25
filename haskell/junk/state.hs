{-# LANGUAGE ScopedTypeVariables, RankNTypes #-}
import Control.Monad.State
import Data.Functor.Identity
import Control.Arrow

toTrans :: forall a s m. Monad m => (forall b. b -> m b) -> State s a -> StateT s m a
toTrans ca (StateT f) = StateT $ ca . runIdentity . f
