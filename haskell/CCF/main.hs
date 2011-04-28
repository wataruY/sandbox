{-# LANGUAGE GADTs, ScopedTypeVariables #-}
module Main where

import Text.Printf
import Control.Applicative hiding (Const)
import Control.Monad.Random
import Control.Arrow

data RExp a where
    Const :: a -> RExp a
    Add :: RExp a -> RExp a -> RExp a
    Mul :: RExp a -> RExp a -> RExp a
    Inv :: RExp a -> RExp a
           deriving Eq

type BinF a = RExp a -> RExp a -> RExp a

instance Show a => Show (RExp a) where
    show (Const a) = show a
    show (Add x y) = printf "(%s + %s)" (show x) $ show y
    show (Mul x y) = printf "(%s * %s)" (show x) $ show y
    show (Inv a) = printf "-%s" $ show a

data BinOp = LAdd | LMul deriving (Eq,Show,Enum)

mkTree :: forall m a. (Applicative m, Monad m) => Int -> m (Maybe BinOp) -> m Bool -> m a -> m (RExp a)
mkTree 0 _ p g = (id `switcher` Inv) p <*> (Const <$> g)
mkTree n f p g = f >>= mkTree 0 f p g `maybe` cexp 
    where rest = mkTree (n - 1) f p g
          cexp :: BinOp -> m (RExp a)
          cexp f' = (makeBinOp f') <$> rest <*> rest

makeBinOp :: BinOp -> (RExp a -> RExp a -> RExp a)
makeBinOp LAdd = Add
makeBinOp LMul = Mul

instance (Random BinOp) where
    random = randomBinOp
    randomR = const random

randomBinOp :: RandomGen g => g -> (BinOp, g)
randomBinOp = first f . random
    where f :: Bool -> BinOp
          f b = if b then LAdd else LMul

mkTreeRandom :: (Random a, Applicative m, MonadRandom m) => Int -> m (RExp a)
mkTreeRandom n = mkTree n getRandom getRandom getRandom

instance Random a => Random (Maybe a) where
    random g = maybeRandomG random g
    randomR r = maybeRandomG $ random `maybe` randomR $ unMaybes r
        where unMaybes (x,y) = (,) <$> x <*> y

maybeRandomG f g =
    let (x,g') = random g
        rest = f g'
    in if x then first Just rest else (Nothing,g')

switcher :: Monad m => a -> a -> m Bool -> m a
switcher x y p = do
  p' <- p
  return $ if p' then x else y

retryUntil :: Monad m => (a -> Bool) -> m a -> m a
retryUntil p g = do
  x <- g
  if p x then return x else retryUntil p g

distribute :: BinF a -> RExp a -> RExp a -> Maybe (RExp a)
distribute g l r = do
  (op,(x,y)) <- destruct r
  let f = makeBinOp op
  return $ f l x `g` f l y

destruct :: RExp a -> Maybe (BinOp,(RExp a, RExp a))
destruct (Add x y) = Just (LAdd,(x,y))
destruct (Mul x y) = Just (LMul,(x,y))
destruct _ = Nothing

mapRExp :: (a -> b) -> (RExp b -> RExp b) -> (RExp b -> RExp b -> RExp b) -> RExp a -> RExp b
mapRExp f g h xss =
    case xss of
      Const a -> Const $ f a
      Add x y -> rec x `h` rec y
      Mul x y -> rec x `h` rec y
      Inv x -> g $ rec x
    where rec = mapRExp f g h

main :: IO ()
main = undefined