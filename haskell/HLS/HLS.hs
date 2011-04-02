{-# LANGUAGE ViewPatterns, DeriveFunctor, ScopedTypeVariables #-}
module
    HLS
    (convertRGBtoHLS, convertHLStoRGB,RGB, run, HLSEnv (..))
    where
import Prelude hiding (min,max,sum,mod)
import Data.Word (Word8, Word16)
import Data.List (sort)
import Data.Maybe (fromJust, isNothing)
import Control.Applicative
import Tuple3
import Control.Monad.Reader

-- utility 
while p = until $ not . p

data HLSEnv a = HLSEnv { maxRGB :: a, maxHue :: a } deriving (Functor)

type HLSM a = Reader (HLSEnv a)
type HLSMT a m = ReaderT (HLSEnv a) m


mod :: (Ord a, Num a) => a -> a -> a
mod x y = abs $ (subtract x) $ until ((x<=) . (+y)) (+y) 0

type RGB = Tuple3 Word8
type HLS = (Maybe Rational,Rational,Rational)
type RGB' = Tuple3 Rational
getMaxRGB, getMaxHue :: Real a => Reader (HLSEnv a) a
getMaxRGB = asks maxRGB
getMaxHue = asks maxHue

toHLSM :: (Real e, Monad m) => m a -> HLSMT e m a
toHLSM = lift

run :: HLSM a b -> HLSEnv a -> b
run x e = runReader x e

convertRGBtoHLS :: forall a. (Real a, Integral a) => Tuple3 a -> HLSM a HLS
convertRGBtoHLS (r',g',b') = do
  (maxRGB :: Rational) <- toRational <$> getMaxRGB
  (maxHue :: Rational) <- toRational <$> getMaxHue
  let cs@[r,g,b] = map ((/maxRGB) . toRational) [r',g',b']
      [min, _, max] = sort cs
      c = max - min
      h' :: Maybe Rational
      h' | c == 0 = Nothing
         | max == r = Just $ (g - b) / (c`mod`6)
         | max == g = Just $ (b - r) / c + 2
         | otherwise = Just $ (r - g) / c + 4
      l = (max + min) / 2
      s | c == 0 = 0
        | otherwise = c / (1 - (abs $ 2 * l - 1))
  (h :: Maybe Rational) <- (trick toRational  :: HLSMT Rational Maybe Rational -> HLSM a (Maybe Rational)) $
                           (toHLSM :: Maybe Rational -> HLSMT Rational Maybe Rational)
                           ((\ x -> x * maxHue / 6 ) <$> h')
                           >>= adjustHue
  return (toRational <$> h, toRational l, toRational s)

adjustHue' :: Real a => a -> HLSM a a
adjustHue' x = do
  maxHue <- getMaxHue
  return $ while (maxHue<=) (subtract maxHue) $ until (0<=) (+maxHue) $ x

adjustHue :: (Real a, Monad m) => a -> HLSMT a m a
adjustHue = toTrans' return . adjustHue'

toTrans' :: Monad m => (a -> m a) -> Reader r a -> ReaderT r m a
toTrans' f x = ReaderT $ \ r -> f $ runReader x r

fromTrans' :: Monad m => ReaderT r m a -> Reader r (m a)
fromTrans' t = reader $ \ r -> runReaderT t r

trick :: forall a b m. (Functor m) => (b -> a) -> HLSMT a m a -> HLSM b (m a)
trick f x = reader $ \ (r :: HLSEnv b) -> runReaderT x (fmap f r)

-- type RGB' = Tuple3 Rational

convertHLStoRGB' :: (Num a, Real a) => HLS -> HLSM a RGB'
convertHLStoRGB' (h',l,s) = do
  maxHue <- toRational <$> getMaxHue
  let c = (1 - (abs $ 2*l - 1)) * s
      h = maybe undefined (/ (maxHue / 6)) h'
      x = c * (1 - (abs $ h `mod` 2 - 1))
      (r, g, b) | isNothing h' = (0,0,0)
                | h < 1 = (c, x, 0)
                | h < 2 = (x, c, 0)
                | h < 3 = (0, c, x)
                | h < 4 = (0, x, c)
                | h < 5 = (x, 0, c)
                | h < 6 = (c, 0, x)
                | otherwise = error "h < 6"
      m = l - c / 2
  return (r + m, g + m, b + m)

convertHLStoRGB :: (Num a, Real a, Integral a) => HLS -> HLSM a (Tuple3 a)
convertHLStoRGB x = do
  maxRGB <- toRational <$> getMaxRGB
  mapTuple3 (truncate . (maxRGB*)) <$> convertHLStoRGB' x
