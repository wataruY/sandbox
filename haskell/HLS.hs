{-# LANGUAGE ViewPatterns, ScopedTypeVariables #-}
module Color where
import Prelude hiding (min,max,sum,mod)
import qualified Prelude as P
import Data.Word (Word8, Word16)
import Data.List (sort)
import Data.Maybe (fromJust, isNothing)
import Test.QuickCheck 
import Control.Applicative
-- data RGB = RGB { r :: Word8, g :: Word8, b :: Word8 } deriving (Show, Eq)
-- data HLS = HLS { h :: Float, l :: Float, s :: Float } deriving (Show, Eq)

-- 3 element tuple
mapTuple3 :: (a -> b) -> Tuple3 a -> Tuple3 b
mapTuple3 f (x,y,z) = (f x, f y, f z)

fst3 :: (a,b,c) -> a
fst3 (x,_,_) = x
snd3 (_,y,_) = y
trd3 (_,_,z) = z

type Tuple3 a = (a,a,a)

-- utility 
while p = until $ not . p

type RGB = Tuple3 Word8
type HLS = (Maybe Rational,Rational,Rational)
type Chroma = Rational

convertRGBtoHLS :: (Real a) => Tuple3 a -> HLS
convertRGBtoHLS (r',g',b') =
    let cs@[r,g,b] = map ((/maxRGB) . toRational) [r',g',b']
        [min, _, max] = sort cs
        c = max - min
        h' | c == 0 = Nothing
           | max == r = Just $ (g - b) / (c`mod`6)
           | max == g = Just $ (b - r) / c + 2
           | otherwise = Just $ (r - g) / c + 4
        h = adjustHue . (\ x -> x * maxHue / 6 ) <$> h'
        l = (max + min) / 2
        s | c == 0 = 0
          | otherwise = c / (1 - (abs $ 2 * l - 1))
    in (h, l, s)

maxRGB = 0xff
maxHue = 360

adjustHue = while (maxHue<=) (subtract maxHue) . until (0<=) (+maxHue)

type RGB' = Tuple3 Rational

convertHLStoRGB' :: HLS -> RGB'
convertHLStoRGB' (h',l,s) =
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
    in  (r + m, g + m, b + m)

mod :: (Ord a, Num a) => a -> a -> a
mod x y = abs $ (subtract x) $ until ((x<=) . (+y)) (+y) 0

convertHLStoRGB :: Integral a => HLS -> Tuple3 a
convertHLStoRGB = mapTuple3 (truncate . (maxRGB*)) .  convertHLStoRGB'

exsample = convertHLStoRGB  (convertRGBtoHLS (10,155,200))

test = quickCheck (\ (x :: Tuple3 Word8 )->  x == ((convertHLStoRGB . convertRGBtoHLS) x))

torelance n (x,y,z) (a,b,c) = all (<n) [diff x a, diff y b, diff z c]
    where diff n m = P.max n m - P.min n m