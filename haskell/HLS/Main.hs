{-# LANGUAGE ScopedTypeVariables #-}
module Main  where

import Test.QuickCheck
import HLS
import Tuple3
import Data.Word

example = convertHLStoRGB  (convertRGBtoHLS (10,155,200))

rgb_hls_id :: RGB -> Bool
rgb_hls_id (x :: Tuple3 Word8 ) = x == (convertHLStoRGB . convertRGBtoHLS) x

main = quickCheck rgb_hls_id




