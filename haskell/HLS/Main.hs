{-# LANGUAGE ScopedTypeVariables #-}
module Main  where

import Test.QuickCheck
import HLS 
import Tuple3
import Data.Word

env = HLSEnv { maxRGB = 0xff, maxHue = 360 }
run' = flip HLS.run env

example = test $ (10,155,200) 


test x = run' $ convertRGBtoHLS (f x) >>= convertHLStoRGB
    where f = mapTuple3 fromIntegral

rgb_hls_id :: RGB -> Bool
rgb_hls_id (x :: Tuple3 Word8 ) = x == test x

allRGB :: [Tuple3 Word8]
allRGB = [(r,g,b) | r <- cs, g <- cs, b <- cs]
    where cs = [0..0xff]

deep = growingElements allRGB `forAll` rgb_hls_id

main = quickCheck rgb_hls_id