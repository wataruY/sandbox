{-# LANGUAGE DeriveDataTypeable #-}
module Main where 

import System.Console.CmdArgs
import HLS 
import Data.Word
import Tuple3

data Config  = FromRGB { red :: Integer, green :: Integer, blue :: Integer }
             | FromHLS { hue :: Double, lightness :: Double, saturation :: Double } deriving (Show,Data,Typeable)

fromRGB = FromRGB { red = def &= typ "R" &= argPos 0
                  , green = def &= typ "G" &= argPos 1
                  , blue = def &= typ "B" &= argPos 2
                  }
fromHLS = FromHLS { hue = def &= typ "H" &= argPos 0
                  , lightness = def &= typ "L" &= argPos 1
                  , saturation = def &= typ "S" &= argPos 2
                  }

env = HLSEnv { maxRGB = 0xff, maxHue = 360 }
run' = flip HLS.run env


main = do conf <- cmdArgs $
             modes [fromHLS &= name "hls" &= help "HLS -> RGB",fromRGB &= name "rgb" &= help "RGB -> HLS"]
                       &= help "RGB <-> HLS"
          case conf of
            FromRGB r g b -> print $ f $ run' $ convertRGBtoHLS (r, g, b)
                where f (x,y,z) = ((-1) `maybe` fromRational $ x, fromRational y, fromRational z)
            FromHLS h l s -> print $ run' $ convertHLStoRGB (Just $ toRational h, toRational l, toRational s)