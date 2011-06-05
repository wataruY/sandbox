{-# LANGUAGE GeneralizedNewtypeDeriving #-}
import Data.Word

newtype Pos = Pos Word16 deriving (Ord,Eq,Enum,Bounded)

makePos :: (Integral a,Num a) => a -> Maybe Pos
makePos x | x < 1 = Nothing
          | otherwise = Just $ Pos $ fromIntegral x

instance Show Pos where
    show (Pos x) = show x

instance Num Pos where
    fromInteger x | x < 1 = Pos 1
                  | otherwise = Pos $ fromInteger x
    (Pos x) + (Pos y) = Pos $ x+y
    (Pos x) * (Pos y) = Pos $ x*y
    abs x = x
    signum x = 1
    quotRem (Pos x) (Pos y) = 
instance Real Pos where
    toRational (Pos x) = toRational x

instance Integral Pos where
    toInteger (Pos x) = toInteger x