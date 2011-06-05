{-# LANGUAGE FlexibleInstances, UndecidableInstances, ScopedTypeVariables #-}
import Test.QuickCheck
import qualified List as L
import Data.Maybe (fromJust)
import Control.Monad (foldM)

class LowerBounded a where
    zero :: a
instance Bounded a => LowerBounded a where
    zero = minBound
class (Eq a, Num a, LowerBounded a, Integral a) => Peano a where
    suc :: a -> a
instance (Bounded a,Integral a) => Peano a where
    suc = succ

splitAtMaybe_prop :: (Peano n,Eq a) => n -> [a] -> Bool
splitAtMaybe_prop n xs | length xs < fromIntegral n = y == Nothing
                       | otherwise = xs == uncurry (++) (fromJust y)
    where y = splitAtMaybe n xs
splitAtMaybe_test =
    quickCheck $ forAll g $ \ (n,xs) -> splitAtMaybe_prop n xs
        where g = suchThat (arbitrary::Gen (Int,[Int])) $ \ x -> fst x >= 0
splitAtMaybe :: Peano n => n -> [a] -> Maybe ([a],[a])
splitAtMaybe 0 xs = Just $ splitAt 0 xs
splitAtMaybe n [] = Nothing
splitAtMaybe n (x:xs) = do
  (ys,zs) <- splitAtMaybe (n-1) xs
  return $ (x:ys,zs)

chunks :: Peano n => n -> [a] -> [[a]]
chunks 1 xs = [xs]
chunks n as = short `maybe` long $ splitAtMaybe n as
    where short = take (fromIntegral n) $ map return as ++ repeat []
          long (ys,rest) = zipWith (:) ys $ chunks n rest

setEq :: Eq a => [a] -> [a] -> Bool
setEq xs ys = False `maybe` null $ foldM phi ys xs
    where phi zs x = if null zs then Nothing else Just $ L.delete x zs

preserveContents :: (Peano n, Eq a) => n -> [a] -> Bool
preserveContents n xs = setEq xs $ concat $ chunks n xs

main = quickCheck $ forAll (arbitrary `suchThat` (\ a -> fst a > 0)) $ \ ((n,xs):: (Int,[Int])) -> preserveContents n xs