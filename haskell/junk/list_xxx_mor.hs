{-# LANGUAGE ScopedTypeVariables #-}
import Data.Functor.Foldable
import Test.QuickCheck
import Test.QuickCheck.Checkers
import Control.Comonad.Cofree
import Control.Comonad
import Control.Monad.Free
import Control.Arrow


dropApo :: Int -> [a] -> [a]
dropApo = curry $ apo psi
    where psi (_,[]) = Nil
          psi (n,(x:xs)) = if n < 1 then Cons x (Left xs) else psi (n-1,xs)
drop_prop = \ n (xs::[Int]) -> dropApo n xs == drop n xs

takeAna :: Int -> [a] -> [a]
takeAna = curry $ ana psi
    where psi (_,[]) = Nil
          psi (n,(x:xs)) = if n < 1 then Nil else Cons x (n-1,xs)

take_prop = \ n (xs::[Int]) -> takeAna n xs == take n xs

takeWhileAna :: (a -> Bool) -> [a] -> [a]
takeWhileAna p = ana psi
    where psi [] = Nil
          psi (x:xs) | p x = Cons x xs
                     | otherwise = Nil

dropWhilePara :: (a -> Bool) -> [a] -> [a]
dropWhilePara p = para phi
    where phi Nil = []
          phi (Cons x (xs,ys)) | p x = ys
                               | otherwise = xs

initAna :: [a] -> [a]
initAna = ana psi
    where psi [x] = Nil
          psi (x:xs) = Cons x xs

at' :: [a] -> Int -> [a]
at' = curry $ futu psi
    where psi (x:_,0) = Cons x (Free Nil)
          psi (x:xs,n) = Cons x (Pure (xs,n-1))

lastHisto :: [a] -> a
lastHisto = histo phi
    where phi (Cons x xs) = case unwrap xs of
                              Nil -> x
                              Cons _ ys -> extract xs

at :: [a] -> Int -> a
at = curry $ lastHisto . uncurry at'

main :: IO ()
main = quickBatch $
       ("List operation defined with XXX morphism", [
         ("drop",property $ True)
        ]
       )