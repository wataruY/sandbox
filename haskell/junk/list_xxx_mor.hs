{-# LANGUAGE ScopedTypeVariables #-}
import Data.Functor.Foldable
import Test.QuickCheck
import Control.Arrow

dropApo :: Int -> [a] -> [a]
dropApo = curry $ apo psi
    where psi (_,[]) = Nil
          psi (n,(x:xs)) = if n < 1 then Cons x (Left xs) else psi (n-1,xs)

main :: IO ()
main = quickCheck $ \ n (xs::[Int]) -> dropApo n xs == drop n xs