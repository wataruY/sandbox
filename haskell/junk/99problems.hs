{-# LANGUAGE ScopedTypeVariables, TupleSections, TypeOperators, RankNTypes #-}
import Data.Functor.Foldable
import Control.Monad.Free
import Control.Comonad
import Control.Comonad.Cofree
import Control.Monad
import Control.Arrow

import Test.QuickCheck

myLast :: [a] -> Maybe a
myLast = para phi
    where phi :: Prim [a] ([a],Maybe a) -> Maybe a
          phi Nil = Nothing
          phi (Cons x ([],_)) = Just x
          phi (Cons x (xs,a)) = a `mplus` Just x

toMaybe :: Prim [a] b -> Maybe (a,b)
toMaybe Nil = Nothing
toMaybe (Cons x xs) = Just (x,xs)

myButLast :: [a] -> Maybe a
myButLast = histo phi
    where phi :: Prim [a] (Cofree (Prim [a]) (Maybe a)) -> Maybe a
          phi Nil = Nothing
          phi (Cons x xs) = do toMaybe $ unwrap xs
                               extract xs `mplus` Just x

myTail :: [a] -> Maybe [a]
myTail = para phi
    where phi Nil = Nothing
          phi (Cons _ (ys,zs)) = Just ys

elementAt :: [a] -> Int -> a
elementAt xs = head . ($xs) . hylo phi psi 
    where phi Nil = id
          phi (Cons f fs) = f . fs
          psi n | n < 1 = Nil
                | otherwise = Cons tail $ n - 1

myLength :: [a] -> Int
myLength = cata $ toMaybe >>> 0 `maybe` (succ . snd)

myreverse :: [a] -> [a]
myreverse = cata phi >>> ($[])
    where phi Nil = id
          phi (Cons x a) = a . (x:)

swap :: Arrow a => a (b,c) (c,b)
swap = arr snd &&& arr fst

halve :: [a] -> ([a],[a])
halve = cata phi >>> first (ceiling . (/2) . fromIntegral ) >>> swap >>> app
    where
      phi :: Prim [a] (Int, Int -> ([a],[a])) -> (Int, Int -> ([a],[a]))
      phi Nil = (0,const ([],[]))
      phi (Cons x (n,ct)) = (succ n, \ m -> if m == 0 then second (x:) $ ct 0 else first (x:) $ ct $ m - 1)

isPalindrome :: Eq a => [a] -> Bool
isPalindrome = and . uncurry (zipWith (==)) . halve

flatten :: [[a]] -> [a]
flatten = cata $ toMaybe >>> [] `maybe` uncurry (++)

compress :: Eq a => [a] -> [a]
compress = histo phi
    where phi Nil = []
          phi (Cons x xs) = case unwrap xs of
                              Nil -> [x]
                              Cons y _ -> if x == y then extract xs else x : extract xs


pack :: Eq a => [a] -> [[a]]
pack = ana psi
    where psi [] = Nil
          psi (x:xs) = uncurry Cons $ first (x:) $ span (==x) xs

encode :: Eq a => [a] -> [(Int,a)]
encode = ana psi
    where psi [] = Nil
          psi (x:xs) = ($xs) $ uncurry Cons . first ((,x) . succ . length) . span (==x) 

listToFree :: b -> [a] -> Free (Prim [a]) b
listToFree e = foldr (\ x y -> (wrap (Cons x y))) (Pure e)

decode :: Eq a => [(Int,a)] -> [a]
decode = futu psi
    where psi  [] = Nil
          psi  ((n,x) :xs) = Cons x $ listToFree xs $ replicate (n-1) x

infixl 0 ===
f === g = \ x -> f x == g x

testEncodeDecode :: Eq a => [a] -> Bool
testEncodeDecode = id === decode . encode 

type (:+) = Either

cond p x = if p x then Left x else Right x

type MEncoded a = (a :+ (Int,a))

encodeModified :: forall a. Eq a => [a] -> [MEncoded a]
encodeModified =  ana psi
    where psi [] = Nil
          psi (x:xs) = uncurry Cons . first f . span (==x) $ xs
              where f :: [a] -> MEncoded a
                    f = cond null >>> const x +++ (,x) . succ . length

decodeModified :: Eq a => [MEncoded a] -> [a]
decodeModified = futu psi
    where psi  [] = Nil
          psi  (a :xs) = (`Cons`Pure xs) ||| f $ a
              where f (n,x) = Cons x $ listToFree xs $ replicate (n-1) x

checkEncodeDecodeModiefied :: Eq a => [a] -> Bool
checkEncodeDecodeModiefied = decodeModified . encodeModified === id