module Tuple3  where

-- 3 element tuple
mapTuple3 :: (a -> b) -> Tuple3 a -> Tuple3 b
mapTuple3 f (x,y,z) = (f x, f y, f z)

fst3 :: (a,b,c) -> a
fst3 (x,_,_) = x
snd3 (_,y,_) = y
trd3 (_,_,z) = z

type Tuple3 a = (a,a,a)
