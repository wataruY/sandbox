import Prelude hiding (divMod)

divMod_positive :: (Ord a,Num a) => a -> a -> (a,a)
divMod_positive m n
    | m < n = (0,m)
    | m == n = (1,0)
    | m > n = let (b,r) = divMod_positive (m-n) n
              in (b+1,r)
