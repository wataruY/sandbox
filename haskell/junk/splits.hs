import Data.List (unfoldr)
import Control.Arrow
import Test.QuickCheck
splits xs = unfoldr psi 0 ++ [(xs,[])]
    where psi n = let ys@(_,zs) = splitAt n xs
                  in if null zs then Nothing
                     else Just (ys, succ n)

splits' [] = [([],[])]
splits' as@(x:xs) = ([], as) : map (first (x:)) (splits xs)