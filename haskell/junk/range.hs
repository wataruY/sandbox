{-# LANGUAGE TemplateHaskell, FlexibleInstances, UndecidableInstances, ViewPatterns, ScopedTypeVariables #-}
import Data.Lens.Common
import Data.Lens.Template
import Control.Monad
import Control.Arrow
import Data.Maybe (fromJust)
import Data.List (intercalate)

data Range a = Range { _from :: a, _to :: a } deriving (Eq)
$( makeLenses [''Range] )

instance Show a => Show (Range a) where
    show x = "["++show (x^.from) ++ ", " ++ show (x^.to) ++ ")"

class (Ord a,Num a,Enum a) => Ranged a where
instance (Ord a,Num a, Enum a) => Ranged a

makeRange :: Ranged a => a -> a -> Maybe (Range a)
makeRange m n | x < n = Just $ Range x n
              | otherwise = Nothing
              where x = m `max` 0

(∈) :: Ranged a => a -> Range a -> Bool
x ∈ r = r^.from <= x && x <= r^.to
x ∉ r = not (x ∈ r)

splitRange :: Ranged a => a -> Range a -> Maybe (Range a,Range a)
splitRange x r = do guard $ x ∈ r
                    makeRange (r^.from) x `f` makeRange x (r^.to)
    where f = liftM2 (,)

combineRange :: Ranged a => Range a -> Range a -> Maybe (Range a)
combineRange x y = do guard (x^.to == y ^.from)
                      makeRange (x^.from) (y^.to)

splits :: Ranged a => Range a -> [(Range a, Range a)]
splits x = map (fromJust . (`splitRange` x)) ixs
    where ixs = [succ (x^.from) .. pred (x^.to)]

newtype Pattern a = Pattern [Range a] deriving Eq
instance Show a => Show (Pattern a ) where
    show (Pattern xs) = "{" ++ intercalate ", " ss ++ "}"
        where ss = map show xs

diff x = x^.to - x^.from

singlePat :: Range a -> Pattern a
singlePat = Pattern . return

allSplits :: Ranged a => Range a -> [Pattern a]
allSplits x = singlePat x :
                [ Pattern $ y : z' | (y,z) <- splits x
                , Pattern z' <- allSplits z ]

sublist :: Range Int -> [b] -> [b]
sublist r = r^.from `f` r^.to
    where f m n = take (n - m) . drop m
          infixr 0 `f`

makeAbbrev :: Pattern Int -> [a] -> [[a]]
makeAbbrev (Pattern ps) xs = map (`sublist`xs) ps

allAbbrevs :: [a] -> [[[a]]]
allAbbrevs xs = [] `maybe` f $ makeRange 0 l
    where f = map (`makeAbbrev` xs) . allSplits
          l = length xs