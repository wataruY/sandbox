{-# LANGUAGE TemplateHaskell, ViewPatterns #-}
import Prelude hiding (readList)
import System.Environment
import System.Process
import Control.Applicative
import Control.Arrow
import Distribution.Version
import Distribution.Text
import GHC.Paths
import Data.Function (on)
import Data.List (groupBy,isPrefixOf,intercalate,intersperse)
import Data.Char (isSpace)
import Control.Arrow
import Data.Label
import Data.List.Split


init' :: [a] -> [a]
init' [] = []
init' xs = init xs

readList = filter (not . null . fst) . map ((init'.head)&&& map (dropWhile isSpace) . tail) .
      groupBy ((/=) `on` (" " `isPrefixOf`)) .
      lines <$> readProcess ghc_pkg ["list"] ""

data PackageConf = PackageConf { _confPath :: FilePath, _packages :: [FilePath] } deriving (Show)
data Package = Package { _name :: String, _version :: [Int] } deriving (Show)
$( mkLabels [''PackageConf, ''Package] )

parsePackage :: String -> Package
parsePackage = cond isHidden >>> left (init . tail) >>>
               each ( reverse >>> break (=='-') >>> second tail >>> both reverse >>> swap >>>
                      second (sepBy "." >>> map (read :: String -> Int))
                    ) >>>
               left (first $ \ x -> "("++x++")") >>>
               (uncurry Package ||| uncurry Package)

makeConstraints :: Package -> String
makeConstraints (modify name (cond isHidden  >>> ((init . tail) ||| id)) -> x) =
    get name x ++ "==" ++ intercalate "." (map show $ get version x)

constraints :: IO [String]
constraints = map (("--constraint="++). makeConstraints) . concatMap ((map (parsePackage)) . snd) <$> readList

main = do
  as <- getArgs
  c <- constraints
  let xs = as ++ c
  print $ "cabal "m ++ unwords xs
  end <- rawSystem "cabal" xs
  return ()


swap = snd&&&fst

each f = f +++ f
both f = f *** f



isHidden :: String -> Bool
isHidden [] = False
isHidden xs = head xs == '(' &&  last xs == ')'

cond :: (a -> Bool) -> a -> Either a a
cond p x = if p x then Left x else Right x

