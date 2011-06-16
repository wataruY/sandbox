{-# LANGUAGE RankNTypes, TypeOperators, Arrows, ImpredicativeTypes, LiberalTypeSynonyms #-}
module DirTrav where

import System.FilePath
import System.Directory
import CD
import Control.Applicative
import Control.Arrow
import Control.Monad
import Data.Either (partitionEithers)

type Directory = FilePath

type FileList = [FilePath]
type DirList = [Directory]

ls :: CD FileList
ls = pwd >>= condM (liftIO . doesDirectoryExist) >>=
     (liftIO . getDirectoryContents ||| const (return []))

condM :: Monad m => (a -> m Bool) -> a -> m (Either a a)
condM p x = do
  p' <- p x
  return $ ($x) $ if p' then Left else Right

ignoreDot :: FileList -> FileList
ignoreDot = filter ((/=".") . take 1)

isDirectory,isFile :: FilePath -> CD Bool
isDirectory = liftIO . doesDirectoryExist
isFile = liftIO . doesFileExist

lsParted :: CD (FileList,DirList)
lsParted = do
  ls >>= (partitionEithers<$>) . mapM (condM isFile <=< toAbs) . ignoreDot
  
upDir :: FilePath -> FilePath
upDir = joinPath . init . splitDirectories

ud = do
  d <- pwd
  cd (upDir d) pwd
  
find :: CD FileList
find = do
  root <- pwd
  (fs,ds) <- lsParted
  rest <- mapM (\ d -> cd d find) ds
  return $ fs ++ concat rest