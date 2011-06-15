{-# LANGUAGE PackageImports, RankNTypes, ScopedTypeVariables, FlexibleInstances, UndecidableInstances #-}
module Main where 
import System.Directory
import System.FilePath

import "mtl" Control.Monad.Reader
import Control.Monad.IO.Class
import Control.Arrow
import Control.Applicative
import Data.List (intercalate)
import "mtl" Control.Monad.Identity

type Child a = forall m. MonadIO m => ReaderT FilePath m a

coqlib :: FilePath
coqlib = "/usr/local/lib/coq/theories/"

getChild :: Child [FilePath]
getChild = ask >>= lift . liftIO . getDirectoryContents

filterSplit :: (a -> Bool) -> [a] -> ([a],[a])
filterSplit p = runIdentity . filterSplitM (return . p)

filterSplitM :: Monad m => (a -> m Bool) -> [a] -> m ([a],[a])
filterSplitM p = foldM (\ (xs,ys) x -> do
                          p' <- p x
                          return $ if p' then (x:xs,ys) else (xs,x:ys)
                       ) ([],[])

withOutDot :: [FilePath] -> [FilePath]
withOutDot = filter ((/=".") . take 1)

getChildren :: Child [FilePath]
getChildren = do
  cd <- ask
  xs <- getChild
  let toAbs = (cd</>)
  (files,xs') <- liftIO $ filterSplitM (doesFileExist . toAbs) $ withOutDot xs
  dirs <- liftIO $ filterM (doesDirectoryExist . toAbs) xs'
  rest <- forM dirs $ \ cd -> local (</>cd)  getChildren
  return $ map (cd</>) $ files ++ concat rest

upDirectory :: FilePath -> FilePath
upDirectory = joinPath . init . splitDirectories

runChild :: (MonadIO m, Monad n) => FilePath -> Child a -> m (n (Maybe a))
runChild root x = do
  p <- liftIO $ doesDirectoryExist root
  if p then Just <$> runReaderT x root else return Nothing

getChildrenRel :: (Functor m, MonadIO m) => FilePath -> m [FilePath]
getChildrenRel root = [] `maybe` map (makeRelative root)  <$> runChild root getChildren

getCoqlibs :: (MonadIO m,Functor m) => FilePath -> m [FilePath]
getCoqlibs = getChildrenRel >>>
             fmap (filter (takeExtension >>> (==".vo")) >>>
                   map (dropExtension >>> splitDirectories >>> intercalate "."))
