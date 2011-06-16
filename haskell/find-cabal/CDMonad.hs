{-# LANGUAGE RankNTypes, TypeSynonymInstances, MultiParamTypeClasses #-}
module CDMonad where

import Control.Monad.Reader
import System.FilePath
import Control.Applicative

type CD a = ReaderT FilePath IO a

toAbs :: FilePath -> CD FilePath
toAbs x = asks (</>x)

toRel :: FilePath -> CD FilePath
toRel x = makeRelative <$> ask <*> pure x

cd :: FilePath -> CD a -> CD a
cd x = local (const x)

pwd :: CD FilePath
pwd = ask

withCD :: FilePath -> CD a -> IO a
withCD x = flip runReaderT x

runCD :: CD a -> FilePath -> IO a
runCD = runReaderT

{-# RULES
  "Rel/Abs" forall x. toAbs x >>= toRel = return x
  #-}