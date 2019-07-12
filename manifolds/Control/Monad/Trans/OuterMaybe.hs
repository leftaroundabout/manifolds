-- |
-- Module      : Control.Monad.Trans.OuterMaybe
-- Copyright   : (c) Justus Sagemüller 2016
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsag $ hvl.no
-- Stability   : experimental
-- Portability : portable
-- 
{-# LANGUAGE DeriveFunctor              #-}

module Control.Monad.Trans.OuterMaybe where

data OuterMaybeT f a = OuterNothing | OuterJust (f a) deriving (Functor)
instance (Applicative f) => Applicative (OuterMaybeT f) where
  pure = OuterJust . pure
  OuterJust fs <*> OuterJust xs = OuterJust $ fs <*> xs
  _ <*> _ = OuterNothing




