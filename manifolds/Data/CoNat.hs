-- |
-- Module      : Data.CoNat
-- Copyright   : (c) Justus Sagemüller 2015
-- License     : GPL v3
-- 
-- Maintainer  : (@) sagemueller $ geo.uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE UnicodeSyntax              #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE PatternGuards              #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE DataKinds                  #-}

module Data.CoNat where

import Data.Tagged
import Data.Semigroup
    
import qualified Prelude as Hask hiding(foldl)
import qualified Control.Applicative as Hask
import qualified Control.Monad       as Hask
import qualified Data.Foldable       as Hask


import Control.Category.Constrained.Prelude hiding ((^))


    
-- | Mainly intended to be used as a data kind.
--   Of course, we'd rather use "GHC.TypeLits" naturals, but they aren't mature enough yet.
data Nat = Z | S Nat deriving (Eq)

natToInt :: Nat -> Int
natToInt Z = 0; natToInt (S n) = 1 + natToInt n

fromNat :: Num a => Nat -> a
fromNat = fromIntegral . natToInt

class KnownNat (n :: Nat) where
  theNat :: Tagged n Nat
            
  cozero :: s Z -> Option (s n)
  cozeroT :: c Z x -> Option (c n x)
             
  cosucc :: (forall k . KnownNat k => s (S k)) -> Option (s n)
  fCosucc :: Hask.Alternative f => (forall k . KnownNat k => f (s (S k))) -> f (s n)
  cosuccT :: (forall k . KnownNat k => s (S k) x) -> Option (s n x)
  fCosuccT :: Hask.Alternative f => (forall k . KnownNat k => f (s (S k) x)) -> f (s n x)


instance KnownNat Z where
  theNat = Tagged Z
  cozero  = pure; cosucc _  = Hask.empty; fCosucc _  = Hask.empty
  cozeroT = pure; cosuccT _ = Hask.empty; fCosuccT _ = Hask.empty
instance (KnownNat n) => KnownNat (S n) where
  theNat = fmap S theNat
  cozero _  = Hask.empty; cosucc v  = pure v; fCosucc v  = v
  cozeroT _ = Hask.empty; cosuccT v = pure v; fCosuccT v = v

