-- |
-- Module      : Math.Manifold.VectorSpace.ZeroDimensional
-- Copyright   : (c) Justus Sagemüller 2016
-- License     : GPL v3
-- 
-- Maintainer  : (@) sagemueller $ geo.uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 
{-# LANGUAGE TypeFamilies               #-}

module Math.Manifold.VectorSpace.ZeroDimensional (
                         ZeroDim (..)
            ) where

import Data.AffineSpace
import Data.VectorSpace
import Data.Basis
import Data.Void



data ZeroDim s = Origin deriving (Eq, Show)

instance Monoid (ZeroDim s) where
  mempty = Origin
  mappend Origin Origin = Origin

instance AffineSpace (ZeroDim s) where
  type Diff (ZeroDim s) = ZeroDim s
  Origin .+^ Origin = Origin
  Origin .-. Origin = Origin
instance AdditiveGroup (ZeroDim s) where
  zeroV = Origin
  Origin ^+^ Origin = Origin
  negateV Origin = Origin
instance VectorSpace (ZeroDim s) where
  type Scalar (ZeroDim s) = s
  _ *^ Origin = Origin
instance HasBasis (ZeroDim s) where
  type Basis (ZeroDim k) = Void
  basisValue = absurd
  decompose Origin = []
  decompose' Origin = absurd
