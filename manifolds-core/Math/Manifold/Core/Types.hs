-- |
-- Module      : Math.Manifold.Core.Types
-- Copyright   : (c) Justus Sagemüller 2016
-- License     : GPL v3
-- 
-- Maintainer  : (@) sagemueller $ geo.uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 
-- Several low-dimensional manifolds, represented in some simple way as Haskell
-- data types. All these are in the 'PseudoAffine' class.
-- 


{-# LANGUAGE TypeFamilies             #-}


module Math.Manifold.Core.Types where


import Data.VectorSpace
import Math.Manifold.VectorSpace.ZeroDimensional
import Data.AffineSpace
import Data.Basis
import Data.Void
import Data.Monoid

import Control.Applicative (Const(..), Alternative(..))




-- | The zero-dimensional sphere is actually just two points. Implementation might
--   therefore change to @ℝ⁰ 'Control.Category.Constrained.+' ℝ⁰@: the disjoint sum of two
--   single-point spaces.
data S⁰ = PositiveHalfSphere | NegativeHalfSphere deriving(Eq, Show)

otherHalfSphere :: S⁰ -> S⁰
otherHalfSphere PositiveHalfSphere = NegativeHalfSphere
otherHalfSphere NegativeHalfSphere = PositiveHalfSphere

-- | The unit circle.
newtype S¹ = S¹ { φParamS¹ :: Double -- ^ Must be in range @[-π, π[@.
                } deriving (Show)




type ℝP¹ = S¹




-- | The &#x201c;one-dimensional disk&#x201d; &#x2013; really just the line segment between
--   the two points -1 and 1 of 'S⁰', i.e. this is simply a closed interval.
newtype D¹ = D¹ { xParamD¹ :: Double -- ^ Range @[-1, 1]@.
                } deriving (Show)
fromIntv0to1 :: ℝ -> D¹
fromIntv0to1 x | x<0        = D¹ (-1)
               | x>1        = D¹ 1
               | otherwise  = D¹ $ x*2 - 1



type ℝ = Double
type ℝ⁰ = ZeroDim ℝ




instance VectorSpace () where
  type Scalar () = ℝ
  _ *^ () = ()

instance HasBasis () where
  type Basis () = Void
  basisValue = absurd
  decompose () = []
  decompose' () = absurd
instance InnerSpace () where
  () <.> () = 0


