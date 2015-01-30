-- |
-- Module      : Data.Manifold.Types
-- Copyright   : (c) Justus Sagemüller 2015
-- License     : GPL v3
-- 
-- Maintainer  : (@) sagemueller $ geo.uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 


{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE UndecidableInstances     #-}
-- {-# LANGUAGE OverlappingInstances     #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE FunctionalDependencies   #-}
{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE RankNTypes               #-}
{-# LANGUAGE TupleSections            #-}
{-# LANGUAGE ConstraintKinds          #-}
{-# LANGUAGE PatternGuards            #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE ScopedTypeVariables      #-}
{-# LANGUAGE RecordWildCards          #-}


module Data.Manifold.Types where


import Data.VectorSpace
import Data.AffineSpace
import Data.Basis
import Data.Complex hiding (magnitude)
import Data.Void

import qualified Prelude

import Control.Category.Constrained.Prelude hiding ((^))
import Control.Arrow.Constrained
import Control.Monad.Constrained
import Data.Foldable.Constrained






type EuclidSpace v = (HasBasis v, EqFloating(Scalar v), Eq v)
type EqFloating f = (Eq f, Ord f, Floating f)



data GraphWindowSpec = GraphWindowSpec {
    lBound, rBound, bBound, tBound :: Double
  , xResolution, yResolution :: Int
  }





data S⁰ = PositiveHalfSphere | NegativeHalfSphere deriving(Eq, Show)
newtype S¹ = S¹ { φParamS¹ :: Double -- [-π, π[
                } deriving (Show)
data S² = S² { ϑParamS² :: !Double -- [0, π[
             , φParamS² :: !Double -- [-π, π[
             } deriving (Show)


class NaturallyEmbedded m v where
  embed :: m -> v
  coEmbed :: v -> m
  

instance (VectorSpace y) => NaturallyEmbedded x (x,y) where
  embed x = (x, zeroV)
  coEmbed (x,_) = x
instance (VectorSpace y, VectorSpace z) => NaturallyEmbedded x ((x,y),z) where
  embed x = (embed x, zeroV)
  coEmbed (x,_) = coEmbed x

instance NaturallyEmbedded S⁰ ℝ where
  embed PositiveHalfSphere = 1
  embed NegativeHalfSphere = -1
  coEmbed x | x>=0       = PositiveHalfSphere
            | otherwise  = NegativeHalfSphere
instance NaturallyEmbedded S¹ ℝ² where
  embed (S¹ φ) = (cos φ, sin φ)
  coEmbed (x,y) = S¹ $ atan2 y x
instance NaturallyEmbedded S² ℝ³ where
  embed (S² ϑ φ) = ((cos φ * sin ϑ, sin φ * sin ϑ), cos ϑ)
  coEmbed ((x,y),z) = S² (acos $ z/r) (atan2 y x)
   where r = sqrt $ x^2 + y^2 + z^2
 




type Endomorphism a = a->a


type ℝ = Double
type ℝ² = (ℝ,ℝ)
type ℝ³ = (ℝ²,ℝ)

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



(^) :: Num a => a -> Int -> a
(^) = (Prelude.^)

