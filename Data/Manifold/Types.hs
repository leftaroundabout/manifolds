-- |
-- Module      : Data.Manifold.Types
-- Copyright   : (c) Justus Sagemüller 2015
-- License     : GPL v3
-- 
-- Maintainer  : (@) sagemueller $ geo.uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 
-- Several low-dimensional manifolds, represented in some simple way as Haskell
-- data types. All these are in the 'PseudoAffine' class.
-- 
-- Also included in this module are some misc helper constraints etc., which don't really
-- belong here.


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


module Data.Manifold.Types (
        -- * Index / ASCII names
          Real0, Real1, Real2, Real3, Sphere0, Sphere1, Sphere2, Projective1, Projective2
        -- * Linear manifolds
        , ZeroDim(..)
        , ℝ⁰, ℝ, ℝ², ℝ³
        -- * Hyperspheres
        , S⁰(..), S¹(..), S²(..)
        -- * Projective spaces
        , ℝP¹,  ℝP²(..)
        -- * Utility (deprecated)
        , NaturallyEmbedded(..)
        , GraphWindowSpec(..), Endomorphism, (^), EuclidSpace, EqFloating
   ) where


import Data.VectorSpace
import Data.AffineSpace
import Data.Basis
import Data.Complex hiding (magnitude)
import Data.Void
import Data.Monoid

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



-- | A single point. Can be considered a zero-dimensional vector space, WRT any scalar.
data ZeroDim k = Origin deriving(Eq, Show)
instance Monoid (ZeroDim k) where
  mempty = Origin
  mappend Origin Origin = Origin
instance AdditiveGroup (ZeroDim k) where
  zeroV = Origin
  Origin ^+^ Origin = Origin
  negateV Origin = Origin
instance VectorSpace (ZeroDim k) where
  type Scalar (ZeroDim k) = k
  _ *^ Origin = Origin
instance HasBasis (ZeroDim k) where
  type Basis (ZeroDim k) = Void
  basisValue = absurd
  decompose Origin = []
  decompose' Origin = absurd

-- | The zero-dimensional sphere is actually just two points. Implementation might
--   therefore change to @ℝ⁰ 'Control.Category.Constrained.+' ℝ⁰@: the disjoint sum of two
--   single-point spaces.
data S⁰ = PositiveHalfSphere | NegativeHalfSphere deriving(Eq, Show)
-- | The unit circle.
newtype S¹ = S¹ { φParamS¹ :: Double -- ^ Must be in range @[-π, π[@.
                } deriving (Show)
-- | The ordinary unit sphere.
data S² = S² { ϑParamS² :: !Double -- ^ Range @[0, π[@.
             , φParamS² :: !Double -- ^ Range @[-π, π[@.
             } deriving (Show)




type ℝP¹ = S¹

-- | The two-dimensional real projective space, implemented as a unit disk with
--   opposing points on the rim glued together.
data ℝP² = ℝP² { rParamℝP² :: !Double -- ^ Range @[0, 1]@.
               , φParamℝP² :: !Double -- ^ Range @[-π, π[@.
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
 
instance NaturallyEmbedded ℝP² ℝ³ where
  embed (ℝP² r φ) = ((r * cos φ, r * sin φ), sqrt $ 1-r^2)
  coEmbed ((x,y),z) = ℝP² (sqrt $ 1-(z/r)^2) (atan2 (y/r) (x/r))
   where r = sqrt $ x^2 + y^2 + z^2




type Endomorphism a = a->a


type ℝ⁰ = ZeroDim ℝ
type ℝ = Double
type ℝ² = (ℝ,ℝ)
type ℝ³ = (ℝ²,ℝ)




type Real0 = ℝ⁰
type Real1 = ℝ
type Real2 = ℝ²
type Real3 = ℝ³

type Sphere0 = S⁰
type Sphere1 = S¹
type Sphere2 = S²

type Projective1 = ℝP¹
type Projective2 = ℝP²




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

