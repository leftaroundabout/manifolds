-- |
-- Module      : Data.Manifold.Types.Primitive
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
{-# LANGUAGE ExplicitNamespaces       #-}
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


module Data.Manifold.Types.Primitive (
        -- * Index / ASCII names
          Real0, Real1, RealPlus, Real2, Real3
        , Sphere0, Sphere1, Sphere2
        , Projective0, Projective1, Projective2
        , Disk1, Disk2, Cone, OpenCone
        -- * Linear manifolds
        , ZeroDim(..)
        , ℝ, ℝ⁰, ℝ¹, ℝ², ℝ³, ℝ⁴
        -- * Hyperspheres
        , S⁰(..), otherHalfSphere, S¹(..), S²(..)
        -- * Projective spaces
        , ℝP⁰(..), ℝP¹(..),  ℝP²(..)
        -- * Intervals\/disks\/cones
        , D¹(..), fromIntv0to1, D²(..)
        , ℝay
        , CD¹(..), Cℝay(..)
        -- * Tensor products
        , type (⊗)(..)
        -- * Utility (deprecated)
        , NaturallyEmbedded(..)
        , GraphWindowSpec(..), Endomorphism, (^), (^.), EqFloating
        , empty
   ) where


import Math.Manifold.Core.Types

import Data.VectorSpace
import Data.VectorSpace.Free
import Linear.V2
import Linear.V3
import Math.VectorSpace.ZeroDimensional
import Data.AffineSpace
import Data.Basis
import Data.Void
import Data.Monoid
import Data.Fixed (mod')
import Math.LinearMap.Category (type (⊗)())

import Control.Applicative (Const(..), Alternative(..))

import Control.Lens ((^.))

import qualified Prelude

import Control.Category.Constrained.Prelude hiding ((^))
import Control.Arrow.Constrained

import Data.Embedding

import qualified Test.QuickCheck as QC




type EqFloating f = (Eq f, Ord f, Floating f)



data GraphWindowSpec = GraphWindowSpec {
    lBound, rBound, bBound, tBound :: Double
  , xResolution, yResolution :: Int
  }








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
  embed (S¹ φ) = V2 (cos φ) (sin φ)
  coEmbed (V2 x y) = S¹ $ atan2 y x
instance NaturallyEmbedded S² ℝ³ where
  embed (S² ϑ φ) = V3 (cos φ * sin ϑ) (sin φ * sin ϑ) (cos ϑ)
  coEmbed (V3 x y z) = S² (acos $ z/r) (atan2 y x)
   where r = sqrt $ x^2 + y^2 + z^2
 
instance NaturallyEmbedded ℝP² ℝ³ where
  embed (ℝP² r φ) = V3 (r * cos φ) (r * sin φ) (sqrt $ 1-r^2)
  coEmbed (V3 x y z) = ℝP² (sqrt $ 1-(z/r)^2) (atan2 (y/r) (x/r))
   where r = sqrt $ x^2 + y^2 + z^2

instance NaturallyEmbedded D¹ ℝ where
  embed = xParamD¹
  coEmbed = D¹ . max (-1) . min 1

instance (NaturallyEmbedded x p) => NaturallyEmbedded (Cℝay x) (p,ℝ) where
  embed (Cℝay h p) = (embed p, h)
  coEmbed (v,z) = Cℝay (max 0 z) (coEmbed v)



type Endomorphism a = a->a


type ℝ¹ = V1 ℝ
type ℝ² = V2 ℝ
type ℝ³ = V3 ℝ
type ℝ⁴ = V4 ℝ


-- | Better known as &#x211d;&#x207a; (which is not a legal Haskell name), the ray
--   of positive numbers (including zero, i.e. closed on one end).
type ℝay = Cℝay ℝ⁰




type Real0 = ℝ⁰
type Real1 = ℝ
type RealPlus = ℝay
type Real2 = ℝ²
type Real3 = ℝ³

type Sphere0 = S⁰
type Sphere1 = S¹
type Sphere2 = S²

type Projective0 = ℝP⁰
type Projective1 = ℝP¹
type Projective2 = ℝP²

type Disk1 = D¹
type Disk2 = D²

type Cone = CD¹ 
type OpenCone = Cℝay




infixr 8 ^

(^) :: Num a => a -> Int -> a
(^) = (Prelude.^)



instance QC.Arbitrary S⁰ where
  arbitrary = (\hsph -> if hsph then PositiveHalfSphere else NegativeHalfSphere)
               <$> QC.arbitrary

instance QC.Arbitrary S¹ where
  arbitrary = S¹ . (pi-) . (`mod'`(2*pi))
               <$> QC.arbitrary

instance QC.Arbitrary S² where
  arbitrary = ( \θ φ -> S² (θ`mod'`pi) (pi - (φ`mod'`(2*pi))) )
               <$> QC.arbitrary<*>QC.arbitrary

instance QC.Arbitrary ℝP⁰ where
  arbitrary = pure ℝPZero

instance QC.Arbitrary ℝP¹ where
  arbitrary = ( \h -> ℝP¹ (1 - (h`mod'`2)) ) <$> QC.arbitrary

instance QC.Arbitrary ℝP² where
  arbitrary = ( \r φ -> ℝP² (r`mod'`1) (pi - (φ`mod'`(2*pi))) )
               <$> QC.arbitrary<*>QC.arbitrary

