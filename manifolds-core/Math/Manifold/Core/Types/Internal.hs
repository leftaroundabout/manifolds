-- |
-- Module      : Math.Manifold.Core.Types.Internal
-- Copyright   : (c) Justus Sagemüller 2018
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsagemue $ uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 
-- Several low-dimensional manifolds, represented in some simple way as Haskell
-- data types. All these are in the 'PseudoAffine' class.
-- 
{-# LANGUAGE DeriveGeneric    #-}
{-# LANGUAGE EmptyCase        #-}


module Math.Manifold.Core.Types.Internal where

import Math.Manifold.VectorSpace.ZeroDimensional

import Data.Fixed (mod')

import Proof.Propositional (Empty(..))

import GHC.Generics


-- | The empty space can be considered a manifold with any sort of tangent space.
data EmptyMfd v

instance Empty (EmptyMfd v) where
  eliminate p = case p of {}
instance Eq (EmptyMfd v) where
  p==q = eliminate p && eliminate q
instance Ord (EmptyMfd v) where
  p<q = eliminate p && eliminate q
  p<=q = eliminate p && eliminate q

-- | The zero-dimensional sphere is actually just two points. Implementation might
--   therefore change to @ℝ⁰ 'Control.Category.Constrained.+' ℝ⁰@: the disjoint sum of two
--   single-point spaces.
type S⁰ = S⁰_ Double

data S⁰_ r = PositiveHalfSphere | NegativeHalfSphere deriving(Eq, Show, Generic)

type ℝP⁰ = ℝP⁰_ Double
data ℝP⁰_ r = ℝPZero deriving (Eq, Show, Generic)

-- | The unit circle.
type S¹ = S¹_ Double

newtype S¹_ r = S¹Polar { φParamS¹ :: r -- ^ Must be in range @[-π, π[@.
                        } deriving (Show, Generic)

instance (Eq r, RealFloat r) => Eq (S¹_ r) where
  S¹Polar φ == S¹Polar φ' = φ `mod'` (2*pi) == φ' `mod'` (2*pi)
     -- It's not clear that it's actually a good idea to fold back the range here,
     -- since values outside @[-π, π[@ should not be allowed in the first place.


type ℝP¹ = ℝP¹_ Double
newtype ℝP¹_ r = HemisphereℝP¹Polar { φParamℝP¹ :: r -- ^ Range @[-π\/2,π\/2[@.
                                    } deriving (Show, Generic)

-- | The ordinary unit sphere.
type S² = S²_ Double
data S²_ r = S²Polar { ϑParamS² :: !r -- ^ Range @[0, π[@.
                     , φParamS² :: !r -- ^ Range @[-π, π[@.
                     } deriving (Show, Generic)

instance (Eq r, RealFloat r) => Eq (S²_ r) where
  S²Polar θ φ == S²Polar θ' φ'
   | θ > 0, θ < pi  = θ == θ' && φ `mod'` (2*pi) == φ' `mod'` (2*pi)
   | otherwise      = θ == θ'

-- | The two-dimensional real projective space, implemented as a disk with
--   opposing points on the rim glued together. Image this disk as the northern hemisphere
--   of a unit sphere; 'ℝP²' is the space of all straight lines passing through
--   the origin of 'ℝ³', and each of these lines is represented by the point at which it
--   passes through the hemisphere.
type ℝP² = ℝP²_ Double
data ℝP²_ r = HemisphereℝP²Polar { ϑParamℝP² :: !r -- ^ Range @[0, π/2]@.
                                 , φParamℝP² :: !r -- ^ Range @[-π, π[@.
                                 } deriving (Show, Generic)


-- | The standard, closed unit disk. Homeomorphic to the cone over 'S¹', but not in the
--   the obvious, “flat” way. (In is /not/ homeomorphic, despite
--   the almost identical ADT definition, to the projective space 'ℝP²'!)
type D² = D²_ Double
data D²_ r = D²Polar { rParamD² :: !r -- ^ Range @[0, 1]@.
                     , φParamD² :: !r -- ^ Range @[-π, π[@.
                     } deriving (Show, Generic)


-- | The “one-dimensional disk” – really just the line segment between
--   the two points -1 and 1 of 'S⁰', i.e. this is simply a closed interval.
type D¹ = D¹_ Double
newtype D¹_ r = D¹ { xParamD¹ :: r -- ^ Range @[-1, 1]@.
                   } deriving (Show, Generic)

type ℝ = Double
type ℝ⁰ = ZeroDim ℝ




