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


module Data.Manifold.Types.Primitive (
        -- * Index / ASCII names
          Real0, Real1, RealPlus, Real2, Real3
        , Sphere0, Sphere1, Sphere2
        , Projective1, Projective2
        , Disk1, Disk2, Cone, OpenCone
        -- * Linear manifolds
        , ZeroDim(..)
        , ℝ⁰, ℝ, ℝ², ℝ³, ℝ⁴
        -- * Hyperspheres
        , S⁰(..), otherHalfSphere, S¹(..), S²(..)
        -- * Projective spaces
        , ℝP¹,  ℝP²(..)
        -- * Intervals\/disks\/cones
        , D¹(..), fromIntv0to1, D²(..)
        , ℝay
        , CD¹(..), Cℝay(..)
        -- * Tensor products
        , (⊗)(..)
        -- * Utility (deprecated)
        , NaturallyEmbedded(..)
        , GraphWindowSpec(..), Endomorphism, (^), (^.), EqFloating
        , empty
   ) where


import Data.VectorSpace
import Data.VectorSpace.Free
import Linear.V2
import Linear.V3
import Math.VectorSpace.ZeroDimensional
import Data.AffineSpace
import Data.Basis
import Data.Void
import Data.Monoid
import Math.LinearMap.Category ((⊗)())

import Control.Applicative (Const(..), Alternative(..))

import Lens.Micro ((^.))

import qualified Prelude

import Control.Category.Constrained.Prelude hiding ((^))
import Control.Arrow.Constrained

import Data.Embedding






type EqFloating f = (Eq f, Ord f, Floating f)



data GraphWindowSpec = GraphWindowSpec {
    lBound, rBound, bBound, tBound :: Double
  , xResolution, yResolution :: Int
  }




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



-- | The &#x201c;one-dimensional disk&#x201d; &#x2013; really just the line segment between
--   the two points -1 and 1 of 'S⁰', i.e. this is simply a closed interval.
newtype D¹ = D¹ { xParamD¹ :: Double -- ^ Range @[-1, 1]@.
                }
fromIntv0to1 :: ℝ -> D¹
fromIntv0to1 x | x<0        = D¹ (-1)
               | x>1        = D¹ 1
               | otherwise  = D¹ $ (x+1)/2

-- | The standard, closed unit disk. Homeomorphic to the cone over 'S¹', but not in the
--   the obvious, &#x201c;flat&#x201d; way. (And not at all, despite
--   the identical ADT definition, to the projective space 'ℝP²'!)
data D² = D² { rParamD² :: !Double -- ^ Range @[0, 1]@.
             , φParamD² :: !Double -- ^ Range @[-π, π[@.
             } deriving (Show)

-- | A (closed) cone over a space @x@ is the product of @x@ with the closed interval 'D¹'
--   of &#x201c;heights&#x201d;,
--   except on its &#x201c;tip&#x201d;: here, @x@ is smashed to a single point.
--   
--   This construct becomes (homeomorphic-to-) an actual geometric cone (and to 'D²') in the
--   special case @x = 'S¹'@.
data CD¹ x = CD¹ { hParamCD¹ :: !Double -- ^ Range @[0, 1]@
                 , pParamCD¹ :: !x      -- ^ Irrelevant at @h = 0@.
                 }


-- | An open cone is homeomorphic to a closed cone without the &#x201c;lid&#x201d;,
--   i.e. without the &#x201c;last copy&#x201d; of @x@, at the far end of the height
--   interval. Since that means the height does not include its supremum, it is actually
--   more natural to express it as the entire real ray, hence the name.
data Cℝay x = Cℝay { hParamCℝay :: !Double -- ^ Range @[0, &#x221e;[@
                   , pParamCℝay :: !x      -- ^ Irrelevant at @h = 0@.
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


type ℝ⁰ = ZeroDim ℝ
type ℝ = Double
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

type Projective1 = ℝP¹
type Projective2 = ℝP²

type Disk1 = D¹
type Disk2 = D²

type Cone = CD¹ 
type OpenCone = Cℝay



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


infixr 8 ^

(^) :: Num a => a -> Int -> a
(^) = (Prelude.^)



