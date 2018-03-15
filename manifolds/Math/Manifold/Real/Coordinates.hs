-- |
-- Module      : Math.Manifold.Real.Coordinates
-- Copyright   : (c) Justus Sagemüller 2018
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsagemue $ uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 

{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE Rank2Types             #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE UnicodeSyntax          #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE EmptyCase              #-}
{-# LANGUAGE StandaloneDeriving     #-}



module Math.Manifold.Real.Coordinates
         ( Coordinate, coordinate
         , HasCoordinates(..)
         -- * Vector space axes
         , HasXCoord(..), HasYCoord(..), HasZCoord(..)
         -- * Tangent space diffs
         , CoordDifferential(..)
         -- * Spherical coordinates
         , HasAzimuth(..)
         , HasZenithDistance(..)
         ) where


import Data.Manifold.Types.Primitive
import Data.Manifold.Types.Stiefel
import Data.Manifold.PseudoAffine
import Math.LinearMap.Category
import Data.VectorSpace

import Control.Lens hiding ((<.>))

import qualified Linear as Lin

import qualified Test.QuickCheck as QC

-- | To give a custom type coordinate axes, first define an instance of this class.
class HasCoordinates m where
  -- | A unique description of a coordinate axis.
  data CoordinateIdentifier m :: *
  -- | How to use a coordinate axis for points in the containing space.
  --   This is what 'coordinate' calls under the hood.
  coordinateAsLens :: CoordinateIdentifier m -> Lens' m ℝ

class CoordinateIsh q m | q -> m where
  useCoordinate :: CoordinateIdentifier m -> q

instance CoordinateIsh (CoordinateIdentifier m) m where
  useCoordinate = id
instance (Functor f, HasCoordinates m, a ~ (ℝ -> f ℝ), b ~ (m -> f m))
          => CoordinateIsh (a -> b) m where
  useCoordinate = coordinateAsLens

coordinate :: CoordinateIdentifier m -> Coordinate m
coordinate = useCoordinate

-- | A coordinate is a function that can be used both to determine the position
-- of a point on a manifold along the one of some family of (possibly curved) axes on
-- which it lies, and for moving the point along that axis.
-- Basically, this is a 'Lens' and can indeed be used with the '^.', '.~' and '%~'
-- operators.
-- 
-- @
-- 'Coordinate' m ~ 'Lens'' m 'ℝ'
-- @
-- 
-- In addition, each type may also have a way of identifying particular coordinate
-- axes. This is done with 'CoordinateIdentifier', which is what should be used
-- for /defining/ given coordinate axes.
type Coordinate m = ∀ q . CoordinateIsh q m => q

instance HasCoordinates ℝ⁰ where
  data CoordinateIdentifier ℝ⁰
  coordinateAsLens b = case b of {}

instance HasCoordinates ℝ where
  data CoordinateIdentifier ℝ = RealCoord { realAxisTfmStretch :: !ℝ }
                      deriving (Show)
  coordinateAsLens (RealCoord μ) = iso (/μ) (*μ)
  {-# INLINE coordinateAsLens #-}

instance QC.Arbitrary (CoordinateIdentifier ℝ) where
  arbitrary = RealCoord . QC.getNonZero <$> QC.arbitrary
  shrink (RealCoord μ) = [ RealCoord ν | ν <- QC.shrink μ, ν/=0 ]

data OriginAxisCoord v = OriginAxisCoord
       { coordHeading :: !v             -- ^ Must be conjugate to heading, i.e.
       , coordSensor :: !(DualVector v) -- ^ @'coordSensor' <.>^ 'coordHeading' = 1@.
       }
deriving instance (Show v, Show (DualVector v)) => Show (OriginAxisCoord v)

originAxisCoordAsLens :: LinearSpace v => OriginAxisCoord v -> Lens' v (Scalar v)
originAxisCoordAsLens (OriginAxisCoord v dv)
     = lens (dv<.>^)
            (\w c' -> w ^+^ (c' - dv<.>^w)*^v)
{-# INLINE originAxisCoordAsLens #-}

instance (QC.Arbitrary v, InnerSpace v, v ~ DualVector v, Scalar v ~ ℝ)
    => QC.Arbitrary (OriginAxisCoord v) where
  arbitrary = QC.arbitrary `QC.suchThatMap` \v
   -> case magnitudeSq v of
       0 -> Nothing
       v² -> Just $ OriginAxisCoord v (v^/v²)
  shrink (OriginAxisCoord v _) = [ OriginAxisCoord w (w^/w²)
                                 | w <- QC.shrink v
                                 , let w² = magnitudeSq w
                                 , w² > 0 ]

instance HasCoordinates ℝ² where
  data CoordinateIdentifier ℝ² = ℝ²Coord !(OriginAxisCoord ℝ²) deriving (Show)
  coordinateAsLens (ℝ²Coord b) = originAxisCoordAsLens b
  {-# INLINE coordinateAsLens #-}

instance QC.Arbitrary ℝ² => QC.Arbitrary (CoordinateIdentifier ℝ²) where
  arbitrary = ℝ²Coord <$> QC.arbitrary
  shrink (ℝ²Coord q) = ℝ²Coord <$> QC.shrink q

instance HasCoordinates ℝ³ where
  data CoordinateIdentifier ℝ³ = ℝ³Coord !(OriginAxisCoord ℝ³) deriving (Show)
  coordinateAsLens (ℝ³Coord b) = originAxisCoordAsLens b
  {-# INLINE coordinateAsLens #-}

instance QC.Arbitrary ℝ³ => QC.Arbitrary (CoordinateIdentifier ℝ³) where
  arbitrary = ℝ³Coord <$> QC.arbitrary
  shrink (ℝ³Coord q) = ℝ³Coord <$> QC.shrink q

instance (HasCoordinates a, HasCoordinates b) => HasCoordinates (a,b) where
  data CoordinateIdentifier (a,b) = LSubspaceCoord (CoordinateIdentifier a)
                                  | RSubspaceCoord (CoordinateIdentifier b)
  coordinateAsLens (LSubspaceCoord ca) = _1 . coordinateAsLens ca
  coordinateAsLens (RSubspaceCoord cb) = _2 . coordinateAsLens cb
  {-# INLINE coordinateAsLens #-}

class HasCoordinates m => HasXCoord m where
  xCoord :: Coordinate m

instance HasXCoord ℝ where
  xCoord = coordinate (RealCoord 1)
  {-# INLINE xCoord #-}
instance HasXCoord ℝ² where
  xCoord = coordinate (ℝ²Coord $ OriginAxisCoord (Lin.V2 1 0) (Lin.V2 1 0))
  {-# INLINE xCoord #-}
instance HasXCoord ℝ³ where
  xCoord = coordinate (ℝ³Coord $ OriginAxisCoord (Lin.V3 1 0 0) (Lin.V3 1 0 0))
  {-# INLINE xCoord #-}
instance (HasXCoord v, HasCoordinates w) => HasXCoord (v,w) where
  xCoord = coordinate $ LSubspaceCoord xCoord

class HasYCoord m where
  yCoord :: Coordinate m

instance HasYCoord ℝ² where
  yCoord = coordinate (ℝ²Coord $ OriginAxisCoord (Lin.V2 0 1) (Lin.V2 0 1))
  {-# INLINE yCoord #-}
instance HasYCoord ℝ³ where
  yCoord = coordinate (ℝ³Coord $ OriginAxisCoord (Lin.V3 0 1 0) (Lin.V3 0 1 0))
  {-# INLINE yCoord #-}
instance HasCoordinates w => HasYCoord ((ℝ,ℝ),w) where
  yCoord = coordinate $ LSubspaceCoord yCoord
instance (HasXCoord w) => HasYCoord (ℝ,w) where
  yCoord = coordinate $ RSubspaceCoord xCoord

class HasZCoord m where
  zCoord :: Coordinate m

instance HasZCoord ℝ³ where
  zCoord = coordinate (ℝ³Coord $ OriginAxisCoord (Lin.V3 0 0 1) (Lin.V3 0 0 1))
  {-# INLINE zCoord #-}
instance HasXCoord w => HasZCoord ((ℝ,ℝ),w) where
  zCoord = coordinate $ RSubspaceCoord xCoord
instance (HasYCoord w) => HasZCoord (ℝ,w) where
  zCoord = coordinate $ RSubspaceCoord yCoord

instance (HasCoordinates (Interior b), HasCoordinates f)
              => HasCoordinates (FibreBundle b f) where
  data CoordinateIdentifier (FibreBundle b f)
           = BaseSpaceCoordinate (CoordinateIdentifier (Interior b))
           | FibreSpaceCoordinate (Interior b -> CoordinateIdentifier f)
  coordinateAsLens (BaseSpaceCoordinate b)
            = lens (\(FibreBundle p _) -> p)
                   (\(FibreBundle _ f) p -> FibreBundle p f)
                . coordinateAsLens b
  coordinateAsLens (FibreSpaceCoordinate b)
            = \φ pf@(FibreBundle p f) -> case coordinateAsLens $ b p of
                 fLens -> FibreBundle p <$> fLens φ f
  

class CoordDifferential m where
  -- | Observe local, small variations (in the tangent space) of a coordinate.
  delta :: CoordinateIdentifier m -> Coordinate (TangentBundle m)

instance CoordDifferential ℝ where
  delta ζ = coordinate . FibreSpaceCoordinate $ const ζ
instance CoordDifferential ℝ² where
  delta ζ = coordinate . FibreSpaceCoordinate $ const ζ


instance HasCoordinates S¹ where
  data CoordinateIdentifier S¹ = S¹Azimuth
  coordinateAsLens S¹Azimuth = lens φParamS¹ (const S¹Polar)

class HasAzimuth m where
  azimuth :: Coordinate m

instance HasAzimuth S¹ where
  azimuth = coordinate S¹Azimuth
  
instance HasCoordinates S² where
  data CoordinateIdentifier S² = S²ZenithAngle | S²Azimuth
  coordinateAsLens S²ZenithAngle = lens ϑParamS² (\(S²Polar _ φ) θ -> S²Polar θ φ)
  coordinateAsLens S²Azimuth = lens φParamS² (\(S²Polar θ _) φ -> S²Polar θ φ)

instance HasAzimuth S² where
  azimuth = coordinate S²Azimuth
  
class HasZenithDistance m where
  zenithAngle :: Coordinate m

instance HasZenithDistance S² where
  zenithAngle = coordinate S²ZenithAngle

