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



module Math.Manifold.Real.Coordinates
         ( Coordinate, coordinate
         , HasCoordinates(..)
         , HasXCoord(..), HasYCoord(..), HasZCoord(..)
         , CoordDifferential(..)
         ) where


import Data.Manifold.Types.Primitive
import Data.Manifold.Types.Stiefel
import Data.Manifold.PseudoAffine
import Math.LinearMap.Category
import Data.VectorSpace

import Control.Lens hiding ((<.>))

import qualified Linear as Lin

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

instance HasCoordinates ℝ where
  data CoordinateIdentifier ℝ = RealCoord
  coordinateAsLens RealCoord = id
  {-# INLINE coordinateAsLens #-}

instance HasCoordinates ℝ² where
  data CoordinateIdentifier ℝ² = ℝ²xCoord | ℝ²yCoord
  coordinateAsLens ℝ²xCoord = Lin._x
  coordinateAsLens ℝ²yCoord = Lin._y
  {-# INLINE coordinateAsLens #-}

instance HasCoordinates ℝ³ where
  data CoordinateIdentifier ℝ³ = ℝ³xCoord | ℝ³yCoord | ℝ³zCoord
  coordinateAsLens ℝ³xCoord = Lin._x
  coordinateAsLens ℝ³yCoord = Lin._y
  coordinateAsLens ℝ³zCoord = Lin._z
  {-# INLINE coordinateAsLens #-}

instance (HasCoordinates a, HasCoordinates b) => HasCoordinates (a,b) where
  data CoordinateIdentifier (a,b) = LSubspaceCoord (CoordinateIdentifier a)
                                  | RSubspaceCoord (CoordinateIdentifier b)
  coordinateAsLens (LSubspaceCoord ca) = _1 . coordinateAsLens ca
  coordinateAsLens (RSubspaceCoord cb) = _2 . coordinateAsLens cb
  {-# INLINE coordinateAsLens #-}

class HasCoordinates m => HasXCoord m where
  xCoord :: Coordinate m

instance HasXCoord ℝ where
  xCoord = coordinate RealCoord
  {-# INLINE xCoord #-}
instance HasXCoord ℝ² where
  xCoord = coordinate ℝ²xCoord
  {-# INLINE xCoord #-}
instance HasXCoord ℝ³ where
  xCoord = coordinate ℝ³xCoord
  {-# INLINE xCoord #-}
instance (HasXCoord v, HasCoordinates w) => HasXCoord (v,w) where
  xCoord = coordinate $ LSubspaceCoord xCoord

class HasYCoord m where
  yCoord :: Coordinate m

instance HasYCoord ℝ² where
  yCoord = coordinate ℝ²yCoord
  {-# INLINE yCoord #-}
instance HasYCoord ℝ³ where
  yCoord = coordinate ℝ³yCoord
  {-# INLINE yCoord #-}
instance HasCoordinates w => HasYCoord ((ℝ,ℝ),w) where
  yCoord = coordinate $ LSubspaceCoord yCoord
instance (HasXCoord w) => HasYCoord (ℝ,w) where
  yCoord = coordinate $ RSubspaceCoord xCoord

class HasZCoord m where
  zCoord :: Coordinate m

instance HasZCoord ℝ³ where
  zCoord = coordinate ℝ³zCoord
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
  delta RealCoord = coordinate . FibreSpaceCoordinate $ const RealCoord
instance CoordDifferential ℝ² where
  delta ℝ²xCoord = coordinate . FibreSpaceCoordinate $ const ℝ²xCoord
  delta ℝ²yCoord = coordinate . FibreSpaceCoordinate $ const ℝ²yCoord
