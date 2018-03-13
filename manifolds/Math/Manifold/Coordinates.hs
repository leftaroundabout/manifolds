-- |
-- Module      : Math.Manifold.Coordinates
-- Copyright   : (c) Justus Sagemüller 2018
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsagemue $ uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 

{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE Rank2Types             #-}



module Math.Manifold.Coordinates where


import Data.Manifold.Types.Primitive
import Data.Manifold.Types.Stiefel
import Data.Manifold.PseudoAffine
import Math.LinearMap.Category
import Data.VectorSpace

import Control.Lens hiding ((<.>))

import qualified Linear as Lin

type Coordinate m = Lens' m ℝ

class HasXCoord m where
  xCoord :: Coordinate m

instance HasXCoord ℝ where
  xCoord = id
instance HasXCoord ℝ² where
  xCoord = Lin._x
instance (HasXCoord v) => HasXCoord (v,w) where
  xCoord = _1 . xCoord

class HasYCoord m where
  yCoord :: Coordinate m

instance HasYCoord ℝ² where
  yCoord = Lin._y
instance HasYCoord ((ℝ,ℝ),w) where
  yCoord = _1 . yCoord
instance (HasXCoord w) => HasYCoord (ℝ,w) where
  yCoord = _2 . xCoord

class CoordDifferential m where
  delta :: Coordinate m -> Coordinate (TangentBundle m)

instance CoordDifferential ℝ where
  delta c = lens (\(FibreBundle _ f) -> μ*f)
                 (\(FibreBundle p _) δ -> FibreBundle p $ δ/μ)
   where μ = 1^.c
instance CoordDifferential ℝ² where
  delta c = lens (\(FibreBundle _ f) -> μ<.>f)
                 (\(FibreBundle p _) δ -> FibreBundle p $ δ*^μ')
   where μ  = Lin.V2 μ₀ μ₁
         μ' = Lin.V2 (recip μ₀) (recip μ₁)
         μ₀ = Lin.V2 1 0^.c
         μ₁ = Lin.V2 0 1^.c
