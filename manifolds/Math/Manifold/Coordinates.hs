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



module Math.Manifold.Coordinates where


import Data.Manifold.Types.Primitive
import Data.Manifold.Types.Stiefel
import Data.Manifold.PseudoAffine
import Math.LinearMap.Category

import Control.Lens

import qualified Linear as Lin

class HasXCoord m where
  xCoord :: Lens' m ℝ

instance HasXCoord ℝ where
  xCoord = id
instance HasXCoord ℝ² where
  xCoord = Lin._x
instance (HasXCoord v) => HasXCoord (v,w) where
  xCoord = _1 . xCoord
