-- |
-- Module      : Data.Manifold.Atlas
-- Copyright   : (c) Justus Sagemüller 2015
-- License     : GPL v3
-- 
-- Maintainer  : (@) sagemueller $ geo.uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 

{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE EmptyDataDecls, EmptyCase #-}
{-# LANGUAGE CPP                       #-}

module Data.Manifold.Atlas where

import Data.VectorSpace
import Data.Manifold.PseudoAffine
import Data.Manifold.Types.Primitive

import Data.Void

import Data.VectorSpace.Free

import Control.Arrow

class Semimanifold m => Atlas m where
  type ChartIndex m :: *
  chartReferencePoint :: ChartIndex m -> m
  lookupAtlas :: m -> ChartIndex m

#define VectorSpaceAtlas(c,v)    \
instance (c) => Atlas (v) where { \
  type ChartIndex (v) = ();        \
  chartReferencePoint () = zeroV;   \
  lookupAtlas _ = () }

VectorSpaceAtlas((), ZeroDim s)
VectorSpaceAtlas((), ℝ)
VectorSpaceAtlas(Num s, V0 s)
VectorSpaceAtlas(Num s, V1 s)
VectorSpaceAtlas(Num s, V2 s)
VectorSpaceAtlas(Num s, V3 s)
VectorSpaceAtlas(Num s, V4 s)

instance (Atlas x, Atlas y) => Atlas (x,y) where
  type ChartIndex (x,y) = (ChartIndex x, ChartIndex y)
  chartReferencePoint = chartReferencePoint *** chartReferencePoint
  lookupAtlas = lookupAtlas *** lookupAtlas

instance Atlas S⁰ where
  type ChartIndex S⁰ = S⁰
  chartReferencePoint = id
  lookupAtlas = id
instance Atlas S¹ where
  type ChartIndex S¹ = S⁰
  chartReferencePoint NegativeHalfSphere = S¹ $ -pi/2
  chartReferencePoint PositiveHalfSphere = S¹ $ pi/2
  lookupAtlas (S¹ φ) | φ<0        = NegativeHalfSphere
                     | otherwise  = PositiveHalfSphere
instance Atlas S² where
  type ChartIndex S² = S⁰
  chartReferencePoint PositiveHalfSphere = S² 0 0
  chartReferencePoint NegativeHalfSphere = S² pi 0
  lookupAtlas (S² ϑ _) | ϑ<pi/2     = PositiveHalfSphere
                       | otherwise  = NegativeHalfSphere
