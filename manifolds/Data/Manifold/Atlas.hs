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
{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE EmptyDataDecls, EmptyCase #-}
{-# LANGUAGE CPP                       #-}
{-# LANGUAGE ScopedTypeVariables       #-}

module Data.Manifold.Atlas where

import Prelude as Hask

import Data.VectorSpace
import Data.Manifold.PseudoAffine
import Data.Manifold.Types.Primitive

import Data.Void

import Data.VectorSpace.Free
import Math.LinearMap.Category

import Control.Arrow

import Data.MemoTrie (HasTrie)

import qualified Linear.Affine as LinAff

class Semimanifold m => Atlas m where
  type ChartIndex m :: *
  chartReferencePoint :: ChartIndex m -> m
  chartReferencePoint = fromInterior . interiorChartReferencePoint ([]::[m])
  interiorChartReferencePoint :: Hask.Functor p => p m -> ChartIndex m -> Interior m
  lookupAtlas :: m -> ChartIndex m

#define VectorSpaceAtlas(c,v)              \
instance (c) => Atlas (v) where {           \
  type ChartIndex (v) = ();                  \
  interiorChartReferencePoint _ () = zeroV;   \
  chartReferencePoint () = zeroV;              \
  lookupAtlas _ = () }

VectorSpaceAtlas((), ZeroDim s)
VectorSpaceAtlas((), ℝ)
VectorSpaceAtlas(Num s, V0 s)
VectorSpaceAtlas(Num s, V1 s)
VectorSpaceAtlas(Num s, V2 s)
VectorSpaceAtlas(Num s, V3 s)
VectorSpaceAtlas(Num s, V4 s)
VectorSpaceAtlas((LinearSpace v, Scalar v ~ s, TensorSpace w, Scalar w ~ s), LinearMap s v w)
VectorSpaceAtlas((TensorSpace v, Scalar v ~ s, TensorSpace w, Scalar w ~ s), Tensor s v w)

instance (Atlas x, Atlas y) => Atlas (x,y) where
  type ChartIndex (x,y) = (ChartIndex x, ChartIndex y)
  chartReferencePoint = chartReferencePoint *** chartReferencePoint
  interiorChartReferencePoint p
         = interiorChartReferencePoint (fst<$>p) *** interiorChartReferencePoint (snd<$>p)
  lookupAtlas = lookupAtlas *** lookupAtlas

instance Atlas S⁰ where
  type ChartIndex S⁰ = S⁰
  chartReferencePoint = id
  interiorChartReferencePoint _ = id
  lookupAtlas = id
instance Atlas S¹ where
  type ChartIndex S¹ = S⁰
  chartReferencePoint NegativeHalfSphere = S¹Polar $ -pi/2
  chartReferencePoint PositiveHalfSphere = S¹Polar $ pi/2
  interiorChartReferencePoint _ NegativeHalfSphere = S¹Polar $ -pi/2
  interiorChartReferencePoint _ PositiveHalfSphere = S¹Polar $ pi/2
  lookupAtlas (S¹Polar φ) | φ<0        = NegativeHalfSphere
                     | otherwise  = PositiveHalfSphere
instance Atlas S² where
  type ChartIndex S² = S⁰
  chartReferencePoint PositiveHalfSphere = S²Polar 0 0
  chartReferencePoint NegativeHalfSphere = S²Polar pi 0
  interiorChartReferencePoint _ PositiveHalfSphere = S²Polar 0 0
  interiorChartReferencePoint _ NegativeHalfSphere = S²Polar pi 0
  lookupAtlas (S²Polar ϑ _) | ϑ<pi/2     = PositiveHalfSphere
                            | otherwise  = NegativeHalfSphere

instance (LinearSpace (a n), Needle (a n) ~ a n, Interior (a n) ~ a n)
              => Atlas (LinAff.Point a n) where
  type ChartIndex (LinAff.Point a n) = ()
  interiorChartReferencePoint _ () = LinAff.P zeroV
  lookupAtlas _ = ()



-- | The 'AffineSpace' class plus manifold constraints.
type AffineManifold m = ( Atlas m, Manifold m, AffineSpace m
                        , Needle m ~ Diff m, HasTrie (ChartIndex m) )

-- | An euclidean space is a real affine space whose tangent space is a Hilbert space.
type EuclidSpace x = ( AffineManifold x, InnerSpace (Diff x)
                     , DualVector (Diff x) ~ Diff x, Floating (Scalar (Diff x)) )

euclideanMetric :: EuclidSpace x => proxy x -> Metric x
euclideanMetric _ = euclideanNorm

