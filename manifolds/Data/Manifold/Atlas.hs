-- |
-- Module      : Data.Manifold.Atlas
-- Copyright   : (c) Justus Sagemüller 2015
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsag $ hvl.no
-- Stability   : experimental
-- Portability : portable
-- 

{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE EmptyDataDecls, EmptyCase #-}
{-# LANGUAGE CPP                       #-}
{-# LANGUAGE ScopedTypeVariables       #-}

module Data.Manifold.Atlas where

import Prelude as Hask

import Data.VectorSpace
import Data.Manifold.PseudoAffine
import Data.Manifold.Types.Primitive
import Data.Manifold.WithBoundary
import Data.Manifold.WithBoundary.Class

import Data.Void

import Data.VectorSpace.Free
import Math.LinearMap.Category

import Control.Arrow

import Data.MemoTrie (HasTrie)

import qualified Linear.Affine as LinAff

class SemimanifoldWithBoundary m => Atlas m where
  type ChartIndex m :: *
  chartReferencePoint :: ChartIndex m -> m
  lookupAtlas :: m -> ChartIndex m

#define VectorSpaceAtlas(c,v)              \
instance (c) => Atlas (v) where {           \
  type ChartIndex (v) = ();                  \
  chartReferencePoint () = zeroV;              \
  lookupAtlas _ = () }

type NumPrime s = (Num' s, Eq s, OpenManifold s, ProjectableBoundary s)

VectorSpaceAtlas(NumPrime s, ZeroDim s)
VectorSpaceAtlas((), ℝ)
VectorSpaceAtlas(NumPrime s, V0 s)
VectorSpaceAtlas(NumPrime s, V1 s)
VectorSpaceAtlas(NumPrime s, V2 s)
VectorSpaceAtlas(NumPrime s, V3 s)
VectorSpaceAtlas(NumPrime s, V4 s)
VectorSpaceAtlas((NumPrime s, LinearSpace v, Scalar v ~ s, LinearSpace w, Scalar w ~ s), LinearMap s v w)
VectorSpaceAtlas((NumPrime s, LinearSpace v, Scalar v ~ s, LinearSpace w, Scalar w ~ s), Tensor s v w)

instance (Atlas x, Atlas y, SemimanifoldWithBoundary (x,y)) => Atlas (x,y) where
  type ChartIndex (x,y) = (ChartIndex x, ChartIndex y)
  chartReferencePoint = chartReferencePoint *** chartReferencePoint
  lookupAtlas = lookupAtlas *** lookupAtlas

instance Atlas S⁰ where
  type ChartIndex S⁰ = S⁰
  chartReferencePoint = id
  lookupAtlas = id
instance Atlas S¹ where
  type ChartIndex S¹ = S⁰
  chartReferencePoint NegativeHalfSphere = S¹Polar $ -pi/2
  chartReferencePoint PositiveHalfSphere = S¹Polar $ pi/2
  lookupAtlas (S¹Polar φ) | φ<0        = NegativeHalfSphere
                     | otherwise  = PositiveHalfSphere
instance Atlas S² where
  type ChartIndex S² = S⁰
  chartReferencePoint PositiveHalfSphere = S²Polar 0 0
  chartReferencePoint NegativeHalfSphere = S²Polar pi 0
  lookupAtlas (S²Polar ϑ _) | ϑ<pi/2     = PositiveHalfSphere
                            | otherwise  = NegativeHalfSphere

instance (Num'' n, LinearManifold (a n), Scalar (a n) ~ n, Needle (a n) ~ a n)
              => Atlas (LinAff.Point a n) where
  type ChartIndex (LinAff.Point a n) = ()
  chartReferencePoint () = LinAff.P zeroV
  lookupAtlas _ = ()

type Atlas' m = (Atlas m, HasTrie (ChartIndex m))


-- | The 'AffineSpace' class plus manifold constraints.
type AffineManifold m = ( Atlas' m, Manifold m, AffineSpace m
                        , Needle m ~ Diff m )

-- | An euclidean space is a real affine space whose tangent space is a Hilbert space.
type EuclidSpace x = ( AffineManifold x, InnerSpace (Diff x)
                     , DualVector (Diff x) ~ Diff x, Floating (Scalar (Diff x)) )

euclideanMetric :: EuclidSpace x => proxy x -> Metric x
euclideanMetric _ = euclideanNorm

