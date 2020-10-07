-- |
-- Module      : Data.Manifold.WithBoundary
-- Copyright   : (c) Justus Sagemüller 2020
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsag $ hvl.no
-- Stability   : experimental
-- Portability : portable
-- 

{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE UndecidableInstances     #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE DefaultSignatures        #-}
{-# LANGUAGE DeriveGeneric            #-}
{-# LANGUAGE StandaloneDeriving       #-}
{-# LANGUAGE UnicodeSyntax            #-}
{-# LANGUAGE ScopedTypeVariables      #-}
{-# LANGUAGE EmptyCase                #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE TypeInType               #-}


module Data.Manifold.WithBoundary where

import Data.VectorSpace
import Data.AffineSpace
import Data.Basis

import Math.Manifold.Core.PseudoAffine
import Math.Manifold.Core.Types
import Data.Manifold.Types.Primitive
import Math.Manifold.VectorSpace.ZeroDimensional

import Control.Applicative
import Control.Arrow

import qualified GHC.Generics as Gnrx
import GHC.Generics (Generic, (:*:)(..))
import Data.Kind (Type)

import Data.CallStack (HasCallStack)


class VectorSpace (FullSubspace h) => HalfSpace h where
  type FullSubspace h :: Type
  scaleNonNeg :: ℝay -> h -> h
  fromFullSubspace :: FullSubspace h -> h
  projectToFullSubspace :: h -> FullSubspace h

instance HalfSpace ℝay where
  type FullSubspace ℝay = ℝ⁰
  scaleNonNeg (Cℝay μ Origin) (Cℝay l Origin) = Cℝay (μ*l) Origin
  fromFullSubspace o = Cℝay 0 o
  projectToFullSubspace (Cℝay _ o) = o

class ( Semimanifold (Interior m), Semimanifold (Boundary m)
      , HalfSpace (HalfNeedle m), FullSubspace (HalfNeedle m) ~ Needle (Boundary m)
      ) => SemimanifoldWithBoundary m where
  type Interior m :: Type
  type Boundary m :: Type
  type HalfNeedle m :: Type
  fromInterior :: Interior m -> m
  toInterior :: m -> Maybe (Interior m)
  (|+^) :: Boundary m -> HalfNeedle m -> m
  (.-|) :: m -> Boundary m -> HalfNeedle m
  (.+^|) :: m -> Needle m -> Maybe (Boundary m)

instance SemimanifoldWithBoundary ℝ where
  type Interior ℝ = ℝ
  type Boundary ℝ = EmptyMfd ℝ⁰
  type HalfNeedle ℝ = ℝay
  fromInterior = id
  toInterior = Just
  p|+^_ = case p of {}
  _.-|p = case p of {}
  _.+^|_ = Nothing

