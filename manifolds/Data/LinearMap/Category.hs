-- |
-- Module      : Data.LinearMap.Category
-- Copyright   : (c) Justus Sagemüller 2015
-- License     : GPL v3
-- 
-- Maintainer  : (@) sagemueller $ geo.uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE UnicodeSyntax              #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE PatternGuards              #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE DataKinds                  #-}

module Data.LinearMap.Category where

import Data.Tagged
import Data.Semigroup

import Data.MemoTrie
import Data.VectorSpace
import Data.VectorSpace.FiniteDimensional
import Data.AffineSpace
import Data.Basis
import Data.AdditiveGroup
    
import qualified Prelude as Hask hiding(foldl)
import qualified Control.Applicative as Hask
import qualified Control.Monad       as Hask
import qualified Data.Foldable       as Hask


import Control.Category.Constrained.Prelude hiding ((^))
import Control.Arrow.Constrained

import Data.Manifold.Types.Primitive

import qualified Data.Vector as Arr
import qualified Numeric.LinearAlgebra.HMatrix as HMat


    
-- | A linear mapping between finite-dimensional spaces, implemeted as a dense matrix.
data Linear s a b = Linear { getDenseMatrix :: HMat.Matrix s }

identMat :: forall v w . FiniteDimensional v => Linear (Scalar v) w v
identMat = Linear $ HMat.ident n
 where (Tagged n) = dimension :: Tagged v Int

instance (SmoothScalar s) => Category (Linear s) where
  type Object (Linear s) v = (FiniteDimensional v, Scalar v~s)
  id = identMat
  Linear f . Linear g = Linear $ f * g

instance Cartesian (Linear ℝ) where
  type UnitObject (Linear ℝ) = ZeroDim ℝ
  swap = lSwap
  attachUnit = identMat
  detachUnit = identMat
  regroup = identMat
  regroup' = identMat


lSwap :: forall v w . (FiniteDimensional v, FiniteDimensional w, Scalar v~ℝ, Scalar w~ℝ)
          => Linear ℝ (v,w) (w,v)
lSwap = Linear $ HMat.toDense l
 where l = [ ((i,i+nv), 1) | i<-[0.. nw-1] ] ++ [ ((i+nv,i), 1) | i<-[0.. nw-1] ] 
       (Tagged nv) = dimension :: Tagged v Int
       (Tagged nw) = dimension :: Tagged w Int




