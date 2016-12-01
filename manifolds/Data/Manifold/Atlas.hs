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

