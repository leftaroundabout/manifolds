-- |
-- Module      : Data.Manifold.TreeCover
-- Copyright   : (c) Justus Sagemüller 2015
-- License     : GPL v3
-- 
-- Maintainer  : (@) sagemueller $ geo.uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 
{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE UndecidableInstances     #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE FunctionalDependencies   #-}
{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE RankNTypes               #-}
{-# LANGUAGE TupleSections            #-}
{-# LANGUAGE ConstraintKinds          #-}
{-# LANGUAGE PatternGuards            #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE ScopedTypeVariables      #-}
{-# LANGUAGE RecordWildCards          #-}
{-# LANGUAGE CPP                      #-}


module Data.Manifold.TreeCover where


import Data.List
import Data.Maybe
import Data.Semigroup
import Data.Function (on)
import Data.Fixed

import Data.VectorSpace
import Data.LinearMap
import Data.LinearMap.HerMetric
import Data.MemoTrie (HasTrie)
import Data.AffineSpace
import Data.Basis
import Data.Complex hiding (magnitude)
import Data.Void
import Data.Tagged

import Data.Manifold.Types
import Data.Manifold.PseudoAffine

import qualified Prelude as Hask
import qualified Control.Monad as Hask

import Control.Category.Constrained.Prelude hiding ((^))
import Control.Arrow.Constrained
import Control.Monad.Constrained
import Data.Foldable.Constrained



data Shade v = Shade { shadeCtr :: v
                     , shadeExpanse :: HerMetric' (PseudoDiff v) }

class PseudoAffine v => HasTreeCover v where
  branchShades :: Shade v -> [Shade v]
  -- | This basically amounts to requiring an 'InnerSpace' instance with real scalars.
  occlusion :: Shade v -> v -> ℝ

innerOcclusion :: ( PseudoAffine m, v~PseudoDiff m
                  , HasMetric v, InnerSpace v, v~DualSpace v, Scalar v~ℝ)
        => Shade m -> m -> ℝ
innerOcclusion (Shade p₀ δ) p
   = case p .-~. p₀ of
      Option(Just vd) -> metricSq' δ vd / magnitudeSq vd^2
      _               -> 0

instance (RealDimension s) => HasTreeCover (ZeroDim s) where
  branchShades _ = []
  occlusion _ _ = 1

instance HasTreeCover ℝ where
  branchShades (Shade x δ)
       = let r = 1 / metric' δ 1
             δ₂ = projector' $ r/2
         in [ Shade (x-r) δ₂, Shade (x+r) δ₂ ]
  occlusion = innerOcclusion

-- instance (HasTreeCover x, HasTreeCover y) => HasTreeCover (x,y) where
--   branchShades (Shade xy δ)
--        = let δx = transformMetric
  
  
--   data TreeCovMap v p :: *
--   fromList :: (v,p) -> TreeCovMap v p
--   occlusion :: TreeCovMap v p -> (v, Metric' (PseudoDiff v))
--   branches :: TreeCovMap v p -> [TreeCovMap v p]
--   linearApprox :: 
-- 
-- 
-- newtype TreeCovSet v = TreeCovSet { getTreeCovSet :: TreeCovMap v () }

