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



data Shade x = Shade { shadeCtr :: x
                     , shadeExpanse :: HerMetric' (PseudoDiff x) }

class PseudoAffine x => HasTreeCover x where
  branchShades :: Shade x -> [Shade x]
  
  -- | This basically amounts to requiring an 'InnerSpace' instance
  --   with real scalars, and then performing @<v|δ|v> / |v|⁴@; but actually
  --   it is more general. At least, it is possible for physical-quantity
  --   spaces, though these are not equal to their dual/reciprocals.
  occlusion :: Shade x -> x -> ℝ

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

instance (HasTreeCover x, HasTreeCover y) => HasTreeCover (x,y) where
  branchShades = brcs
   where brch (Shade (x,y) δ)
           = let δx = transformMetric lfst δ
                 δx0 = transformMetric lcofst δx
                 δy = transformMetric lsnd δ
                 δ0y = transformMetric lcosnd δy
                 shxs = fmap (\(Shade x' δx')
                           -> Shade (x',y) (transformMetric lcofst δx' ^+^ δ0y)
                         ) $ branchShades (Shade x δx)
                 shxs = fmap (\(Shade y' δy')
                           -> Shade (x,y') (δx0 ^+^ transformMetric lcosnd δy')
                         ) $ branchShades (Shade x δx)
             in intlv (fmap 
         lfst = linear fst; lsnd = linear snd
         lcofst = linear(,zeroV); lcosnd = linear(zeroV,)
  
  
--   data TreeCovMap v p :: *
--   fromList :: (v,p) -> TreeCovMap v p
--   occlusion :: TreeCovMap v p -> (v, Metric' (PseudoDiff v))
--   branches :: TreeCovMap v p -> [TreeCovMap v p]
--   linearApprox :: 
-- 
-- 
-- newtype TreeCovSet v = TreeCovSet { getTreeCovSet :: TreeCovMap v () }

