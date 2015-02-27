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

class ( PseudoAffine x
      , HasMetric (PseudoDiff x), HasMetric (DualSpace (PseudoDiff x))
      , Scalar (DualSpace (PseudoDiff x)) ~ Scalar (PseudoDiff x)
      ) => HasTreeCover x where
  branchShades :: Shade x -> [Shade x]
  
-- | Check the statistical likelyhood of a point being within a shade.
occlusion :: (HasTreeCover x, s ~ Scalar (PseudoDiff x), RealDimension s)
                => Shade x -> x -> s
occlusion (Shade p₀ δ) = occ
 where occ p = case p .-~. p₀ of
         Option(Just vd) -> exp . negate $ metricSq δinv vd
         _               -> zeroV
       δinv = recipMetric δ

-- instance (RealDimension s) => HasTreeCover (ZeroDim s) where
  -- branchShades _ = []

instance HasTreeCover ℝ where
  branchShades (Shade x δ)
       = let r = 1 / metric' δ 1
             δ₂ = projector' $ r/2
         in [ Shade (x-r) δ₂, Shade (x+r) δ₂ ]

instance ( HasTreeCover x, HasTreeCover y
         , v ~ PseudoDiff x, w ~ PseudoDiff y
         , v ~ DualSpace v, w ~ DualSpace w
         , InnerSpace v, InnerSpace w
         , s~Scalar v, s~Scalar w, Fractional s
         , DualSpace (DualSpace v) ~ v, DualSpace (DualSpace w) ~ w
         , Scalar (DualSpace v) ~ Scalar v, Scalar (DualSpace w) ~ Scalar w
         ) => HasTreeCover (x,y) where
  branchShades = brcs
   where brcs (Shade (x,y) δ)
           = let δx = transformMetric' lfst δ
                 δx0 = transformMetric' lcofst δx
                 δy = transformMetric' lsnd δ
                 δ0y = transformMetric' lcosnd δy
                 shxs = fmap (\(Shade x' δx')
                           -> Shade (x',y) (transformMetric' lcofst δx' ^+^ δ0y)
                         ) $ branchShades (Shade x δx)
                 shys = fmap (\(Shade y' δy')
                           -> Shade (x,y') (δx0 ^+^ transformMetric' lcosnd δy')
                         ) $ branchShades (Shade y δy)
             in intlv shxs shys
         intlv [] r = r
         intlv l [] = l
         intlv (a:l) (b:r) = a : b : intlv l r
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

