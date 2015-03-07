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
import Data.Ord (comparing)
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

subshadeId :: (PseudoAffine x, HasMetric (PseudoDiff x), Scalar (PseudoDiff x) ~ ℝ)
                  => Shade x -> x -> Int
subshadeId (Shade c expa) = \x
             -> case x .-~. c of
                 Option (Just v) -> let (iu,vl) = maximumBy (comparing $ abs . snd)
                                                   $ zip [0,2..] (map (v <.>^) expvs)
                                    in iu + if vl>0 then 1 else 0
                 _ -> -1
                 
 where expvs = eigenCoSpan expa


pointsShades :: (PseudoAffine x, HasMetric (PseudoDiff x), Scalar (PseudoDiff x) ~ ℝ)
                 => [x] -> [Shade x]
pointsShades [] = []
pointsShades ps@(p₀:_) = Shade ctr expa : pointsShades nonreachable
 where (ctr,nonreachable)
             = foldr ( \(i,p) (acc, nr) -> case p.-~.acc of 
                                            Option (Just δ) -> (acc .+~^ δ^/i, nr)
                                            _ -> (acc, p:nr) )
                     (p₀,[])
                     ( zip [1..] ps )
       expa = undefined
       
  
-- | Check the statistical likelyhood of a point being within a shade.
occlusion :: (PseudoAffine x, HasMetric (PseudoDiff x)
             , s ~ (Scalar (PseudoDiff x)), RealDimension s )
                => Shade x -> x -> s
occlusion (Shade p₀ δ) = occ
 where occ p = case p .-~. p₀ of
         Option(Just vd) -> exp . negate $ metricSq δinv vd
         _               -> zeroV
       δinv = recipMetric δ

-- instance (RealDimension s) => HasTreeCover (ZeroDim s) where
  -- branchShades _ = []


