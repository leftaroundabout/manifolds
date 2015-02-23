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
                     , shadeExpanse :: Metric' (PseudoDiff v) }

class PseudoAffine v => HasTreeCover v where
  branchShades :: Shade v -> [Shade v]
  occludes :: Shade v -> v -> Bool

instance (RealDimension s) => HasTreeCover (ZeroDim s)
  brachShades _ = []
  occludes _ _ = True
  
--   data TreeCovMap v p :: *
--   fromList :: (v,p) -> TreeCovMap v p
--   occlusion :: TreeCovMap v p -> (v, Metric' (PseudoDiff v))
--   branches :: TreeCovMap v p -> [TreeCovMap v p]
--   linearApprox :: 
-- 
-- 
-- newtype TreeCovSet v = TreeCovSet { getTreeCovSet :: TreeCovMap v () }

