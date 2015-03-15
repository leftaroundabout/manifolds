{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE UndecidableInstances  #-}

module Data.Random.Manifold (shade, shadeT, D_S) where

import Data.VectorSpace
import Data.LinearMap
import Data.LinearMap.HerMetric
import Data.Manifold.Types
import Data.Manifold.PseudoAffine
import Data.Manifold.TreeCover

import Data.Random
import Data.Random.Distribution
import Data.Random.Distribution.Normal

import Control.Applicative

-- |
-- @
-- instance D_S x => 'Distribution' 'Shade' x
-- @
type D_S x = (PseudoAffine x, HasMetric (PseudoDiff x), Scalar (PseudoDiff x) ~ ℝ)

instance D_S x => Distribution Shade x where
  rvarT shade = shadeT' (shadeCtr shade) (shadeExpanse shade)

shadeT' :: (PseudoAffine x, HasMetric (PseudoDiff x), Scalar (PseudoDiff x) ~ ℝ)
                      => x -> HerMetric' (PseudoDiff x) -> RVarT m x
shadeT' ctr expa = ((ctr.+~^) . sumV) <$> mapM (\v -> (v^*) <$> stdNormalT) eigSpan
   where eigSpan = eigenSpan expa

-- | A shade can be considered a specification for a generalised normal distribution.
-- 
--   If you use 'rvar' to sample a large number of points from a shade @sh@ in a sufficiently
--   flat space, then 'pointsShades' of that sample will again be approximately @[sh]@.
shade :: (Distribution Shade x, D_S x) => x -> HerMetric' (PseudoDiff x) -> RVar x
shade ctr expa = rvar $ fullShade ctr expa

shadeT :: (Distribution Shade x, D_S x) => x -> HerMetric' (PseudoDiff x) -> RVarT m x
shadeT = shadeT'
