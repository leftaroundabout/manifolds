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
type D_S x = WithField ℝ Manifold x

instance D_S x => Distribution Shade x where
  rvarT (Shade c e) = shadeT' c e

shadeT' :: (PseudoAffine x, HasMetric (Needle x), Scalar (Needle x) ~ ℝ)
                      => x -> HerMetric' (Needle x) -> RVarT m x
shadeT' ctr expa = ((ctr.+~^) . sumV) <$> mapM (\v -> (v^*) <$> stdNormalT) eigSpan
   where eigSpan = eigenSpan expa

-- | A shade can be considered a specification for a generalised normal distribution.
-- 
--   If you use 'rvar' to sample a large number of points from a shade @sh@ in a sufficiently
--   flat space, then 'pointsShades' of that sample will again be approximately @[sh]@.
shade :: (Distribution Shade x, D_S x) => x -> HerMetric' (Needle x) -> RVar x
shade ctr expa = rvar $ fullShade ctr expa

shadeT :: (Distribution Shade x, D_S x) => x -> HerMetric' (Needle x) -> RVarT m x
shadeT = shadeT'
