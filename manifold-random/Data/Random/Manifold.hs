{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE UndecidableInstances  #-}

module Data.Random.Manifold where

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

instance (PseudoAffine x, HasMetric (PseudoDiff x), Scalar (PseudoDiff x) ~ ℝ)
                      => Distribution Shade x where
  rvarT (Shade ctr expa)
           = ((ctr.+~^) . sumV) <$> mapM (\v -> (v^*) <$> stdNormalT) eigSpan
   where eigSpan = eigenSpan expa

-- | A shade can be considered a specification for a generalised normal distribution.
shade :: Distribution Shade x => x -> HerMetric' (PseudoDiff x) -> RVar x
shade ctr expa = rvar $ Shade ctr expa

shadeT :: Distribution Shade x => x -> HerMetric' (PseudoDiff x) -> RVarT m x
shadeT ctr expa = rvarT $ Shade ctr expa
