{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE TypeOperators         #-}

module Data.Random.Manifold (shade, shadeT, D_S, uncertainFunctionSamplesT, uncrtFuncIntervalSpls) where

import Data.VectorSpace
import Data.AffineSpace
import Data.LinearMap
import Data.LinearMap.HerMetric
import Data.Manifold.Types
import Data.Manifold.PseudoAffine
import Data.Manifold.TreeCover

import Data.Random
import Data.Random.Distribution
import Data.Random.Distribution.Normal

import Control.Applicative
import Control.Monad
import Control.Arrow

-- |
-- @
-- instance D_S x => 'Distribution' 'Shade' x
-- @
type D_S x = WithField ℝ Manifold x

instance D_S x => Distribution Shade x where
  rvarT (Shade c e) = shadeT' c e

shadeT' :: (PseudoAffine x, HasMetric (Needle x), Scalar (Needle x) ~ ℝ)
                      => Interior x -> HerMetric' (Needle x) -> RVarT m x
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




uncertainFunctionSamplesT :: (Distribution Shade x, D_S x, Distribution Shade y, D_S y)
                => Int -> Shade x -> (x -> Shade y) -> RVarT m (x`Shaded`y)
uncertainFunctionSamplesT n shx f = do
      domainSpls <- replicateM n $ rvarT shx
      pts <- forM domainSpls $ \x -> do
         y <- rvarT $ f x
         return (WithAny y x)
      return $ fromLeafPoints pts

uncrtFuncIntervalSpls :: (x~ℝ, y~ℝ)
      => Int -> (x,x) -> (x -> (y, Diff y)) -> RVar (x`Shaded`y)
uncrtFuncIntervalSpls n (xl,xr) f
      = uncertainFunctionSamplesT n
            (Shade ((xl+xr)/2) $ projector' ((xr-xl)/2))
            (f >>> \(y,δy) -> Shade y $ projector' δy)
     

