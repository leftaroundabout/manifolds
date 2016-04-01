{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE UnicodeSyntax         #-}

module Data.Random.Manifold (shade, shadeT, D_S, uncertainFunctionSamplesT, uncrtFuncIntervalSpls) where

import Prelude hiding (($))
import Control.Category.Constrained.Prelude (($))

import Data.VectorSpace
import Data.AffineSpace
import Data.LinearMap
import Data.LinearMap.HerMetric
import Data.Manifold.Types
import Data.Manifold.PseudoAffine
import Data.Manifold.TreeCover

import Data.Semigroup

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




uncertainFunctionSamplesT :: ∀ x y m .
                       (Distribution Shade x, D_S x, Distribution Shade y, D_S y)
                => Int -> Shade x -> (x -> Shade y) -> RVarT m (x`Shaded`y)
uncertainFunctionSamplesT n shx f = do
      domainSpls <- replicateM n $ rvarT shx
      pts <- forM domainSpls $ \x -> do
         y <- rvarT $ f x
         return (WithAny y x)
      let t₀ = fromLeafPoints pts
          ntwigs = length $ twigsWithEnvirons t₀
          nPerTwig = fromIntegral n / fromIntegral ntwigs
          ensureThickness :: Shade' (x,y) -> RVarT m (Shade' y, Linear ℝ (Needle x) (Needle y))
          ensureThickness shl@(Shade' (xlc,ylc) expa) = do
             let Option (Just jOrig) = covariance $ recipMetric' expa
                 (expax,expay) = factoriseMetric expa
                 expax' = recipMetric' expax
                 mkControlSample css confidence
                  | confidence > 6  = return css
                  | otherwise  = do
                              -- exaggerate deviations a bit here, to avoid clustering
                              -- in center of normal distribution.
                       x <- rvarT (Shade xlc $ expax'^*1.5)
                       let Shade ylc expaly = f x
                       y <- rvarT $ Shade ylc (expaly^*1.5)
                       mkControlSample ((x,y):css)
                         $ confidence + occlusion shl (x,y)
             css <- mkControlSample [] 0
             let [Shade (xCtrl,yCtrl) expaCtrl] = pointsShades css
                 expayCtrl = recipMetric . snd $ factoriseMetric' expaCtrl
                 Option (Just jCtrl) = covariance expaCtrl
                 jFin = jOrig^*η ^+^ jCtrl^*η'
                 Option (Just δx) = xlc.-~.xCtrl
                 yCtrl' = yCtrl .+~^ (jFin $ δx)
                 η, η' :: ℝ
                 η = nPerTwig / (nPerTwig + fromIntegral (length css))
                 η' = 1 - η
                 yCtrl' :: y
                 Option (Just δy) = yCtrl'.-~.ylc
             return (Shade' (ylc .+~^ δy^*η') (expay^*η ^+^ expayCtrl^*η'), jFin)
      flexTwigsShading ensureThickness t₀

uncrtFuncIntervalSpls :: (x~ℝ, y~ℝ)
      => Int -> (x,x) -> (x -> (y, Diff y)) -> RVar (x`Shaded`y)
uncrtFuncIntervalSpls n (xl,xr) f
      = uncertainFunctionSamplesT n
            (Shade ((xl+xr)/2) $ projector' ((xr-xl)/2))
            (f >>> \(y,δy) -> Shade y $ projector' δy)
     

