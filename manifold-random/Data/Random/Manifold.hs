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
import Math.LinearMap.Category
import Data.Manifold.Types
import Data.Manifold.PseudoAffine
import Data.Manifold.TreeCover

import Data.Semigroup
import Data.Maybe (catMaybes)

import Data.Random

import Control.Applicative
import Control.Monad
import Control.Arrow

-- |
-- @
-- instance D_S x => 'Distribution' 'Shade' x
-- @
type D_S x = (WithField ℝ PseudoAffine x, SimpleSpace (Needle x))

instance D_S x => Distribution Shade x where
  rvarT (Shade c e) = shadeT' c e

shadeT' :: (PseudoAffine x, SimpleSpace (Needle x), Scalar (Needle x) ~ ℝ)
                      => Interior x -> Variance (Needle x) -> RVarT m x
shadeT' ctr expa = ((ctr.+~^) . sumV) <$> mapM (\v -> (v^*) <$> stdNormalT) eigSpan
   where eigSpan = varianceSpanningSystem expa

-- | A shade can be considered a specification for a generalised normal distribution.
-- 
--   If you use 'rvar' to sample a large number of points from a shade @sh@ in a sufficiently
--   flat space, then 'pointsShades' of that sample will again be approximately @[sh]@.
shade :: (Distribution Shade x, D_S x) => Interior x -> Variance (Needle x) -> RVar x
shade ctr expa = rvar $ fullShade ctr expa

shadeT :: (Distribution Shade x, D_S x) => Interior x -> Variance (Needle x) -> RVarT m x
shadeT = shadeT'




uncertainFunctionSamplesT :: ∀ x y m .
        ( WithField ℝ Manifold x, SimpleSpace (Needle x)
        , WithField ℝ Manifold y, SimpleSpace (Needle y) )
       => Int -> Shade x -> (x -> Shade y) -> RVarT m (x`Shaded`y)
uncertainFunctionSamplesT n shx f = case ( dualSpaceWitness :: DualNeedleWitness x
                                         , dualSpaceWitness :: DualNeedleWitness y
                                         , boundarylessWitness :: BoundarylessWitness x
                                         , pseudoAffineWitness :: PseudoAffineWitness y ) of
    ( DualSpaceWitness, DualSpaceWitness, BoundarylessWitness
     ,PseudoAffineWitness (SemimanifoldWitness BoundarylessWitness) ) -> do
      domainSpls <- replicateM n $ rvarT shx
      pts <- forM domainSpls $ \x -> do
         y <- rvarT $ f x
         return (WithAny y x)
      let t₀ = fromLeafPoints pts
          ntwigs = length $ twigsWithEnvirons t₀
          nPerTwig = fromIntegral n / fromIntegral ntwigs
          ensureThickness :: Shade' (x,y)
                  -> RVarT m (x, (Shade' y, Needle x +> Needle y))
          ensureThickness shl@(Shade' (xlc,ylc) expa) = do
             let jOrig = dependence $ dualNorm expa
                 (expax,expay) = summandSpaceNorms expa
                 expax' = dualNorm expax
                 mkControlSample css confidence
                  | confidence > 6  = return css
                  | otherwise  = do
                              -- exaggerate deviations a bit here, to avoid clustering
                              -- in center of normal distribution.
                       x <- rvarT (Shade xlc $ scaleNorm 1.2 expax')
                       let Shade ylc expaly = f x
                       y <- rvarT $ Shade ylc (scaleNorm 1.2 expaly)
                       mkControlSample ((x,y):css)
                         $ confidence + occlusion shl (x,y)
             css <- mkControlSample [] 0
             let [Shade (xCtrl,yCtrl) expaCtrl :: Shade (x,y)]
                       = pointsShades . catMaybes $ getOption.toInterior<$>css
                 yCtrl :: Interior y
                 expayCtrl = dualNorm . snd $ summandSpaceNorms expaCtrl
                 jCtrl = dependence expaCtrl
                 jFin = jOrig^*η ^+^ jCtrl^*η'
                 Just δx = xlc.-~.xCtrl
                 η, η' :: ℝ
                 η = nPerTwig / (nPerTwig + fromIntegral (length css))
                 η' = 1 - η
                 Just δy = yCtrl.-~.ylc
             return ( xlc .+~^ δx^*η'
                    , ( Shade' (ylc .+~^ δy^*η')
                               (scaleNorm (sqrt η) expay <> scaleNorm (sqrt η') expayCtrl)
                      , jFin ) )
      flexTwigsShading ensureThickness t₀

uncrtFuncIntervalSpls :: (x~ℝ, y~ℝ)
      => Int -> (x,x) -> (x -> (y, Diff y)) -> RVar (x`Shaded`y)
uncrtFuncIntervalSpls n (xl,xr) f
      = uncertainFunctionSamplesT n
            (Shade ((xl+xr)/2) $ spanVariance [(xr-xl)/2])
            (f >>> \(y,δy) -> Shade y $ spanVariance [δy])
     

