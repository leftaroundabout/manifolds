-- |
-- Module      : Data.Manifold.Riemannian
-- Copyright   : (c) Justus Sagemüller 2015
-- License     : GPL v3
-- 
-- Maintainer  : (@) sagemueller $ geo.uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 
-- Riemannian manifolds are manifolds equipped with a 'Metric' at each point.
-- That means, these manifolds aren't merely topological objects anymore, but
-- have a geometry as well. This gives, in particular, a notion of distance
-- and shortest paths (geodesics) along which you can interpolate.
-- 
-- Keep in mind that the types in this library are
-- generally defined in an abstract-mathematical spirit, which may not always
-- match the intuition if you think about manifolds as embedded in ℝ³.
-- (For instance, the torus inherits its geometry from the decomposition as
-- @'S¹' × 'S¹'@, not from the “doughnut” embedding; the cone over @S¹@ is
-- simply treated as the unit disk, etc..)

{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE ParallelListComp           #-}
{-# LANGUAGE UnicodeSyntax              #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE PatternGuards              #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE LiberalTypeSynonyms        #-}
{-# LANGUAGE CPP                        #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DefaultSignatures          #-}


module Data.Manifold.Riemannian  where


import Data.Maybe
import qualified Data.Vector as Arr

import Data.VectorSpace
import Data.VectorSpace.Free
import Data.AffineSpace
import Math.LinearMap.Category
import Linear (V0(..), V1(..), V2(..), V3(..), V4(..))

import Data.Manifold.Types
import Data.Manifold.Types.Primitive ((^), empty, embed, coEmbed)
import Data.Manifold.Types.Stiefel
import Data.Manifold.PseudoAffine
    
import Data.CoNat

import qualified Prelude as Hask hiding(foldl, sum, sequence)
import qualified Control.Applicative as Hask
import qualified Control.Monad       as Hask hiding(forM_, sequence)
import Data.Functor.Identity
import qualified Data.Foldable       as Hask
import qualified Data.Traversable as Hask

import Control.Category.Constrained.Prelude hiding
     ((^), all, elem, sum, forM, Foldable(..), Traversable)
import Control.Arrow.Constrained
import Control.Monad.Constrained hiding (forM)
import Data.Foldable.Constrained


data GeodesicWitness x where
  GeodesicWitness :: Geodesic (Interior x)
       => SemimanifoldWitness x -> GeodesicWitness x

class Semimanifold x => Geodesic x where
  geodesicBetween ::
          x -- ^ Starting point; the interpolation will yield this at -1.
       -> x -- ^ End point, for +1.
            -- 
            --   If the two points are actually connected by a path...
       -> Maybe (D¹ -> x) -- ^ ...then this is the interpolation function. Attention: 
                          --   the type will change to 'Differentiable' in the future.
  geodesicWitness :: GeodesicWitness x
  default geodesicWitness :: Geodesic (Interior x) => GeodesicWitness x
  geodesicWitness = GeodesicWitness semimanifoldWitness

interpolate :: (Geodesic x, IntervalLike i) => x -> x -> Maybe (i -> x)
interpolate a b = (. toClosedInterval) <$> geodesicBetween a b




#define deriveAffineGD(x)                                         \
instance Geodesic x where {                                        \
  geodesicBetween a b = return $ alerp a b . (/2) . (+1) . xParamD¹ \
 }

deriveAffineGD (ℝ)

instance Geodesic (ZeroDim s) where
  geodesicBetween Origin Origin = return $ \_ -> Origin

instance ∀ a b . (Geodesic a, Geodesic b) => Geodesic (a,b) where
  geodesicBetween (a,b) (α,β) = liftA2 (&&&) (geodesicBetween a α) (geodesicBetween b β)
  geodesicWitness = case ( geodesicWitness :: GeodesicWitness a
                         , geodesicWitness :: GeodesicWitness b ) of
     (GeodesicWitness _, GeodesicWitness _) -> GeodesicWitness semimanifoldWitness

instance ∀ a b c . (Geodesic a, Geodesic b, Geodesic c) => Geodesic (a,b,c) where
  geodesicBetween (a,b,c) (α,β,γ)
      = liftA3 (\ia ib ic t -> (ia t, ib t, ic t))
           (geodesicBetween a α) (geodesicBetween b β) (geodesicBetween c γ)
  geodesicWitness = case ( geodesicWitness :: GeodesicWitness a
                         , geodesicWitness :: GeodesicWitness b
                         , geodesicWitness :: GeodesicWitness c ) of
     (GeodesicWitness _, GeodesicWitness _, GeodesicWitness _)
         -> GeodesicWitness semimanifoldWitness

-- instance (KnownNat n) => Geodesic (FreeVect n ℝ) where
--   geodesicBetween (FreeVect v) (FreeVect w)
--       = return $ \(D¹ t) -> let μv = (1-t)/2; μw = (t+1)/2
--                             in FreeVect $ Arr.zipWith (\vi wi -> μv*vi + μw*wi) v w

instance ∀ v . ( Geodesic v, FiniteFreeSpace v, FiniteFreeSpace (DualVector v)
               , LinearSpace v, Scalar v ~ ℝ, Geodesic (DualVector v)
               , InnerSpace (DualVector v) )
             => Geodesic (Stiefel1 v) where
  geodesicBetween = gb dualSpaceWitness
   where gb :: DualSpaceWitness v -> Stiefel1 v -> Stiefel1 v -> Maybe (D¹ -> Stiefel1 v)
         gb DualSpaceWitness (Stiefel1 p') (Stiefel1 q')
           = (\f -> \(D¹ t) -> Stiefel1 . f . D¹ $ g * tan (ϑ*t))
            <$> geodesicBetween p q
          where p = normalized p'; q = normalized q'
                l = magnitude $ p^-^q
                ϑ = asin $ l/2
                g = sqrt $ 4/l^2 - 1


instance Geodesic S⁰ where
  geodesicBetween PositiveHalfSphere PositiveHalfSphere = return $ const PositiveHalfSphere
  geodesicBetween NegativeHalfSphere NegativeHalfSphere = return $ const NegativeHalfSphere
  geodesicBetween _ _ = empty

instance Geodesic S¹ where
  geodesicBetween (S¹ φ) (S¹ ϕ)
    | abs (φ-ϕ) < pi  = (>>> S¹) <$> geodesicBetween φ ϕ
    | φ > 0           = (>>> S¹ . \ψ -> signum ψ*pi - ψ)
                        <$> geodesicBetween (pi-φ) (-ϕ-pi)
    | otherwise       = (>>> S¹ . \ψ -> signum ψ*pi - ψ)
                        <$> geodesicBetween (-pi-φ) (pi-ϕ)


-- instance Geodesic (Cℝay S⁰) where
--   geodesicBetween p q = (>>> fromℝ) <$> geodesicBetween (toℝ p) (toℝ q)
--    where toℝ (Cℝay h PositiveHalfSphere) = h
--          toℝ (Cℝay h NegativeHalfSphere) = -h
--          fromℝ x | x>0        = Cℝay x PositiveHalfSphere
--                  | otherwise  = Cℝay (-x) NegativeHalfSphere
-- 
-- instance Geodesic (CD¹ S⁰) where
--   geodesicBetween p q = (>>> fromI) <$> geodesicBetween (toI p) (toI q)
--    where toI (CD¹ h PositiveHalfSphere) = h
--          toI (CD¹ h NegativeHalfSphere) = -h
--          fromI x | x>0        = CD¹ x PositiveHalfSphere
--                  | otherwise  = CD¹ (-x) NegativeHalfSphere
-- 
-- instance Geodesic (Cℝay S¹) where
--   geodesicBetween p q = (>>> fromP) <$> geodesicBetween (toP p) (toP q)
--    where fromP = fromInterior
--          toP w = case toInterior w of {Just i -> i}
-- 
-- instance Geodesic (CD¹ S¹) where
--   geodesicBetween p q = (>>> fromI) <$> geodesicBetween (toI p) (toI q)
--    where toI (CD¹ h (S¹ φ)) = (h*cos φ, h*sin φ)
--          fromI (x,y) = CD¹ (sqrt $ x^2+y^2) (S¹ $ atan2 y x)
-- 
-- instance Geodesic (Cℝay S²) where
--   geodesicBetween p q = (>>> fromP) <$> geodesicBetween (toP p) (toP q)
--    where fromP = fromInterior
--          toP w = case toInterior w of {Just i -> i}
-- 
-- instance Geodesic (CD¹ S²) where
--   geodesicBetween p q = (>>> fromI) <$> geodesicBetween (toI p) (toI q :: ℝ³)
--    where toI (CD¹ h sph) = h *^ embed sph
--          fromI v = CD¹ (magnitude v) (coEmbed v)

#define geoVSpCone(c,t)                                               \
instance (c) => Geodesic (Cℝay (t)) where {                            \
  geodesicBetween p q = (>>> fromP) <$> geodesicBetween (toP p) (toP q) \
   where { fromP (x,0) = Cℝay 0 x                                        \
         ; fromP (x,h) = Cℝay h (x^/h)                                    \
         ; toP (Cℝay h w) = ( h*^w, h ) } } ;                              \
instance (c) => Geodesic (CD¹ (t)) where {                                  \
  geodesicBetween p q = (>>> fromP) <$> geodesicBetween (toP p) (toP q)      \
   where { fromP (x,0) = CD¹ 0 x                                              \
         ; fromP (x,h) = CD¹ h (x^/h)                                          \
         ; toP (CD¹ h w) = ( h*^w, h ) } }

-- geoVSpCone ((), ℝ)
-- geoVSpCone ((), ℝ⁰)
-- geoVSpCone ((WithField ℝ HilbertManifold a, WithField ℝ HilbertManifold b
--             , Geodesic (a,b)), (a,b))
-- geoVSpCone (KnownNat n, FreeVect n ℝ)

deriveAffineGD ((V0 ℝ))
deriveAffineGD (ℝ¹)
deriveAffineGD (ℝ²)
deriveAffineGD (ℝ³)
deriveAffineGD (ℝ⁴)



-- | One-dimensional manifolds, whose closure is homeomorpic to the unit interval.
class WithField ℝ PseudoAffine i => IntervalLike i where
  toClosedInterval :: i -> D¹ -- Differentiable ℝ i D¹

instance IntervalLike D¹ where
  toClosedInterval = id
-- instance IntervalLike (CD¹ S⁰) where
--   toClosedInterval (CD¹ h PositiveHalfSphere) = D¹ h
--   toClosedInterval (CD¹ h NegativeHalfSphere) = D¹ (-h)
-- instance IntervalLike (Cℝay S⁰) where
--   toClosedInterval (Cℝay h PositiveHalfSphere) = D¹ $ tanh h
--   toClosedInterval (Cℝay h NegativeHalfSphere) = D¹ $ -tanh h
-- instance IntervalLike (CD¹ ℝ⁰) where
--   toClosedInterval (CD¹ h Origin) = D¹ $ h*2 - 1
-- instance IntervalLike (Cℝay ℝ⁰) where
--   toClosedInterval (Cℝay h Origin) = D¹ $ 1 - 2/(h+1)
instance IntervalLike ℝ where
  toClosedInterval x = D¹ $ tanh x





class Geodesic m => Riemannian m where
  rieMetric :: RieMetric m

instance Riemannian ℝ where
  rieMetric = const euclideanNorm




middleBetween :: Geodesic m => m -> m -> Maybe m
middleBetween p₀ p₁ = ($ D¹ 0) <$> geodesicBetween p₀ p₁
