-- |
-- Module      : Data.Manifold.FibreBundle
-- Copyright   : (c) Justus Sagemüller 2018
-- License     : GPL v3
-- 
-- Maintainer  : (@) sagemueller $ geo.uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 

{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE UnicodeSyntax              #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE CPP                        #-}
#if __GLASGOW_HASKELL__ >= 800
{-# LANGUAGE UndecidableSuperClasses    #-}
#endif


module Data.Manifold.FibreBundle where


import Data.AdditiveGroup
import Data.VectorSpace
import Math.LinearMap.Category

import Data.Manifold.Types.Primitive
import Data.Manifold.PseudoAffine
    
import qualified Prelude as Hask

import Control.Category.Constrained.Prelude
import Control.Category.Discrete
import Control.Arrow.Constrained

import Linear.V2 (V2(V2))
import Linear.V3 (V3(V3))

import Data.Tagged


data TransportOnNeedleWitness k m f where
  TransportOnNeedle :: (ParallelTransporting (LinearFunction (Scalar (Needle m)))
                                             (Needle m) (Needle f))
                     => TransportOnNeedleWitness k m f

data ForgetTransportProperties k m f where
  ForgetTransportProperties :: ParallelTransporting (->) m f
                     => ForgetTransportProperties k m f

class (PseudoAffine m, m ~ Interior m, Category k, Object k f)
           => ParallelTransporting k m f where
  transportOnNeedleWitness :: TransportOnNeedleWitness k m f
  default transportOnNeedleWitness
      :: ParallelTransporting (LinearFunction (Scalar (Needle m))) (Needle m) (Needle f)
           => TransportOnNeedleWitness k m f
  transportOnNeedleWitness = TransportOnNeedle
  forgetTransportProperties :: ForgetTransportProperties k m f
  default forgetTransportProperties :: ParallelTransporting (->) m f
           => ForgetTransportProperties k m f
  forgetTransportProperties = ForgetTransportProperties
  
  parallelTransport :: m -> Needle m -> k f f
  translateAndInvblyParTransport
        :: m -> Needle m -> (m, (k f f, k f f))
  translateAndInvblyParTransport p v
              = (q, ( parallelTransport p v
                    , parallelTransport q $ p.-~!q ))
   where q = p.+~^v

instance ∀ m s . (PseudoAffine m, m ~ Interior m, s ~ (Scalar (Needle m)), Num' s)
      => ParallelTransporting Discrete m (ZeroDim s) where
  transportOnNeedleWitness = case (pseudoAffineWitness :: PseudoAffineWitness m) of
    (PseudoAffineWitness (SemimanifoldWitness BoundarylessWitness)) -> TransportOnNeedle
  forgetTransportProperties = case (pseudoAffineWitness :: PseudoAffineWitness m) of
    (PseudoAffineWitness (SemimanifoldWitness BoundarylessWitness))
        -> ForgetTransportProperties
  parallelTransport _ _ = id
instance ∀ m s . (PseudoAffine m, m ~ Interior m, s ~ (Scalar (Needle m)), Num' s)
      => ParallelTransporting (LinearFunction s) m (ZeroDim s) where
  transportOnNeedleWitness = case (pseudoAffineWitness :: PseudoAffineWitness m) of
    (PseudoAffineWitness (SemimanifoldWitness BoundarylessWitness)) -> TransportOnNeedle
  forgetTransportProperties = case (pseudoAffineWitness :: PseudoAffineWitness m) of
    (PseudoAffineWitness (SemimanifoldWitness BoundarylessWitness))
        -> ForgetTransportProperties
  parallelTransport _ _ = id
instance ∀ m s . (PseudoAffine m, m ~ Interior m, s ~ (Scalar (Needle m)), Num' s)
      => ParallelTransporting (->) m (ZeroDim s) where
  transportOnNeedleWitness = case (pseudoAffineWitness :: PseudoAffineWitness m) of
    (PseudoAffineWitness (SemimanifoldWitness BoundarylessWitness)) -> TransportOnNeedle
  forgetTransportProperties = case (pseudoAffineWitness :: PseudoAffineWitness m) of
    (PseudoAffineWitness (SemimanifoldWitness BoundarylessWitness))
        -> ForgetTransportProperties
  parallelTransport _ _ = id

instance (Category k, Object k ℝ) => ParallelTransporting k ℝ ℝ where
  parallelTransport _ _ = id
instance (Category k, Object k ℝ²) => ParallelTransporting k ℝ² ℝ² where
  parallelTransport _ _ = id
instance (Category k, Object k ℝ³) => ParallelTransporting k ℝ³ ℝ³ where
  parallelTransport _ _ = id
instance (Category k, Object k ℝ⁴) => ParallelTransporting k ℝ⁴ ℝ⁴ where
  parallelTransport _ _ = id

instance (Category k, Object k ℝ) => ParallelTransporting k S¹ ℝ where
  parallelTransport _ _ = id

instance (EnhancedCat k (LinearMap ℝ), Object k ℝ²)
             => ParallelTransporting k S² ℝ² where
  parallelTransport p v = (fst . snd) (translateAndInvblyParTransport p v)
  translateAndInvblyParTransport (S² θ₀ φ₀) 𝐯
              = (S² θ₁ φ₁, (arr fwd, arr bwd))
   where -- See images/constructions/sphericoords-needles.svg. Translation as in
         -- "Data.Manifold.PseudoAffine" instance.
         S¹ γc₀ = coEmbed 𝐯
         γ₀ | θ₀ < pi/2   = γc₀ + φ₀
            | otherwise   = γc₀ - φ₀
         d = magnitude 𝐯
         S¹ φ₁ = S¹ φ₀ .+~^ δφ
         
         -- Cartesian coordinates of p₁ in the system whose north pole is p₀
         -- with φ₀ as the zero meridian
         V3 bx by bz = embed $ S² d γ₀
         
         sθ₀ = sin θ₀; cθ₀ = cos θ₀
         -- Cartesian coordinates of p₁ in the system with the standard north pole,
         -- but still φ₀ as the zero meridian
         (qx,qz) = ( cθ₀ * bx + sθ₀ * bz
                   ,-sθ₀ * bx + cθ₀ * bz )
         qy      = by
         
         S² θ₁ δφ = coEmbed $ V3 qx qy qz
         
         -- Cartesian coordinates of the standard north pole in the system whose north
         -- pole is p₀ with 𝐯 along the zero meridian
         V3 nbx nby nbz = embed $ S² θ₀ (pi-γ₀)
         
         sd = sin d; cd = cos d
         -- Cartesian coordinates of the standard north pole in the system whose north
         -- pole is p₁ with 𝐯 along the zero meridian
         (ox,oz) = ( cd * nbx - sd * nbz
                   , sd * nbx + cd * nbz )
         oy      = nby

         γ₁ = atan2 oy (-ox)

         γc₁ | θ₁ < pi/2  = γ₁ - φ₁
             | otherwise  = γ₁ + φ₁

         (sδγc, cδγc) = sin &&& cos $ γc₁ - γc₀

         fwd = LinearMap (V2 (V2   cδγc  sδγc)
                             (V2 (-sδγc) cδγc)) :: LinearMap ℝ ℝ² ℝ²
         bwd = LinearMap (V2 (V2 cδγc (-sδγc))
                             (V2 sδγc   cδγc )) :: LinearMap ℝ ℝ² ℝ²


instance {-# OVERLAPS #-} ∀ k a b fa fb s .
         ( ParallelTransporting k a fa, ParallelTransporting k b fb
         , PseudoAffine fa, PseudoAffine fb
         , Scalar (Needle a) ~ s, Scalar (Needle b) ~ s
         , Scalar (Needle fa) ~ s, Scalar (Needle fb) ~ s
         , Num' s
         , Morphism k, ObjectPair k fa fb )
              => ParallelTransporting k (a,b) (fa,fb) where
  transportOnNeedleWitness = case
         ( pseudoAffineWitness :: PseudoAffineWitness a
         , pseudoAffineWitness :: PseudoAffineWitness b
         , pseudoAffineWitness :: PseudoAffineWitness fa
         , pseudoAffineWitness :: PseudoAffineWitness fb
         , transportOnNeedleWitness :: TransportOnNeedleWitness k a fa
         , transportOnNeedleWitness :: TransportOnNeedleWitness k b fb ) of
     ( PseudoAffineWitness (SemimanifoldWitness BoundarylessWitness)
      ,PseudoAffineWitness (SemimanifoldWitness BoundarylessWitness)
      ,PseudoAffineWitness (SemimanifoldWitness BoundarylessWitness)
      ,PseudoAffineWitness (SemimanifoldWitness BoundarylessWitness)
      ,TransportOnNeedle, TransportOnNeedle)
         -> TransportOnNeedle
  forgetTransportProperties = case
    ( forgetTransportProperties :: ForgetTransportProperties k a fa
    , forgetTransportProperties :: ForgetTransportProperties k b fb ) of
     (ForgetTransportProperties, ForgetTransportProperties) -> ForgetTransportProperties
  parallelTransport (pa,pb) (va,vb)
       = parallelTransport pa va  *** parallelTransport pb vb

instance ∀ k a f g s .
         ( ParallelTransporting k a f, ParallelTransporting k a g
         , ParallelTransporting (LinearFunction s) (Needle a) (Needle f, Needle g)
         , PseudoAffine f, PseudoAffine g
         , Morphism k, ObjectPair k f g )
              => ParallelTransporting k a (f,g) where
  transportOnNeedleWitness = case
         ( pseudoAffineWitness :: PseudoAffineWitness a
         , pseudoAffineWitness :: PseudoAffineWitness f
         , pseudoAffineWitness :: PseudoAffineWitness g
         , transportOnNeedleWitness :: TransportOnNeedleWitness k a f
         , transportOnNeedleWitness :: TransportOnNeedleWitness k a g ) of
     ( PseudoAffineWitness (SemimanifoldWitness BoundarylessWitness)
      ,PseudoAffineWitness (SemimanifoldWitness BoundarylessWitness)
      ,PseudoAffineWitness (SemimanifoldWitness BoundarylessWitness)
      ,TransportOnNeedle, TransportOnNeedle)
         -> TransportOnNeedle
  forgetTransportProperties = case
    ( forgetTransportProperties :: ForgetTransportProperties k a f
    , forgetTransportProperties :: ForgetTransportProperties k a g ) of
     (ForgetTransportProperties, ForgetTransportProperties) -> ForgetTransportProperties
  parallelTransport p v
       = parallelTransport p v *** parallelTransport p v


instance ( ParallelTransporting (LinearFunction (Scalar f)) m f, AdditiveGroup m
         , VectorSpace f )
                => AdditiveGroup (FibreBundle m f) where
  zeroV = FibreBundle zeroV zeroV
  FibreBundle p v ^+^ FibreBundle q w = FibreBundle (p^+^q) (v^+^w)
  negateV (FibreBundle p v) = FibreBundle (negateV p) (negateV v)

instance ∀ m f s .
         ( ParallelTransporting (->) m (Interior f), Semimanifold f
         , ParallelTransporting (LinearFunction s) (Needle m) (Needle f)
         , s ~ Scalar (Needle m) )
                => Semimanifold (FibreBundle m f) where
  type Interior (FibreBundle m f) = FibreBundle m (Interior f)
  type Needle (FibreBundle m f) = FibreBundle (Needle m) (Needle f)
  toInterior (FibreBundle p f) = FibreBundle p <$> toInterior f
  translateP = Tagged $ case ( translateP :: Tagged m (Interior m -> Needle m -> Interior m)
                             , semimanifoldWitness :: SemimanifoldWitness f) of
      (Tagged tpm, SemimanifoldWitness BoundarylessWitness)
           -> \(FibreBundle p f) (FibreBundle v δf)
                   -> FibreBundle (tpm p v) (parallelTransport p v f.+~^δf)
  semimanifoldWitness = case ( semimanifoldWitness :: SemimanifoldWitness m
                             , semimanifoldWitness :: SemimanifoldWitness f
                             , forgetTransportProperties
                               :: ForgetTransportProperties (LinearFunction s) (Needle m) (Needle f)
                             ) of
         (SemimanifoldWitness BoundarylessWitness, SemimanifoldWitness BoundarylessWitness
          ,ForgetTransportProperties)
           -> SemimanifoldWitness BoundarylessWitness
  FibreBundle p f .+~^ FibreBundle v δf
      = FibreBundle (p.+~^v) (parallelTransport p v f.+~^δf)

instance ∀ m f s .
         ( ParallelTransporting (->) m f, ParallelTransporting (->) m (Interior f)
         , PseudoAffine f
         , ParallelTransporting (LinearFunction s) (Needle m) (Needle f)
         , s ~ Scalar (Needle m) )
                => PseudoAffine (FibreBundle m f) where
  pseudoAffineWitness = case ( pseudoAffineWitness :: PseudoAffineWitness m
                             , pseudoAffineWitness :: PseudoAffineWitness f
                             , forgetTransportProperties
                               :: ForgetTransportProperties (LinearFunction s) (Needle m) (Needle f)
                             ) of
     ( PseudoAffineWitness (SemimanifoldWitness BoundarylessWitness)
      ,PseudoAffineWitness (SemimanifoldWitness BoundarylessWitness)
      ,ForgetTransportProperties)
         -> PseudoAffineWitness (SemimanifoldWitness BoundarylessWitness)
  FibreBundle p f .-~. FibreBundle q g = case p.-~.q of
      Nothing -> Nothing
      Just v  -> FibreBundle v <$> f .-~. parallelTransport p v g
