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


module Data.Manifold.PseudoAffine where
    


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
import Data.Manifold.Types

import qualified Prelude

import Control.Category.Constrained.Prelude hiding ((^))
import Control.Arrow.Constrained
import Control.Monad.Constrained
import Data.Foldable.Constrained




infix 6 .-~.
infixl 6 .+~^

-- | 'PseudoAffine' is intended as an alternative class for 'Manifold's. The interface
--   is actually identical to the better-known 'AffineSpace' class, but unlike in the
--   standard mathematical definition of affine spaces we don't require associativity of
--   '.+~^' with '^+^', except in an asymptotic sense for small vectors.
--   
--   That innocent-looking change makes the class applicable to vastly more general types:
--   while an affine space is basically nothing but a vector space without particularly
--   designated origin, a pseudo-affine space can have nontrivial topology on the global
--   scale, and yet be used in practically the same way as an affine space. At least the
--   usual spheres and tori make good instances, perhaps the class is in fact equivalent to
--   /parallelisable path-connected manifolds/.
class PseudoAffine x where
  type PseudoDiff x :: *
  (.-~.) :: x -> x -> PseudoDiff x
  (.+~^) :: x -> PseudoDiff x -> x


palerp :: (PseudoAffine x, VectorSpace (PseudoDiff x))
    => x -> x -> Scalar (PseudoDiff x) -> x
palerp p1 p2 = \t -> p1 .+~^ t *^ v
 where v = p2 .-~. p1



#define deriveAffine(t)          \
instance PseudoAffine t where {   \
  type PseudoDiff t = Diff t;      \
  (.-~.) = (.-.);                   \
  (.+~^) = (.+^)  }

deriveAffine(Double)
deriveAffine(Rational)

instance (PseudoAffine a, PseudoAffine b) => PseudoAffine (a,b) where
  type PseudoDiff (a,b) = (PseudoDiff a, PseudoDiff b)
  (a,b).-~.(c,d) = (a.-~.c, b.-~.d)
  (a,b).+~^(v,w) = (a.+~^v, b.+~^w)
instance (PseudoAffine a, PseudoAffine b, PseudoAffine c) => PseudoAffine (a,b,c) where
  type PseudoDiff (a,b,c) = (PseudoDiff a, PseudoDiff b, PseudoDiff c)
  (a,b,c).-~.(d,e,f) = (a.-~.d, b.-~.e, c.-~.f)
  (a,b,c).+~^(v,w,x) = (a.+~^v, b.+~^w, c.+~^x)


instance PseudoAffine S¹ where
  type PseudoDiff S¹ = ℝ
  S¹ φ₁ .-~. S¹ φ₀
     | δφ > pi     = δφ - 2*pi
     | δφ < (-pi)  = δφ + 2*pi
     | otherwise   = δφ
   where δφ = φ₁ - φ₀
  S¹ φ₀ .+~^ δφ
     | φ' < 0     = S¹ $ φ' + tau
     | otherwise  = S¹ $ φ'
   where φ' = (φ₀ + δφ)`mod'`tau

instance PseudoAffine S² where
  type PseudoDiff S² = ℝ²
  S² ϑ₁ φ₁ .-~. S² ϑ₀ φ₀
     | ϑ₀ < pi/2  = ϑ₁*^embed(S¹ φ₁) ^-^ ϑ₀*^embed(S¹ φ₀)
     | otherwise  = (pi-ϑ₁)*^embed(S¹ φ₁) ^-^ (pi-ϑ₀)*^embed(S¹ φ₀)
  S² ϑ₀ φ₀ .+~^ δv
     | ϑ₀ < pi/2  = sphereFold PositiveHalfSphere $ ϑ₀*^embed(S¹ φ₀) ^+^ δv
     | otherwise  = sphereFold NegativeHalfSphere $ (pi-ϑ₀)*^embed(S¹ φ₀) ^+^ δv

sphereFold :: S⁰ -> ℝ² -> S²
sphereFold hfSphere v
   | ϑ₀ > pi     = S² (inv $ tau - ϑ₀) ((φ₀+pi)`mod'`tau)
   | otherwise  = S² (inv ϑ₀) φ₀
 where S¹ φ₀ = coEmbed v
       ϑ₀ = magnitude v `mod'` tau
       inv ϑ = case hfSphere of PositiveHalfSphere -> ϑ
                                NegativeHalfSphere -> pi - ϑ



tau :: Double
tau = 2 * pi






newtype d --> c
   = Differentiable { getDifferentiable ::
                        d -> ( c
                             , PseudoDiff d :-* PseudoDiff c
                             , Option (HerMetric(PseudoDiff c)->HerMetric(PseudoDiff d)) ) }


-- instance Category (-->) where
--   type Object (-->) o = ( PseudoAffine o
--                         , HasBasis (PseudoDiff o)
--                         , HasTrie (Basis (PseudoDiff o)) )
--   id = Differentiable $ \x -> (x, idL, Option Nothing)
--   Differentiable f . Differentiable g = Differentiable $
--      \x -> let (y, y', devg) = g x
--                (z, z', devf) = f y
--                devfg = Option $ case (getOption devf, getOption devg) of
--                         (Nothing, Nothing) -> Nothing
--                         (Just devf', Nothing) -> Just $
--                           \δz -> let δy = devf' δz
--                                  in transformMetric y' δy
--            in (z, z'*.*y', devfg)
              
