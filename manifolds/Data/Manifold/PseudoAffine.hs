-- |
-- Module      : Data.Manifold.PseudoAffine
-- Copyright   : (c) Justus Sagemüller 2015
-- License     : GPL v3
-- 
-- Maintainer  : (@) sagemueller $ geo.uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 
-- This is the second prototype of a manifold class. It appears to give considerable
-- advantages over 'Data.Manifold.Manifold', so that class will probably soon be replaced
-- with the one we define here (though 'PseudoAffine' does not follow the standard notion
-- of a manifold very closely, it should work quite equivalently for pretty much all
-- Haskell types that qualify as manifolds).
-- 
-- Manifolds are interesting as objects of various categories, from continuous to
-- diffeomorphic. At the moment, we mainly focus on /region-wise differentiable functions/,
-- which are a promising compromise between flexibility of definition and provability of
-- analytic properties. In particular, they are well-suited for visualisation purposes.
-- 
-- The classes in this module are mostly aimed at manifolds /without boundary/.
-- Manifolds with boundary (which we call @MWBound@, never /manifold/!)
-- are more or less treated as a disjoint sum of the interior and the boundary.
-- To understand how this module works, best first forget about boundaries – in this case,
-- @'Interior' x ~ x@, 'fromInterior' and 'toInterior' are trivial, and
-- '.+~|', '|-~.' and 'betweenBounds' are irrelevant.
-- The manifold structure of the boundary itself is not considered at all here.

{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE UndecidableInstances     #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE FunctionalDependencies   #-}
{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE LiberalTypeSynonyms      #-}
{-# LANGUAGE DataKinds                #-}
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE StandaloneDeriving       #-}
{-# LANGUAGE RankNTypes               #-}
{-# LANGUAGE TupleSections            #-}
{-# LANGUAGE ConstraintKinds          #-}
{-# LANGUAGE DefaultSignatures        #-}
{-# LANGUAGE PatternGuards            #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE UnicodeSyntax            #-}
{-# LANGUAGE MultiWayIf               #-}
{-# LANGUAGE ScopedTypeVariables      #-}
{-# LANGUAGE RecordWildCards          #-}
{-# LANGUAGE CPP                      #-}


module Data.Manifold.PseudoAffine (
            -- * Manifold class
              Manifold(inInterior)
            , Semimanifold(..), Needle'
            , PseudoAffine(..)
            -- * Type definitions
            -- ** Needles
            , Local(..), (⊙+^), (!+~^)
            -- ** Metrics
            , Metric, Metric'
            , RieMetric, RieMetric'
            -- ** Constraints
            , SemimanifoldWitness(..)
            , PseudoAffineWitness(..)
            , BoundarylessWitness(..)
            , boundarylessWitness
            , DualNeedleWitness 
            , WithField
            , LocallyScalable
            -- ** Local functions
            , LocalLinear, LocalBilinear, LocalAffine
            -- * Misc
            , alerpB, palerp, palerpB, LocallyCoercible(..), CanonicalDiffeomorphism(..)
            , ImpliesMetric(..), coerceMetric, coerceMetric'
            ) where
    

import Math.Manifold.Core.PseudoAffine

import Data.Maybe
import Data.Fixed

import Data.VectorSpace
import Linear.V0
import Linear.V1
import Linear.V2
import Linear.V3
import Linear.V4
import qualified Linear.Affine as LinAff
import Data.Embedding
import Data.LinearMap
import Data.VectorSpace.Free
import Math.LinearMap.Category
import Data.AffineSpace
import Data.Tagged
import Data.Manifold.Types.Primitive

import Data.CoNat

import qualified Prelude as Hask
import qualified Control.Applicative as Hask

import Control.Category.Constrained.Prelude hiding ((^))
import Control.Arrow.Constrained
import Control.Monad.Constrained
import Data.Foldable.Constrained

import Control.Lens (Lens', lens, (^.), (&), (%~), (.~))

import Data.CallStack (HasCallStack)
import GHC.Exts (Constraint)


  
  

-- | See 'Semimanifold' and 'PseudoAffine' for the methods.
class (PseudoAffine m, LSpace (Needle m)) => Manifold m where
  boundarylessWitness :: BoundarylessWitness m
  default boundarylessWitness :: (m ~ Interior m) => BoundarylessWitness m
  boundarylessWitness = BoundarylessWitness
  inInterior :: m -> Interior m
  default inInterior :: (m ~ Interior m) => m -> Interior m
  inInterior = id
instance (PseudoAffine m, LSpace (Needle m), Interior m ~ m) => Manifold m



-- | Instances of this class must be diffeomorphic manifolds, and even have
--   /canonically isomorphic/ tangent spaces, so that
--   @'fromPackedVector' . 'asPackedVector' :: 'Needle' x -> 'Needle' ξ@
--   defines a meaningful “representational identity“ between these spaces.
class ( Semimanifold x, Semimanifold ξ, LSpace (Needle x), LSpace (Needle ξ)
      , Scalar (Needle x) ~ Scalar (Needle ξ) )
         => LocallyCoercible x ξ where
  -- | Must be compatible with the isomorphism on the tangent spaces, i.e.
  -- @
  -- locallyTrivialDiffeomorphism (p .+~^ v)
  --   ≡ locallyTrivialDiffeomorphism p .+~^ 'coerceNeedle' v
  -- @
  locallyTrivialDiffeomorphism :: x -> ξ
  coerceNeedle :: Hask.Functor p => p (x,ξ) -> (Needle x -+> Needle ξ)
  coerceNeedle' :: Hask.Functor p => p (x,ξ) -> (Needle' x -+> Needle' ξ)
  coerceNorm :: Hask.Functor p => p (x,ξ) -> Metric x -> Metric ξ
  coerceNorm p = case ( oppositeLocalCoercion :: CanonicalDiffeomorphism ξ x
                      , dualSpaceWitness :: DualSpaceWitness (Needle x)
                      , dualSpaceWitness :: DualSpaceWitness (Needle ξ) ) of
    (CanonicalDiffeomorphism, DualSpaceWitness, DualSpaceWitness)
          -> case ( coerceNeedle (swap<$>p), coerceNeedle' p ) of
              (f, f') -> \(Norm n) -> Norm $ f' . n . f
  coerceVariance :: Hask.Functor p => p (x,ξ) -> Metric' x -> Metric' ξ
  coerceVariance p = case ( oppositeLocalCoercion :: CanonicalDiffeomorphism ξ x
                          , dualSpaceWitness :: DualSpaceWitness (Needle x)
                          , dualSpaceWitness :: DualSpaceWitness (Needle ξ) ) of
    (CanonicalDiffeomorphism, DualSpaceWitness, DualSpaceWitness)
          -> case ( coerceNeedle p, coerceNeedle' (swap<$>p) ) of
              (f, f') -> \(Norm n) -> Norm $ f . n . f'
  oppositeLocalCoercion :: CanonicalDiffeomorphism ξ x
  default oppositeLocalCoercion :: LocallyCoercible ξ x => CanonicalDiffeomorphism ξ x
  oppositeLocalCoercion = CanonicalDiffeomorphism
  interiorLocalCoercion :: Functor p (->) (->) 
                  => p (x,ξ) -> CanonicalDiffeomorphism (Interior x) (Interior ξ)
  default interiorLocalCoercion :: LocallyCoercible (Interior x) (Interior ξ)
                  => p (x,ξ) -> CanonicalDiffeomorphism (Interior x) (Interior ξ)
  interiorLocalCoercion _ = CanonicalDiffeomorphism

type NumPrime n = (Num' n, Eq n)

#define identityCoercion(c,t)                   \
instance (c) => LocallyCoercible (t) (t) where { \
  locallyTrivialDiffeomorphism = id;              \
  coerceNeedle _ = id;                             \
  coerceNeedle' _ = id;                             \
  oppositeLocalCoercion = CanonicalDiffeomorphism;   \
  interiorLocalCoercion _ = CanonicalDiffeomorphism }
identityCoercion(NumPrime s, ZeroDim s)
identityCoercion(NumPrime s, V0 s)
identityCoercion((), ℝ)
identityCoercion(NumPrime s, V1 s)
identityCoercion((), (ℝ,ℝ))
identityCoercion(NumPrime s, V2 s)
identityCoercion((), (ℝ,(ℝ,ℝ)))
identityCoercion((), ((ℝ,ℝ),ℝ))
identityCoercion(NumPrime s, V3 s)
identityCoercion(NumPrime s, V4 s)


data CanonicalDiffeomorphism a b where
  CanonicalDiffeomorphism :: LocallyCoercible a b => CanonicalDiffeomorphism a b

-- | A point on a manifold, as seen from a nearby reference point.
newtype Local x = Local { getLocalOffset :: Needle x }
deriving instance (Show (Needle x)) => Show (Local x)

type LocallyScalable s x = ( PseudoAffine x
                           , LSpace (Needle x)
                           , s ~ Scalar (Needle x)
                           , s ~ Scalar (Needle' x)
                           , Num' s )

type LocalLinear x y = LinearMap (Scalar (Needle x)) (Needle x) (Needle y)
type LocalBilinear x y = LinearMap (Scalar (Needle x))
                                   (SymmetricTensor (Scalar (Needle x)) (Needle x))
                                   (Needle y)



type LocalAffine x y = (Needle y, LocalLinear x y)

-- | Require some constraint on a manifold, and also fix the type of the manifold's
--   underlying field. For example, @WithField &#x211d; 'HilbertManifold' v@ constrains
--   @v@ to be a real (i.e., 'Double'-) Hilbert space.
--   Note that for this to compile, you will in
--   general need the @-XLiberalTypeSynonyms@ extension (except if the constraint
--   is an actual type class (like 'Manifold'): only those can always be partially
--   applied, for @type@ constraints this is by default not allowed).
type WithField s c x = ( c x, s ~ Scalar (Needle x), s ~ Scalar (Needle' x) )


-- | A co-needle can be understood as a “paper stack”, with which you can measure
--   the length that a needle reaches in a given direction by counting the number
--   of holes punched through them.
type Needle' x = DualVector (Needle x)


-- | The word &#x201c;metric&#x201d; is used in the sense as in general relativity.
--   Actually this is just the type of scalar products on the tangent space.
--   The actual metric is the function @x -> x -> Scalar (Needle x)@ defined by
--
-- @
-- \\p q -> m '|$|' (p.-~!q)
-- @
type Metric x = Norm (Needle x)
type Metric' x = Variance (Needle x)

-- | A Riemannian metric assigns each point on a manifold a scalar product on the tangent space.
--   Note that this association is /not/ continuous, because the charts/tangent spaces in the bundle
--   are a priori disjoint. However, for a proper Riemannian metric, all arising expressions
--   of scalar products from needles between points on the manifold ought to be differentiable.
type RieMetric x = x -> Metric x
type RieMetric' x = x -> Metric' x


coerceMetric :: ∀ x ξ . (LocallyCoercible x ξ, LSpace (Needle ξ))
                             => RieMetric ξ -> RieMetric x
coerceMetric = case ( dualSpaceWitness :: DualNeedleWitness x
                    , dualSpaceWitness :: DualNeedleWitness ξ ) of
   (DualSpaceWitness, DualSpaceWitness)
       -> \m x -> case m $ locallyTrivialDiffeomorphism x of
              Norm sc -> Norm $ bw . sc . fw
 where fw = coerceNeedle ([]::[(x,ξ)])
       bw = case oppositeLocalCoercion :: CanonicalDiffeomorphism ξ x of
              CanonicalDiffeomorphism -> coerceNeedle' ([]::[(ξ,x)])
coerceMetric' :: ∀ x ξ . (LocallyCoercible x ξ, LSpace (Needle ξ))
                             => RieMetric' ξ -> RieMetric' x
coerceMetric' = case ( dualSpaceWitness :: DualNeedleWitness x
                     , dualSpaceWitness :: DualNeedleWitness ξ ) of
   (DualSpaceWitness, DualSpaceWitness)
       -> \m x -> case m $ locallyTrivialDiffeomorphism x of
              Norm sc -> Norm $ bw . sc . fw
 where fw = coerceNeedle' ([]::[(x,ξ)])
       bw = case oppositeLocalCoercion :: CanonicalDiffeomorphism ξ x of
              CanonicalDiffeomorphism -> coerceNeedle ([]::[(ξ,x)])




hugeℝVal :: ℝ
hugeℝVal = 1e+100

#define deriveAffine(c,t)               \
instance (c) => Semimanifold (t) where { \
  type Needle (t) = Diff (t);             \
  fromInterior = id;                       \
  toInterior = pure;                        \
  translateP = Tagged (.+^);                 \
  (.+~^) = (.+^) };                           \
instance (c) => PseudoAffine (t) where {       \
  a.-~.b = pure (a.-.b);      }

deriveAffine(KnownNat n, FreeVect n ℝ)

instance (NumPrime s) => LocallyCoercible (ZeroDim s) (V0 s) where
  locallyTrivialDiffeomorphism Origin = V0
  coerceNeedle _ = LinearFunction $ \Origin -> V0
  coerceNeedle' _ = LinearFunction $ \Origin -> V0
instance (NumPrime s) => LocallyCoercible (V0 s) (ZeroDim s) where
  locallyTrivialDiffeomorphism V0 = Origin
  coerceNeedle _ = LinearFunction $ \V0 -> Origin
  coerceNeedle' _ = LinearFunction $ \V0 -> Origin
instance LocallyCoercible ℝ (V1 ℝ) where
  locallyTrivialDiffeomorphism = V1
  coerceNeedle _ = LinearFunction V1
  coerceNeedle' _ = LinearFunction V1
instance LocallyCoercible (V1 ℝ) ℝ where
  locallyTrivialDiffeomorphism (V1 n) = n
  coerceNeedle _ = LinearFunction $ \(V1 n) -> n
  coerceNeedle' _ = LinearFunction $ \(V1 n) -> n
instance LocallyCoercible (ℝ,ℝ) (V2 ℝ) where
  locallyTrivialDiffeomorphism = uncurry V2
  coerceNeedle _ = LinearFunction $ uncurry V2
  coerceNeedle' _ = LinearFunction $ uncurry V2
instance LocallyCoercible (V2 ℝ) (ℝ,ℝ) where
  locallyTrivialDiffeomorphism (V2 x y) = (x,y)
  coerceNeedle _ = LinearFunction $ \(V2 x y) -> (x,y)
  coerceNeedle' _ = LinearFunction $ \(V2 x y) -> (x,y)
instance LocallyCoercible ((ℝ,ℝ),ℝ) (V3 ℝ) where
  locallyTrivialDiffeomorphism ((x,y),z) = V3 x y z
  coerceNeedle _ = LinearFunction $ \((x,y),z) -> V3 x y z
  coerceNeedle' _ = LinearFunction $ \((x,y),z) -> V3 x y z
instance LocallyCoercible (ℝ,(ℝ,ℝ)) (V3 ℝ) where
  locallyTrivialDiffeomorphism (x,(y,z)) = V3 x y z
  coerceNeedle _ = LinearFunction $ \(x,(y,z)) -> V3 x y z
  coerceNeedle' _ = LinearFunction $ \(x,(y,z)) -> V3 x y z
instance LocallyCoercible (V3 ℝ) ((ℝ,ℝ),ℝ) where
  locallyTrivialDiffeomorphism (V3 x y z) = ((x,y),z)
  coerceNeedle _ = LinearFunction $ \(V3 x y z) -> ((x,y),z)
  coerceNeedle' _ = LinearFunction $ \(V3 x y z) -> ((x,y),z)
instance LocallyCoercible (V3 ℝ) (ℝ,(ℝ,ℝ)) where
  locallyTrivialDiffeomorphism (V3 x y z) = (x,(y,z))
  coerceNeedle _ = LinearFunction $ \(V3 x y z) -> (x,(y,z))
  coerceNeedle' _ = LinearFunction $ \(V3 x y z) -> (x,(y,z))
instance LocallyCoercible ((ℝ,ℝ),(ℝ,ℝ)) (V4 ℝ) where
  locallyTrivialDiffeomorphism ((x,y),(z,w)) = V4 x y z w
  coerceNeedle _ = LinearFunction $ \((x,y),(z,w)) -> V4 x y z w
  coerceNeedle' _ = LinearFunction $ \((x,y),(z,w)) -> V4 x y z w
instance LocallyCoercible (V4 ℝ) ((ℝ,ℝ),(ℝ,ℝ)) where
  locallyTrivialDiffeomorphism (V4 x y z w) = ((x,y),(z,w))
  coerceNeedle _ = LinearFunction $ \(V4 x y z w) -> ((x,y),(z,w))
  coerceNeedle' _ = LinearFunction $ \(V4 x y z w) -> ((x,y),(z,w))


instance ( Semimanifold a, Semimanifold b, Semimanifold c
         , LSpace (Needle a), LSpace (Needle b), LSpace (Needle c)
         , Scalar (Needle a) ~ Scalar (Needle b), Scalar (Needle b) ~ Scalar (Needle c)
         , Scalar (Needle' a) ~ Scalar (Needle a), Scalar (Needle' b) ~ Scalar (Needle b)
         , Scalar (Needle' c) ~ Scalar (Needle c) )
     => LocallyCoercible (a,(b,c)) ((a,b),c) where
  locallyTrivialDiffeomorphism = regroup
  coerceNeedle _ = regroup
  coerceNeedle' _ = regroup
  oppositeLocalCoercion = CanonicalDiffeomorphism
  interiorLocalCoercion _ = case ( semimanifoldWitness :: SemimanifoldWitness a
                                 , semimanifoldWitness :: SemimanifoldWitness b
                                 , semimanifoldWitness :: SemimanifoldWitness c ) of
       ( SemimanifoldWitness BoundarylessWitness
        ,SemimanifoldWitness BoundarylessWitness
        ,SemimanifoldWitness BoundarylessWitness )
              -> CanonicalDiffeomorphism
instance ∀ a b c .
         ( Semimanifold a, Semimanifold b, Semimanifold c
         , LSpace (Needle a), LSpace (Needle b), LSpace (Needle c)
         , Scalar (Needle a) ~ Scalar (Needle b), Scalar (Needle b) ~ Scalar (Needle c)
         , Scalar (Needle' a) ~ Scalar (Needle a), Scalar (Needle' b) ~ Scalar (Needle b)
         , Scalar (Needle' c) ~ Scalar (Needle c)  )
     => LocallyCoercible ((a,b),c) (a,(b,c)) where
  locallyTrivialDiffeomorphism = regroup'
  coerceNeedle _ = regroup'
  coerceNeedle' _ = regroup'
  oppositeLocalCoercion = CanonicalDiffeomorphism
  interiorLocalCoercion _ = case ( semimanifoldWitness :: SemimanifoldWitness a
                                 , semimanifoldWitness :: SemimanifoldWitness b
                                 , semimanifoldWitness :: SemimanifoldWitness c ) of
       ( SemimanifoldWitness BoundarylessWitness
        ,SemimanifoldWitness BoundarylessWitness
        ,SemimanifoldWitness BoundarylessWitness )
            -> CanonicalDiffeomorphism


instance (LinearSpace (a n), Needle (a n) ~ a n, Interior (a n) ~ a n)
            => Semimanifold (LinAff.Point a n) where
  type Needle (LinAff.Point a n) = a n
  fromInterior = id
  toInterior = pure
  LinAff.P v .+~^ w = LinAff.P $ v ^+^ w
  translateP = Tagged $ \(LinAff.P v) w -> LinAff.P $ v ^+^ w
instance (LinearSpace (a n), Needle (a n) ~ a n, Interior (a n) ~ a n)
            => PseudoAffine (LinAff.Point a n) where
  LinAff.P v .-~. LinAff.P w = return $ v ^-^ w




instance Semimanifold S² where
  type Needle S² = ℝ²
  fromInterior = id
  toInterior = pure
  translateP = Tagged (.+~^)
  S² θ₀ φ₀ .+~^ 𝐯 = S² θ₁ φ₁
   where -- See images/constructions/sphericoords-needles.svg.
         S¹ γ = coEmbed 𝐯
         d = magnitude 𝐯
         S¹ φ₁ = S¹ φ₀ .+~^ δφ
         -- Spherical law of cotangents for δφ:
         -- cos θ₀ · cos (π−γ) = cot d · sin θ₀ − cot δφ · sin (π−γ)
         -- ⟹  tan δφ = sin (π−γ) / (cot d · sin θ₀ − cos θ₀ · cos (π−γ))
         --           = sin γ / (cot d · sin θ₀ + cos θ₀ · cos γ)
         --           = (sin γ · sin d)
         --               / (cos d · sin θ₀ + sin d · sin θ₀ · cos γ)
         δφ = atan2 (sin γ * sin d) (cos d * sin θ₀ + sin d * sin θ₀ * cos γ)
         -- Spherical law of cotangents for θ₁:
         -- cos θ₀ · cos δφ = cot θ₁ · sin θ₀ − cot (π−γ) · sin δφ
         -- ⟹  tan θ₁ = sin θ₀ / (cos θ₀ · cos δφ + cot (π−γ) · sin δφ)
         --           = (sin θ₀ · sin γ) / (sin γ · cos θ₀ · cos δφ − cos γ · sin δφ)
         θ₁ = atan2 (sin θ₀ * sin γ) (sin γ * cos θ₀ * cos δφ - cos γ * sin δφ)

instance PseudoAffine S² where
  S² θ₁ φ₁ .-~! S² θ₀ φ₀ = d *^ embed(S¹ γ)
   where -- See images/constructions/sphericoords-needles.svg.
         δφ = S¹ φ₁ .-~! S¹ φ₀
         -- Spherical law of cotangents for γ:
         -- cos θ₀ · cos δφ = cot θ₁ · sin θ₀ − cot (π−γ) · sin δφ
         -- cot (π−γ) · sin δφ = cot θ₁ · sin θ₀ − cos θ₀ · cos δφ
         -- tan (π−γ) = sin δφ / (cot θ₁ · sin θ₀ − cos θ₀ · cos δφ)
         --           = (sin δφ · sin θ₁) / (cos θ₁ · sin θ₀ − sin θ₁ · cos θ₀ · cos δφ)
         γ = pi - atan2 (sin δφ * sin θ₁) (cos θ₁ * sin θ₀ - sin θ₁ * cos θ₀ * cos δφ)
         -- Spherical law of cotangents for d:
         -- cos θ₀ · cos (π−γ) = cot d · sin θ₀ − cot δφ · sin (π−γ)
         -- ⟹  tan d = sin θ₀ / (cot δφ · sin (π−γ) − cos θ₀ · cos (π−γ))
         --          = (sin θ₀ · sin δφ) / (cos δφ · sin γ + sin δφ · cos θ₀ · cos γ)
         d = atan2 (sin θ₀ * sin δφ) (cos δφ * sin γ + sin δφ * cos θ₀ * cos γ)
         



instance Semimanifold ℝP² where
  type Needle ℝP² = ℝ²
  fromInterior = id
  toInterior = pure
  translateP = Tagged (.+~^)
  ℝP² r₀ φ₀ .+~^ V2 δr δφ
   | r₀ > 1/2   = case r₀ + δr of
                   r₁ | r₁ > 1     -> ℝP² (2-r₁) (toS¹range $ φ₀+δφ+pi)
                      | otherwise  -> ℝP²    r₁  (toS¹range $ φ₀+δφ)
  ℝP² r₀ φ₀ .+~^ δxy = let v = r₀*^embed(S¹ φ₀) ^+^ δxy
                           S¹ φ₁ = coEmbed v
                           r₁ = magnitude v `mod'` 1
                       in ℝP² r₁ φ₁  
instance PseudoAffine ℝP² where
  ℝP² r₁ φ₁ .-~. ℝP² r₀ φ₀
   | r₀ > 1/2   = pure `id` case φ₁-φ₀ of
                          δφ | δφ > 3*pi/2  -> V2 (  r₁ - r₀) (δφ - 2*pi)
                             | δφ < -3*pi/2 -> V2 (  r₁ - r₀) (δφ + 2*pi)
                             | δφ > pi/2    -> V2 (2-r₁ - r₀) (δφ - pi  )
                             | δφ < -pi/2   -> V2 (2-r₁ - r₀) (δφ + pi  )
                             | otherwise    -> V2 (  r₁ - r₀) (δφ       )
   | otherwise  = pure ( r₁*^embed(S¹ φ₁) ^-^ r₀*^embed(S¹ φ₀) )


-- instance (PseudoAffine m, VectorSpace (Needle m), Scalar (Needle m) ~ ℝ)
--              => Semimanifold (CD¹ m) where
--   type Needle (CD¹ m) = (Needle m, ℝ)
--   CD¹ h₀ m₀ .+~^ (h₁δm, δh)
--       = let h₁ = min 1 . max 1e-300 $ h₀+δh; δm = h₁δm^/h₁
--         in CD¹ h₁ (m₀.+~^δm)
-- instance (PseudoAffine m, VectorSpace (Needle m), Scalar (Needle m) ~ ℝ)
--              => PseudoAffine (CD¹ m) where
--   CD¹ h₁ m₁ .-~. CD¹ h₀ m₀
--      = fmap ( \δm -> (h₁*^δm, h₁-h₀) ) $ m₁.-~.m₀
                               





class ImpliesMetric s where
  type MetricRequirement s x :: Constraint
  type MetricRequirement s x = Semimanifold x
  inferMetric :: (MetricRequirement s x, LSpace (Needle x))
                     => s x -> Metric x
  inferMetric' :: (MetricRequirement s x, LSpace (Needle x))
                     => s x -> Metric' x

instance ImpliesMetric Norm where
  type MetricRequirement Norm x = (SimpleSpace x, x ~ Needle x)
  inferMetric = id
  inferMetric' = dualNorm



type DualNeedleWitness x = DualSpaceWitness (Needle x)



infixl 6 !+~^
-- | Boundary-unsafe version of `.+~^`.
(!+~^) :: ∀ x . (Semimanifold x, HasCallStack) => x -> Needle x -> x
p!+~^v = case toInterior p of
           Just p' -> p'.+~^v


infix 6 ⊙+^
-- | Proxy-version of `translateP`.
(⊙+^) :: ∀ x proxy . Semimanifold x => Interior x -> Needle x -> proxy x -> Interior x
(⊙+^) x v _ = tp x v
 where Tagged tp = translateP :: Tagged x (Interior x -> Needle x -> Interior x)
