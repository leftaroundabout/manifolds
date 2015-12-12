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
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE RankNTypes               #-}
{-# LANGUAGE TupleSections            #-}
{-# LANGUAGE ConstraintKinds          #-}
{-# LANGUAGE PatternGuards            #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE UnicodeSyntax            #-}
{-# LANGUAGE MultiWayIf               #-}
{-# LANGUAGE ScopedTypeVariables      #-}
{-# LANGUAGE RecordWildCards          #-}
{-# LANGUAGE CPP                      #-}


module Data.Manifold.PseudoAffine (
            -- * Manifold class
              Manifold
            , Semimanifold(..)
            , PseudoAffine(..)
            -- * Type definitions
            -- ** Metrics
            , Metric, Metric', euclideanMetric
            , RieMetric, RieMetric'
            -- ** Constraints
            , RealDimension, AffineManifold
            , LinearManifold
            , WithField
            , HilbertSpace
            , EuclidSpace
            , LocallyScalable
            -- * Misc
            , palerp
            ) where
    


import Data.List
import qualified Data.Vector.Generic as Arr
import qualified Data.Vector
import Data.Maybe
import Data.Semigroup
import Data.Function (on)
import Data.Fixed

import Data.VectorSpace
import Data.LinearMap
import Data.LinearMap.HerMetric
import Data.MemoTrie (HasTrie(..))
import Data.AffineSpace
import Data.Basis
import Data.Complex hiding (magnitude)
import Data.Void
import Data.Tagged
import Data.Manifold.Types.Primitive

import Data.CoNat
import Data.VectorSpace.FiniteDimensional

import qualified Numeric.LinearAlgebra.HMatrix as HMat

import qualified Prelude
import qualified Control.Applicative as Hask

import Control.Category.Constrained.Prelude hiding ((^))
import Control.Arrow.Constrained
import Control.Monad.Constrained
import Data.Foldable.Constrained




infix 6 .-~.
infixl 6 .+~^, .-~^

class ( AdditiveGroup (Needle x), Interior (Interior x) ~ Interior x )
          => Semimanifold x where
  {-# MINIMAL ((.+~^) | fromInterior), toInterior, translateP #-}
  -- | The space of &#x201c;natural&#x201d; ways starting from some reference point
  --   and going to some particular target point. Hence,
  --   the name: like a compass needle, but also with an actual length.
  --   For affine spaces, 'Needle' is simply the space of
  --   line segments (aka vectors) between two points, i.e. the same as 'Diff'.
  --   The 'AffineManifold' constraint makes that requirement explicit.
  -- 
  --   This space should be isomorphic to the tangent space (and is in fact
  --   used somewhat synonymously).
  type Needle x :: *
  
  -- | Manifolds with boundary are a bit tricky. We support such manifolds,
  --   but carry out most calculations only in “the fleshy part” – the
  --   interior, which is an “infinite space”, so you can arbitrarily scale paths.
  -- 
  --   The default implementation is @'Interior' x = x@, which corresponds
  --   to a manifold that has no boundary to begin with.
  type Interior x :: *
  type Interior x = x
  
  -- | Generalised translation operation. Note that the result will always also
  --   be in the interior; scaling up the needle can only get you ever /closer/
  --   to a boundary.
  (.+~^) :: Interior x -> Needle x -> x
  (.+~^) = addvp
   where addvp :: ∀ x . Semimanifold x => Interior x -> Needle x -> x
         addvp p = fromInterior . tp p
          where (Tagged tp) = translateP :: Tagged x (Interior x -> Needle x -> Interior x)
    
  -- | 'id' sans boundary.
  fromInterior :: Interior x -> x
  fromInterior p = p .+~^ zeroV 
  
  toInterior :: x -> Option (Interior x)
  
  -- | The signature of '.+~^' should really be @'Interior' x -> 'Needle' x -> 'Interior' x@,
  --   only, this is not possible because it only consists of non-injective type families.
  --   The solution is this tagged signature, which is of course rather unwieldy. That's
  --   why '.+~^' has the stronger, but easier usable signature. Without boundary, these
  --   functions should be equivalent, i.e. @translateP = Tagged (.+~^)@.
  translateP :: Tagged x (Interior x -> Needle x -> Interior x)
  
  -- | Shorthand for @\\p v -> p .+~^ 'negateV' v@, which should obey the /asymptotic/ law
  --   
  -- @
  -- p .-~^ v .+~^ v &#x2245; p
  -- @
  --   
  --   Meaning: if @v@ is scaled down with sufficiently small factors /&#x3b7;/, then
  --   the difference @(p.-~^v.+~^v) .-~. p@ should scale down even faster:
  --   as /O/ (/&#x3b7;/&#xb2;). For large vectors, it will however behave differently,
  --   except in flat spaces (where all this should be equivalent to the 'AffineSpace'
  --   instance).
  (.-~^) :: Interior x -> Needle x -> x
  p .-~^ v = p .+~^ negateV v

  
-- | This is the class underlying manifolds. ('Manifold' only precludes boundaries
--   and adds an extra constraint that would be circular if it was in a single
--   class. You can always just use 'Manifold' as a constraint in your signatures,
--   but you must /define/ only 'PseudoAffine' for manifold types &#x2013;
--   the 'Manifold' instance follows universally from this, if @'Interior x ~ x@.)
--   
--   The interface is (boundaries aside) almost identical to the better-known
--   'AffineSpace' class, but we don't require associativity of '.+~^' with '^+^'
--   &#x2013; except in an /asymptotic sense/ for small vectors.
--   
--   That innocent-looking change makes the class applicable to vastly more general types:
--   while an affine space is basically nothing but a vector space without particularly
--   designated origin, a pseudo-affine space can have nontrivial topology on the global
--   scale, and yet be used in practically the same way as an affine space. At least the
--   usual spheres and tori make good instances, perhaps the class is in fact equivalent to
--   manifolds in their usual maths definition (with an atlas of charts: a family of
--   overlapping regions of the topological space, each homeomorphic to the 'Needle'
--   vector space or some simply-connected subset thereof).
class ( Semimanifold x, Semimanifold (Interior x)
      , Needle (Interior x) ~ Needle x, Interior (Interior x) ~ Interior x)
        => PseudoAffine x where
  -- | The path reaching from one point to another.
  --   Should only yield 'Nothing' if
  -- 
  --   * The points are on disjoint segments of a non&#x2013;path-connected space.
  -- 
  --   * Either of the points is on the boundary. Use '|-~.' to deal with this.
  -- 
  --   On manifolds, the identity
  --   
  -- @
  -- p .+~^ (q.-~.p) &#x2261; q
  -- @
  --   
  --   should hold, at least save for floating-point precision limits etc..
  -- 
  --   '.-~.' and '.+~^' only really work in manifolds without boundary. If you consider
  --   the path between two points, one of which lies on the boundary, it can't really
  --   be possible to scale this path any longer – it would have to reach “out of the
  --   manifold”. To adress this problem, these functions basically consider only the
  --   /interior/ of the space.
  (.-~.) :: x -> Interior x -> Option (Needle x)

  
  
  

-- | See 'Semimanifold' and 'PseudoAffine' for the methods.
class (PseudoAffine m, LinearManifold (Needle m), Interior m ~ m) => Manifold m
instance (PseudoAffine m, LinearManifold (Needle m), Interior m ~ m) => Manifold m

type LocallyScalable s x = ( PseudoAffine x
                           , HasMetric (Needle x)
                           , s ~ Scalar (Needle x) )

-- | Basically just an &#x201c;updated&#x201d; version of the 'VectorSpace' class.
--   Every vector space is a manifold, this constraint makes it explicit.
--   
--   (Actually, 'LinearManifold' is stronger than 'VectorSpace' at the moment, since
--   'HasMetric' requires 'FiniteDimensional'. This might be lifted in the future.)
type LinearManifold x = ( AffineManifold x, Needle x ~ x, HasMetric x )

type LinearManifold' x = ( PseudoAffine x, AffineSpace x, Diff x ~ x
                         , Interior x ~ x, Needle x ~ x, HasMetric x )

-- | Require some constraint on a manifold, and also fix the type of the manifold's
--   underlying field. For example, @WithField &#x211d; 'HilbertSpace' v@ constrains
--   @v@ to be a real (i.e., 'Double'-) Hilbert space.
--   Note that for this to compile, you will in
--   general need the @-XLiberalTypeSynonyms@ extension (except if the constraint
--   is an actual type class (like 'Manifold'): only those can always be partially
--   applied, for @type@ constraints this is by default not allowed).
type WithField s c x = ( c x, s ~ Scalar (Needle x) )

-- | The 'RealFloat' class plus manifold constraints.
type RealDimension r = ( PseudoAffine r, Interior r ~ r, Needle r ~ r
                       , HasMetric r, DualSpace r ~ r, Scalar r ~ r
                       , RealFloat r, r ~ ℝ)

-- | The 'AffineSpace' class plus manifold constraints.
type AffineManifold m = ( PseudoAffine m, Interior m ~ m, AffineSpace m
                        , Needle m ~ Diff m, LinearManifold' (Diff m) )

-- | A Hilbert space is a /complete/ inner product space. Being a vector space, it is
--   also a manifold.
-- 
--   (Stricly speaking, that doesn't have much to do with the completeness criterion;
--   but since 'Manifold's are at the moment confined to finite dimension, they are in
--   fact (trivially) complete.)
type HilbertSpace x = ( LinearManifold x, InnerSpace x
                      , Interior x ~ x, Needle x ~ x, DualSpace x ~ x
                      , Floating (Scalar x) )

-- | An euclidean space is a real affine space whose tangent space is a Hilbert space.
type EuclidSpace x = ( AffineManifold x, InnerSpace (Diff x)
                     , DualSpace (Diff x) ~ Diff x, Floating (Scalar (Diff x)) )

euclideanMetric :: EuclidSpace x => Tagged x (Metric x)
euclideanMetric = Tagged euclideanMetric'


-- | The word &#x201c;metric&#x201d; is used in the sense as in general relativity. Cf. 'HerMetric'.
type Metric x = HerMetric (Needle x)
type Metric' x = HerMetric' (Needle x)

-- | A Riemannian metric assigns each point on a manifold a scalar product on the tangent space.
--   Note that this association is /not/ continuous, because the charts/tangent spaces in the bundle
--   are a priori disjoint. However, for a proper Riemannian metric, all arising expressions
--   of scalar products from needles between points on the manifold ought to be differentiable.
type RieMetric x = x -> Metric x
type RieMetric' x = x -> Metric' x

-- | Interpolate between points, approximately linearly. For
--   points that aren't close neighbours (i.e. lie in an almost
--   flat region), the pathway is basically undefined – save for
--   its end points.
-- 
--   A proper, really well-defined (on global scales) interpolation
--   only makes sense on a Riemannian manifold, as geodesics.
--   This is a task to be tackled in the future.
palerp :: ∀ x. Manifold x
    => Interior x -> Interior x -> Option (Scalar (Needle x) -> x)
palerp p1 p2 = case (fromInterior p2 :: x) .-~. p1 of
  Option (Just v) -> return $ \t -> p1 .+~^ t *^ v
  _ -> empty




hugeℝVal :: ℝ
hugeℝVal = 1e+100

#define deriveAffine(t)          \
instance Semimanifold (t) where { \
  type Needle (t) = Diff (t);      \
  fromInterior = id;                \
  toInterior = pure;                 \
  translateP = Tagged (.+^);          \
  (.+~^) = (.+^) };                    \
instance PseudoAffine (t) where {       \
  a.-~.b = pure (a.-.b);      }

deriveAffine(Double)
deriveAffine(Rational)

instance SmoothScalar s => Semimanifold (FinVecArrRep t b s) where
  type Needle (FinVecArrRep t b s) = FinVecArrRep t b s
  type Interior (FinVecArrRep t b s) = FinVecArrRep t b s
  fromInterior = id
  toInterior = pure
  translateP = Tagged (.+^)
  (.+~^) = (.+^)
instance SmoothScalar s => PseudoAffine (FinVecArrRep t b s) where
  a.-~.b = pure (a.-.b)
  

instance Semimanifold (ZeroDim k) where
  type Needle (ZeroDim k) = ZeroDim k
  fromInterior = id
  toInterior = pure
  Origin .+~^ Origin = Origin
  Origin .-~^ Origin = Origin
  translateP = Tagged (.+~^)
instance PseudoAffine (ZeroDim k) where
  Origin .-~. Origin = pure Origin

instance (Semimanifold a, Semimanifold b) => Semimanifold (a,b) where
  type Needle (a,b) = (Needle a, Needle b)
  type Interior (a,b) = (Interior a, Interior b)
  (a,b).+~^(v,w) = (a.+~^v, b.+~^w)
  (a,b).-~^(v,w) = (a.-~^v, b.-~^w)
  fromInterior (i,j) = (fromInterior i, fromInterior j)
  toInterior (a,b) = fzip (toInterior a, toInterior b)
  translateP = tp
   where tp :: ∀ a b . (Semimanifold a, Semimanifold b)
                     => Tagged (a,b) ( (Interior a, Interior b) 
                                    -> (Needle a, Needle b)
                                    -> (Interior a, Interior b) )
         tp = Tagged $ \(a,b) (v,w) -> (ta a v, tb b w)
          where Tagged ta = translateP :: Tagged a (Interior a -> Needle a -> Interior a)
                Tagged tb = translateP :: Tagged b (Interior b -> Needle b -> Interior b)
instance (PseudoAffine a, PseudoAffine b) => PseudoAffine (a,b) where
  (a,b).-~.(c,d) = liftA2 (,) (a.-~.c) (b.-~.d)

instance (Semimanifold a, Semimanifold b, Semimanifold c) => Semimanifold (a,b,c) where
  type Needle (a,b,c) = (Needle a, Needle b, Needle c)
  type Interior (a,b,c) = (Interior a, Interior b, Interior c)
  (a,b,c).+~^(v,w,x) = (a.+~^v, b.+~^w, c.+~^x)
  (a,b,c).-~^(v,w,x) = (a.-~^v, b.-~^w, c.-~^x)
  fromInterior (i,j,k) = (fromInterior i, fromInterior j, fromInterior k)
  toInterior (a,b,c) = liftA3 (,,) (toInterior a) (toInterior b) (toInterior c)
  translateP = tp
   where tp :: ∀ a b v . (Semimanifold a, Semimanifold b, Semimanifold c)
                     => Tagged (a,b,c) ( (Interior a, Interior b, Interior c) 
                                      -> (Needle a, Needle b, Needle c)
                                      -> (Interior a, Interior b, Interior c) )
         tp = Tagged $ \(a,b,c) (v,w,x) -> (ta a v, tb b w, tc c x)
          where Tagged ta = translateP :: Tagged a (Interior a -> Needle a -> Interior a)
                Tagged tb = translateP :: Tagged b (Interior b -> Needle b -> Interior b)
                Tagged tc = translateP :: Tagged c (Interior c -> Needle c -> Interior c)
instance (PseudoAffine a, PseudoAffine b, PseudoAffine c) => PseudoAffine (a,b,c) where
  (a,b,c).-~.(d,e,f) = liftA3 (,,) (a.-~.d) (b.-~.e) (c.-~.f)

instance (MetricScalar a, KnownNat n) => Semimanifold (FreeVect n a) where
  type Needle (FreeVect n a) = FreeVect n a
  fromInterior = id
  toInterior = pure
  translateP = Tagged (.+~^)
  (.+~^) = (.+^)
instance (MetricScalar a, KnownNat n) => PseudoAffine (FreeVect n a) where
  a.-~.b = pure (a.-.b)


instance Semimanifold S⁰ where
  type Needle S⁰ = ℝ⁰
  fromInterior = id
  toInterior = pure
  translateP = Tagged (.+~^)
  p .+~^ Origin = p
  p .-~^ Origin = p
instance PseudoAffine S⁰ where
  PositiveHalfSphere .-~. PositiveHalfSphere = pure Origin
  NegativeHalfSphere .-~. NegativeHalfSphere = pure Origin
  _ .-~. _ = Option Nothing

instance Semimanifold S¹ where
  type Needle S¹ = ℝ
  fromInterior = id
  toInterior = pure
  translateP = Tagged (.+~^)
  S¹ φ₀ .+~^ δφ
     | φ' < 0     = S¹ $ φ' + tau
     | otherwise  = S¹ $ φ'
   where φ' = toS¹range $ φ₀ + δφ
instance PseudoAffine S¹ where
  S¹ φ₁ .-~. S¹ φ₀
     | δφ > pi     = pure (δφ - 2*pi)
     | δφ < (-pi)  = pure (δφ + 2*pi)
     | otherwise   = pure δφ
   where δφ = φ₁ - φ₀

instance Semimanifold D¹ where
  type Needle D¹ = ℝ
  type Interior D¹ = ℝ
  fromInterior = D¹ . tanh
  toInterior (D¹ x) | abs x < 1  = return $ atanh x
                    | otherwise  = empty
  translateP = Tagged (+)
instance PseudoAffine D¹ where
  D¹ 1 .-~. _ = empty
  D¹ (-1) .-~. _ = empty
  D¹ x .-~. y
    | abs x < 1  = return $ atanh x - y
    | otherwise  = empty

instance Semimanifold S² where
  type Needle S² = ℝ²
  fromInterior = id
  toInterior = pure
  translateP = Tagged (.+~^)
  S² ϑ₀ φ₀ .+~^ δv
     | ϑ₀ < pi/2  = sphereFold PositiveHalfSphere $ ϑ₀*^embed(S¹ φ₀) ^+^ δv
     | otherwise  = sphereFold NegativeHalfSphere $ (pi-ϑ₀)*^embed(S¹ φ₀) ^+^ δv
instance PseudoAffine S² where
  S² ϑ₁ φ₁ .-~. S² ϑ₀ φ₀
     | ϑ₀ < pi/2  = pure ( ϑ₁*^embed(S¹ φ₁) ^-^ ϑ₀*^embed(S¹ φ₀) )
     | otherwise  = pure ( (pi-ϑ₁)*^embed(S¹ φ₁) ^-^ (pi-ϑ₀)*^embed(S¹ φ₀) )

sphereFold :: S⁰ -> ℝ² -> S²
sphereFold hfSphere v
   | ϑ₀ > pi     = S² (inv $ tau - ϑ₀) (toS¹range $ φ₀+pi)
   | otherwise  = S² (inv ϑ₀) φ₀
 where S¹ φ₀ = coEmbed v
       ϑ₀ = magnitude v `mod'` tau
       inv ϑ = case hfSphere of PositiveHalfSphere -> ϑ
                                NegativeHalfSphere -> pi - ϑ


instance Semimanifold ℝP² where
  type Needle ℝP² = ℝ²
  fromInterior = id
  toInterior = pure
  translateP = Tagged (.+~^)
  ℝP² r₀ φ₀ .+~^ (δr, δφ)
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
                          δφ | δφ > 3*pi/2  -> (  r₁ - r₀, δφ - 2*pi)
                             | δφ < -3*pi/2 -> (  r₁ - r₀, δφ + 2*pi)
                             | δφ > pi/2    -> (2-r₁ - r₀, δφ - pi  )
                             | δφ < -pi/2   -> (2-r₁ - r₀, δφ + pi  )
                             | otherwise    -> (  r₁ - r₀, δφ       )
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
                               


tau :: ℝ
tau = 2 * pi

toS¹range :: ℝ -> ℝ
toS¹range φ = (φ+pi)`mod'`tau - pi





