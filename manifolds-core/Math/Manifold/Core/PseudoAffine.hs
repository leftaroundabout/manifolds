-- |
-- Module      : Math.Manifold.Core.PseudoAffine
-- Copyright   : (c) Justus Sagemüller 2016
-- License     : GPL v3
-- 
-- Maintainer  : (@) sagemueller $ geo.uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 

{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE UndecidableInstances     #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE DefaultSignatures        #-}
{-# LANGUAGE UnicodeSyntax            #-}
{-# LANGUAGE ScopedTypeVariables      #-}
{-# LANGUAGE CPP                      #-}


module Math.Manifold.Core.PseudoAffine where

import Data.VectorSpace
import Data.AffineSpace

import Data.Tagged
import Data.Fixed (mod')

import Math.Manifold.Core.Types
import Math.Manifold.VectorSpace.ZeroDimensional

import Control.Applicative

data BoundarylessWitness m where
  BoundarylessWitness :: (Semimanifold m, Interior m ~ m)
                 => BoundarylessWitness m

-- | This is the reified form of the property that the interior of a semimanifold
--   is a manifold. These constraints would ideally be expressed directly as
--   superclass constraints, but that would require the @UndecidableSuperclasses@
--   extension, which is not reliable yet.
-- 
-- Also, if all those equality constraints are in scope, GHC tends to infer needlessly
-- complicated types like @'Interior' ('Interior' ('Needle' ('Interior' x)))@, which is
-- the same as just @'Needle' x@.
data SemimanifoldWitness x where
  SemimanifoldWitness ::
      ( Semimanifold (Needle x), Needle (Interior x) ~ Needle x
      , Needle (Needle x) ~ Needle x
      , Interior (Needle x) ~ Needle x )
     => BoundarylessWitness (Interior x) -> SemimanifoldWitness x

data PseudoAffineWitness x where
  PseudoAffineWitness ::
      ( PseudoAffine (Interior x), PseudoAffine (Needle x) )
     => SemimanifoldWitness x -> PseudoAffineWitness x

infix 6 .-~., .-~!
infixl 6 .+~^, .-~^

class AdditiveGroup (Needle x) => Semimanifold x where
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
  
  toInterior :: x -> Maybe (Interior x)
  
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
  
  semimanifoldWitness :: SemimanifoldWitness x
  default semimanifoldWitness ::
      ( Semimanifold (Interior x), Semimanifold (Needle x)
      , Interior (Interior x) ~ Interior x, Needle (Interior x) ~ Needle x
      , Needle (Needle x) ~ Needle x
      , Interior (Needle x) ~ Needle x )
     => SemimanifoldWitness x
  semimanifoldWitness = SemimanifoldWitness BoundarylessWitness

  
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
class Semimanifold x => PseudoAffine x where
  {-# MINIMAL (.-~.) | (.-~!) #-}
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
  (.-~.) :: x -> x -> Maybe (Needle x)
  p.-~.q = return $ p.-~!q
  
  -- | Unsafe version of '.-~.'. If the two points lie in disjoint regions,
  --   the behaviour is undefined.
  (.-~!) :: x -> x -> Needle x
  p.-~!q = case p.-~.q of
      Just v -> v
  
  pseudoAffineWitness :: PseudoAffineWitness x
  default pseudoAffineWitness ::
      ( PseudoAffine (Interior x), PseudoAffine (Needle x) )
     => PseudoAffineWitness x
  pseudoAffineWitness = PseudoAffineWitness semimanifoldWitness
  

  
  
  


-- | Interpolate between points, approximately linearly. For
--   points that aren't close neighbours (i.e. lie in an almost
--   flat region), the pathway is basically undefined – save for
--   its end points.
-- 
--   A proper, really well-defined (on global scales) interpolation
--   only makes sense on a Riemannian manifold, as 'Data.Manifold.Riemannian.Geodesic'.
palerp :: ∀ x. (PseudoAffine x, VectorSpace (Needle x))
    => x -> x -> Maybe (Scalar (Needle x) -> x)
palerp p₀ p₁ = case (toInterior p₀, p₁.-~.p₀) of
  (Just b, Just v) -> return $ \t -> b .+~^ t *^ v
  _ -> Nothing

-- | Like 'palerp', but actually restricted to the interval between the points,
--   with a signature like 'Data.Manifold.Riemannian.geodesicBetween'
--   rather than 'Data.AffineSpace.alerp'.
palerpB :: ∀ x. (PseudoAffine x, VectorSpace (Needle x), Scalar (Needle x) ~ ℝ)
                  => x -> x -> Maybe (D¹ -> x)
palerpB p₀ p₁ = case (toInterior p₀, p₁.-~.p₀) of
  (Just b, Just v) -> return $ \(D¹ t) -> b .+~^ ((t+1)/2) *^ v
  _ -> Nothing

-- | Like 'alerp', but actually restricted to the interval between the points.
alerpB :: ∀ x. (AffineSpace x, VectorSpace (Diff x), Scalar (Diff x) ~ ℝ)
                   => x -> x -> D¹ -> x
alerpB p1 p2 = case p2 .-. p1 of
  v -> \(D¹ t) -> p1 .+^ ((t+1)/2) *^ v



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

deriveAffine((),Double)
deriveAffine((),Rational)


instance Semimanifold (ZeroDim k) where
  type Needle (ZeroDim k) = ZeroDim k
  fromInterior = id
  toInterior = pure
  Origin .+~^ Origin = Origin
  Origin .-~^ Origin = Origin
  translateP = Tagged (.+~^)
instance PseudoAffine (ZeroDim k) where
  Origin .-~. Origin = pure Origin

instance ∀ a b . (Semimanifold a, Semimanifold b) => Semimanifold (a,b) where
  type Needle (a,b) = (Needle a, Needle b)
  type Interior (a,b) = (Interior a, Interior b)
  (a,b).+~^(v,w) = (a.+~^v, b.+~^w)
  (a,b).-~^(v,w) = (a.-~^v, b.-~^w)
  fromInterior (i,j) = (fromInterior i, fromInterior j)
  toInterior (a,b) = (,) <$> toInterior a <*> toInterior b
  translateP = Tagged $ \(a,b) (v,w) -> (ta a v, tb b w)
   where Tagged ta = translateP :: Tagged a (Interior a -> Needle a -> Interior a)
         Tagged tb = translateP :: Tagged b (Interior b -> Needle b -> Interior b)
  semimanifoldWitness = case ( semimanifoldWitness :: SemimanifoldWitness a
                             , semimanifoldWitness :: SemimanifoldWitness b ) of
     (SemimanifoldWitness BoundarylessWitness, SemimanifoldWitness BoundarylessWitness)
         -> SemimanifoldWitness BoundarylessWitness
instance (PseudoAffine a, PseudoAffine b) => PseudoAffine (a,b) where
  (a,b).-~.(c,d) = liftA2 (,) (a.-~.c) (b.-~.d)
  pseudoAffineWitness = case ( pseudoAffineWitness :: PseudoAffineWitness a
                             , pseudoAffineWitness :: PseudoAffineWitness b ) of
             (  PseudoAffineWitness (SemimanifoldWitness BoundarylessWitness)
              , PseudoAffineWitness (SemimanifoldWitness BoundarylessWitness) )
              ->PseudoAffineWitness (SemimanifoldWitness BoundarylessWitness)

instance ∀ a b c . (Semimanifold a, Semimanifold b, Semimanifold c)
                          => Semimanifold (a,b,c) where
  type Needle (a,b,c) = (Needle a, Needle b, Needle c)
  type Interior (a,b,c) = (Interior a, Interior b, Interior c)
  (a,b,c).+~^(v,w,x) = (a.+~^v, b.+~^w, c.+~^x)
  (a,b,c).-~^(v,w,x) = (a.-~^v, b.-~^w, c.-~^x)
  fromInterior (i,j,k) = (fromInterior i, fromInterior j, fromInterior k)
  toInterior (a,b,c) = liftA3 (,,) (toInterior a) (toInterior b) (toInterior c)
  translateP = Tagged $ \(a,b,c) (v,w,x) -> (ta a v, tb b w, tc c x)
   where Tagged ta = translateP :: Tagged a (Interior a -> Needle a -> Interior a)
         Tagged tb = translateP :: Tagged b (Interior b -> Needle b -> Interior b)
         Tagged tc = translateP :: Tagged c (Interior c -> Needle c -> Interior c)
  semimanifoldWitness = case ( semimanifoldWitness :: SemimanifoldWitness a
                             , semimanifoldWitness :: SemimanifoldWitness b
                             , semimanifoldWitness :: SemimanifoldWitness c ) of
             ( SemimanifoldWitness BoundarylessWitness
              ,SemimanifoldWitness BoundarylessWitness
              ,SemimanifoldWitness BoundarylessWitness )
                   -> SemimanifoldWitness BoundarylessWitness
instance (PseudoAffine a, PseudoAffine b, PseudoAffine c) => PseudoAffine (a,b,c) where
  (a,b,c).-~.(d,e,f) = liftA3 (,,) (a.-~.d) (b.-~.e) (c.-~.f)
  pseudoAffineWitness = case ( pseudoAffineWitness :: PseudoAffineWitness a
                             , pseudoAffineWitness :: PseudoAffineWitness b
                             , pseudoAffineWitness :: PseudoAffineWitness c ) of
             (  PseudoAffineWitness (SemimanifoldWitness BoundarylessWitness)
              , PseudoAffineWitness (SemimanifoldWitness BoundarylessWitness)
              , PseudoAffineWitness (SemimanifoldWitness BoundarylessWitness) )
              ->PseudoAffineWitness (SemimanifoldWitness BoundarylessWitness)




instance Semimanifold S⁰ where
  type Needle S⁰ = ZeroDim ℝ
  fromInterior = id
  toInterior = pure
  translateP = Tagged (.+~^)
  p .+~^ Origin = p
  p .-~^ Origin = p
instance PseudoAffine S⁰ where
  PositiveHalfSphere .-~. PositiveHalfSphere = pure Origin
  NegativeHalfSphere .-~. NegativeHalfSphere = pure Origin
  _ .-~. _ = Nothing

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
  D¹ x .-~. D¹ y
    | abs x < 1, abs y < 1  = return $ atanh x - atanh y
    | otherwise             = empty








tau :: ℝ
tau = 2 * pi

toS¹range :: ℝ -> ℝ
toS¹range φ = (φ+pi)`mod'`tau - pi




