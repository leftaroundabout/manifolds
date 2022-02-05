-- |
-- Module      : Math.Manifold.Core.PseudoAffine
-- Copyright   : (c) Justus Sagemüller 2016
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsag $ hvl.no
-- Stability   : experimental
-- Portability : portable
-- 

{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE UndecidableInstances     #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE DefaultSignatures        #-}
{-# LANGUAGE DeriveGeneric            #-}
{-# LANGUAGE StandaloneDeriving       #-}
{-# LANGUAGE UnicodeSyntax            #-}
{-# LANGUAGE EmptyCase                #-}
{-# LANGUAGE ConstraintKinds          #-}
{-# LANGUAGE ScopedTypeVariables      #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE CPP                      #-}


module Math.Manifold.Core.PseudoAffine where

import Data.VectorSpace
import Data.AffineSpace
import Data.Basis

import Data.Fixed (mod')
import Data.Void

import Math.Manifold.Core.Types.Internal
import Math.Manifold.VectorSpace.ZeroDimensional

import Control.Applicative
import Control.Arrow

import qualified GHC.Generics as Gnrx
import GHC.Generics (Generic, (:*:)(..))

import Data.CallStack (HasCallStack)

type ℝeal r = (RealFloat r, PseudoAffine r, Semimanifold r, Needle r ~ r)

-- | This is the reified form of the property that the interior of a semimanifold
--   is a manifold. These constraints would ideally be expressed directly as
--   superclass constraints, but that would require the @UndecidableSuperclasses@
--   extension, which is not reliable yet.
-- 
-- Also, if all those equality constraints are in scope, GHC tends to infer needlessly
-- complicated types like @'Needle' ('Needle' ('Needle' x))@, which is
-- the same as just @'Needle' x@.
data SemimanifoldWitness x where
  SemimanifoldWitness ::
      ( Semimanifold (Needle x)
      , Needle (Needle x) ~ Needle x )
     => SemimanifoldWitness x

data PseudoAffineWitness x where
  PseudoAffineWitness :: PseudoAffine (Needle x)
     => SemimanifoldWitness x -> PseudoAffineWitness x

infix 6 .-~., .-~!
infixl 6 .+~^, .-~^

class AdditiveGroup (Needle x) => Semimanifold x where
  -- | The space of &#x201c;ways&#x201d; starting from some reference point
  --   and going to some particular target point. Hence,
  --   the name: like a compass needle, but also with an actual length.
  --   For affine spaces, 'Needle' is simply the space of
  --   line segments (aka vectors) between two points, i.e. the same as 'Diff'.
  --   The 'AffineManifold' constraint makes that requirement explicit.
  -- 
  --   This space should be isomorphic to the tangent space (and in fact
  --   serves an in many ways similar role), however whereas the tangent space
  --   of a manifold is really infinitesimally small, needles actually allow
  --   macroscopic displacements.
  type Needle x :: *
  type Needle x = GenericNeedle x
  
  -- | Generalisation of the translation operation '.+^' to possibly non-flat
  --   manifolds, instead of affine spaces.
  (.+~^) :: x -> Needle x -> x
  default (.+~^) :: ( Generic x, Semimanifold (VRep x)
                    , Needle x ~ GenericNeedle x )
        => x -> Needle x -> x
  p.+~^GenericNeedle v = Gnrx.to (Gnrx.from p.+~^v :: Gnrx.Rep x Void)
  
  -- | Shorthand for @\\p v -> p .+~^ 'negateV' v@, which should obey the /asymptotic/ law
  --   
  -- @
  -- p .-~^ v .+~^ v &#x2245; p
  -- @
  --   
  --   Meaning: if @v@ is scaled down with sufficiently small factors /&#x3b7;/, then
  --   the difference @(p.-~^v.+~^v) .-~. p@ should eventually scale down even faster:
  --   as /O/ (/&#x3b7;/&#xb2;). For large vectors, it may however behave differently,
  --   except in flat spaces (where all this should be equivalent to the 'AffineSpace'
  --   instance).
  (.-~^) :: x -> Needle x -> x
  p .-~^ v = p .+~^ negateV v
  
  semimanifoldWitness :: SemimanifoldWitness x
  default semimanifoldWitness ::
      ( Semimanifold (Needle x), Needle (Needle x) ~ Needle x )
     => SemimanifoldWitness x
  semimanifoldWitness = SemimanifoldWitness

  
-- | This is the class underlying what we understand as manifolds. 
--   
--   The interface is almost identical to the better-known
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
-- 
--   The 'Semimanifold' and 'PseudoAffine' classes can be @anyclass@-derived
--   or empty-instantiated based on 'Generic' for product types (including newtypes) of
--   existing 'PseudoAffine' instances. For example, the definition
--
-- @
-- data Cylinder = CylinderPolar { zCyl :: !D¹, φCyl :: !S¹ }
--   deriving (Generic, Semimanifold, PseudoAffine)
-- @
-- 
--   is equivalent to
--
-- @
-- data Cylinder = CylinderPolar { zCyl :: !D¹, φCyl :: !S¹ }
--
-- data CylinderNeedle = CylinderPolarNeedle { δzCyl :: !(Needle D¹), δφCyl :: !(Needle S¹) }
-- 
-- instance Semimanifold Cylinder where
--   type Needle Cylinder = CylinderNeedle
--   CylinderPolar z φ .+~^ CylinderPolarNeedle δz δφ
--        = CylinderPolar (z.+~^δz) (φ.+~^δφ)
-- 
-- instance PseudoAffine Cylinder where
--   CylinderPolar z₁ φ₁ .-~. CylinderPolar z₀ φ₀
--        = CylinderPolarNeedle <$> z₁.-~.z₀ <*> φ₁.-~.φ₀
--   CylinderPolar z₁ φ₁ .-~! CylinderPolar z₀ φ₀
--        = CylinderPolarNeedle (z₁.-~!z₀) (φ₁.-~.φ₀)
-- @
class Semimanifold x => PseudoAffine x where
  -- | The path reaching from one point to another.
  --   Should only yield 'Nothing' if the points are on disjoint segments
  --   of a non&#x2013;path-connected space.
  --
  --   For a connected manifold, you may define this method as
  --
  -- @
  --   p.-~.q = pure (p.-~!q)
  -- @
  (.-~.) :: x -> x -> Maybe (Needle x)
  default (.-~.) :: ( Generic x, PseudoAffine (VRep x)
                    , Needle x ~ GenericNeedle x )
        => x -> x -> Maybe (Needle x)
  p.-~.q = GenericNeedle <$> Gnrx.from p .-~. (Gnrx.from q :: Gnrx.Rep x Void)
  
  -- | Unsafe version of '.-~.'. If the two points lie in disjoint regions,
  --   the behaviour is undefined.
  -- 
  --   Whenever @p@ and @q@ lie in a connected region, the identity
  --   
  -- @
  -- p .+~^ (q.-~.p) ≡ q
  -- @
  --   
  --   should hold (up to possible floating point rounding etc.).
  --   Meanwhile, you will in general have
  -- 
  -- @
  -- (p.+~^v).-~^v ≠ p
  -- @
  -- 
  -- (though in many instances this is at least for sufficiently small @v@ approximately equal).
  (.-~!) :: HasCallStack => x -> x -> Needle x
  default (.-~!) :: ( Generic x, PseudoAffine (VRep x)
                    , Needle x ~ GenericNeedle x )
        => x -> x -> Needle x
  p.-~!q = GenericNeedle $ Gnrx.from p .-~! (Gnrx.from q :: Gnrx.Rep x Void)
  {-# INLINE (.-~!) #-}
  
  pseudoAffineWitness :: PseudoAffineWitness x
  default pseudoAffineWitness ::
      PseudoAffine (Needle x)
     => PseudoAffineWitness x
  pseudoAffineWitness = PseudoAffineWitness semimanifoldWitness
  

  
  
-- | A fibre bundle combines points in the /base space/ @b@ with points in the /fibre/
--   @f@. The type @FibreBundle b f@ is thus isomorphic to the tuple space @(b,f)@, but
--   it can have a different topology, the prime example being 'TangentBundle', where
--   nearby points may have differently-oriented tangent spaces.
data FibreBundle b f = FibreBundle
      { baseSpace :: !b
      , fibreSpace :: !f
      } deriving (Generic, Show)

-- | Points on a manifold, combined with vectors in the respective tangent space.
type TangentBundle m = FibreBundle m (Needle m)
  


-- | Interpolate between points, approximately linearly. For
--   points that aren't close neighbours (i.e. lie in an almost
--   flat region), the pathway is basically undefined – save for
--   its end points.
-- 
--   A proper, really well-defined (on global scales) interpolation
--   only makes sense on a Riemannian manifold, as 'Data.Manifold.Riemannian.Geodesic'.
palerp :: ∀ x. (PseudoAffine x, VectorSpace (Needle x))
    => x -> x -> Maybe (Scalar (Needle x) -> x)
palerp p₀ p₁ = case p₁.-~.p₀ of
  Just v -> return $ \t -> p₀ .+~^ t *^ v
  _      -> Nothing

-- | Like 'palerp', but actually restricted to the interval between the points,
--   with a signature like 'Data.Manifold.Riemannian.geodesicBetween'
--   rather than 'Data.AffineSpace.alerp'.
palerpB :: ∀ x. (PseudoAffine x, VectorSpace (Needle x), Scalar (Needle x) ~ ℝ)
                  => x -> x -> Maybe (D¹ -> x)
palerpB p₀ p₁ = case p₁.-~.p₀ of
  Just v -> return $ \(D¹ t) -> p₀ .+~^ ((t+1)/2) *^ v
  _ -> Nothing

-- | Like 'alerp', but actually restricted to the interval between the points.
alerpB :: ∀ x. (AffineSpace x, VectorSpace (Diff x), Scalar (Diff x) ~ ℝ)
                   => x -> x -> D¹ -> x
alerpB p1 p2 = case p2 .-. p1 of
  v -> \(D¹ t) -> p1 .+^ ((t+1)/2) *^ v



#define deriveAffine(c,t)               \
instance (c) => Semimanifold (t) where { \
  type Needle (t) = Diff (t);             \
  (.+~^) = (.+^) };                        \
instance (c) => PseudoAffine (t) where {    \
  a.-~.b = pure (a.-.b);                     \
  (.-~!) = (.-.) }

deriveAffine((),Double)
deriveAffine((),Float)
deriveAffine((),Rational)

instance Semimanifold (ZeroDim k) where
  type Needle (ZeroDim k) = ZeroDim k
  Origin .+~^ Origin = Origin
  Origin .-~^ Origin = Origin
instance PseudoAffine (ZeroDim k) where
  Origin .-~! Origin = Origin
  Origin .-~. Origin = pure Origin

instance ∀ a b . (Semimanifold a, Semimanifold b) => Semimanifold (a,b) where
  type Needle (a,b) = (Needle a, Needle b)
  (a,b).+~^(v,w) = (a.+~^v, b.+~^w)
  (a,b).-~^(v,w) = (a.-~^v, b.-~^w)
  semimanifoldWitness = case ( semimanifoldWitness :: SemimanifoldWitness a
                             , semimanifoldWitness :: SemimanifoldWitness b ) of
     (SemimanifoldWitness, SemimanifoldWitness) -> SemimanifoldWitness
instance (PseudoAffine a, PseudoAffine b) => PseudoAffine (a,b) where
  (a,b).-~.(c,d) = liftA2 (,) (a.-~.c) (b.-~.d)
  (a,b).-~!(c,d) = (a.-~!c, b.-~!d)
  pseudoAffineWitness = case ( pseudoAffineWitness :: PseudoAffineWitness a
                             , pseudoAffineWitness :: PseudoAffineWitness b ) of
             (  PseudoAffineWitness (SemimanifoldWitness)
              , PseudoAffineWitness (SemimanifoldWitness) )
              ->PseudoAffineWitness (SemimanifoldWitness)

instance ∀ a b c . (Semimanifold a, Semimanifold b, Semimanifold c)
                          => Semimanifold (a,b,c) where
  type Needle (a,b,c) = (Needle a, Needle b, Needle c)
  (a,b,c).+~^(v,w,x) = (a.+~^v, b.+~^w, c.+~^x)
  (a,b,c).-~^(v,w,x) = (a.-~^v, b.-~^w, c.-~^x)
  semimanifoldWitness = case ( semimanifoldWitness :: SemimanifoldWitness a
                             , semimanifoldWitness :: SemimanifoldWitness b
                             , semimanifoldWitness :: SemimanifoldWitness c ) of
             ( SemimanifoldWitness, SemimanifoldWitness, SemimanifoldWitness )
                   -> SemimanifoldWitness
instance (PseudoAffine a, PseudoAffine b, PseudoAffine c) => PseudoAffine (a,b,c) where
  (a,b,c).-~!(d,e,f) = (a.-~!d, b.-~!e, c.-~!f)
  (a,b,c).-~.(d,e,f) = liftA3 (,,) (a.-~.d) (b.-~.e) (c.-~.f)
  pseudoAffineWitness = case ( pseudoAffineWitness :: PseudoAffineWitness a
                             , pseudoAffineWitness :: PseudoAffineWitness b
                             , pseudoAffineWitness :: PseudoAffineWitness c ) of
             (  PseudoAffineWitness SemimanifoldWitness
              , PseudoAffineWitness SemimanifoldWitness
              , PseudoAffineWitness SemimanifoldWitness )
              ->PseudoAffineWitness SemimanifoldWitness







instance Semimanifold (ℝP⁰_ r) where
  type Needle (ℝP⁰_ r) = ZeroDim r
  p .+~^ Origin = p
  p .-~^ Origin = p
instance PseudoAffine (ℝP⁰_ r) where
  ℝPZero .-~! ℝPZero = Origin
  ℝPZero .-~. ℝPZero = pure Origin

instance ℝeal r => Semimanifold (ℝP¹_ r) where
  type Needle (ℝP¹_ r) = r
  HemisphereℝP¹Polar r₀ .+~^ δr = HemisphereℝP¹Polar . toℝP¹range $ r₀ + δr
instance ℝeal r => PseudoAffine (ℝP¹_ r) where
  p.-~.q = pure (p.-~!q)
  HemisphereℝP¹Polar φ₁ .-~! HemisphereℝP¹Polar φ₀
     | δφ > pi/2     = δφ - pi
     | δφ < (-pi/2)  = δφ + pi
     | otherwise     = δφ
   where δφ = φ₁ - φ₀






tau :: RealFloat r => r
tau = 2 * pi

toS¹range :: RealFloat r => r -> r
toS¹range φ = (φ+pi)`mod'`tau - pi

toℝP¹range :: RealFloat r => r -> r
toℝP¹range φ = (φ+pi/2)`mod'`pi - pi/2

toUnitrange :: RealFloat r => r -> r
toUnitrange φ = (φ+1)`mod'`2 - 1






data NeedleProductSpace f g p = NeedleProductSpace
            !(Needle (f p)) !(Needle (g p)) deriving (Generic)
instance (Semimanifold (f p), Semimanifold (g p))
    => AdditiveGroup (NeedleProductSpace f g p)
instance ( Semimanifold (f p), Semimanifold (g p)
         , VectorSpace (Needle (f p)), VectorSpace (Needle (g p))
         , Scalar (Needle (f p)) ~ Scalar (Needle (g p)) )
    => VectorSpace (NeedleProductSpace f g p)
instance ( Semimanifold (f p), Semimanifold (g p)
         , InnerSpace (Needle (f p)), InnerSpace (Needle (g p))
         , Scalar (Needle (f p)) ~ Scalar (Needle (g p))
         , Num (Scalar (Needle (f p))) )
    => InnerSpace (NeedleProductSpace f g p)
instance (Semimanifold (f p), Semimanifold (g p))
    => AffineSpace (NeedleProductSpace f g p) where
  type Diff (NeedleProductSpace f g p) = NeedleProductSpace f g p
  (.+^) = (^+^)
  (.-.) = (^-^)
instance (Semimanifold (f p), Semimanifold (g p))
    => Semimanifold (NeedleProductSpace f g p) where
  type Needle (NeedleProductSpace f g p) = NeedleProductSpace f g p
  (.+~^) = (^+^)
instance (PseudoAffine (f p), PseudoAffine (g p))
    => PseudoAffine (NeedleProductSpace f g p) where
  p.-~.q = Just $ p.-.q
  (.-~!) = (.-.)
instance ( Semimanifold (f p), Semimanifold (g p)
         , HasBasis (Needle (f p)), HasBasis (Needle (g p))
         , Scalar (Needle (f p)) ~ Scalar (Needle (g p)) )
    => HasBasis (NeedleProductSpace f g p) where
  type Basis (NeedleProductSpace f g p) = Either (Basis (Needle (f p)))
                                                     (Basis (Needle (g p)))
  basisValue (Left bf) = NeedleProductSpace (basisValue bf) zeroV
  basisValue (Right bg) = NeedleProductSpace zeroV (basisValue bg)
  decompose (NeedleProductSpace vf vg)
        = map (first Left) (decompose vf) ++ map (first Right) (decompose vg)
  decompose' (NeedleProductSpace vf _) (Left bf) = decompose' vf bf
  decompose' (NeedleProductSpace _ vg) (Right bg) = decompose' vg bg




newtype GenericNeedle x = GenericNeedle {getGenericNeedle :: Needle (VRep x)}
    deriving (Generic)

instance AdditiveGroup (Needle (VRep x)) => AdditiveGroup (GenericNeedle x) where
  GenericNeedle v ^+^ GenericNeedle w = GenericNeedle $ v ^+^ w
  negateV = GenericNeedle . negateV . getGenericNeedle
  zeroV = GenericNeedle zeroV
instance VectorSpace (Needle (VRep x)) => VectorSpace (GenericNeedle x) where
  type Scalar (GenericNeedle x) = Scalar (Needle (VRep x))
  (*^) μ = GenericNeedle . (*^) μ . getGenericNeedle
instance InnerSpace (Needle (VRep x)) => InnerSpace (GenericNeedle x) where
  GenericNeedle v <.> GenericNeedle w = v <.> w
instance AdditiveGroup (Needle (VRep x)) => AffineSpace (GenericNeedle x) where
  type Diff (GenericNeedle x) = GenericNeedle x
  (.-.) = (^-^)
  (.+^) = (^+^)
instance AdditiveGroup (Needle (VRep x)) => Semimanifold (GenericNeedle x) where
  type Needle (GenericNeedle x) = GenericNeedle x
  (.+~^) = (.+^)
instance AdditiveGroup (Needle (VRep x)) => PseudoAffine (GenericNeedle x) where
  GenericNeedle v .-~. GenericNeedle w = Just $ GenericNeedle (v ^-^ w)
  GenericNeedle v .-~! GenericNeedle w = GenericNeedle (v ^-^ w)




instance ∀ a s . Semimanifold a => Semimanifold (Gnrx.Rec0 a s) where
  type Needle (Gnrx.Rec0 a s) = Needle a
  semimanifoldWitness = case semimanifoldWitness :: SemimanifoldWitness a of
           SemimanifoldWitness
               -> SemimanifoldWitness
  Gnrx.K1 p .+~^ v = Gnrx.K1 $ p .+~^ v
instance ∀ f p i c . Semimanifold (f p) => Semimanifold (Gnrx.M1 i c f p) where
  type Needle (Gnrx.M1 i c f p) = Needle (f p)
  semimanifoldWitness = case semimanifoldWitness :: SemimanifoldWitness (f p) of
           SemimanifoldWitness -> SemimanifoldWitness
  Gnrx.M1 p.+~^v = Gnrx.M1 $ p.+~^v
instance ∀ f g p . (Semimanifold (f p), Semimanifold (g p))
         => Semimanifold ((f :*: g) p) where
  type Needle ((f:*:g) p) = NeedleProductSpace f g p
  semimanifoldWitness = case ( semimanifoldWitness :: SemimanifoldWitness (f p)
                             , semimanifoldWitness :: SemimanifoldWitness (g p) ) of
           ( SemimanifoldWitness, SemimanifoldWitness )
               -> SemimanifoldWitness
  (p:*:q).+~^(NeedleProductSpace v w) = (p.+~^v) :*: (q.+~^w)




instance ∀ a s . PseudoAffine a => PseudoAffine (Gnrx.Rec0 a s) where
  pseudoAffineWitness = case pseudoAffineWitness :: PseudoAffineWitness a of
           PseudoAffineWitness SemimanifoldWitness
               -> PseudoAffineWitness SemimanifoldWitness
  Gnrx.K1 p .-~. Gnrx.K1 q = p .-~. q
  Gnrx.K1 p .-~! Gnrx.K1 q = p .-~! q
instance ∀ f p i c . PseudoAffine (f p) => PseudoAffine (Gnrx.M1 i c f p) where
  pseudoAffineWitness = case pseudoAffineWitness :: PseudoAffineWitness (f p) of
           PseudoAffineWitness SemimanifoldWitness
               -> PseudoAffineWitness SemimanifoldWitness
  Gnrx.M1 p .-~. Gnrx.M1 q = p .-~. q
  Gnrx.M1 p .-~! Gnrx.M1 q = p .-~! q
instance ∀ f g p . (PseudoAffine (f p), PseudoAffine (g p))
         => PseudoAffine ((f :*: g) p) where
  pseudoAffineWitness = case ( pseudoAffineWitness :: PseudoAffineWitness (f p)
                             , pseudoAffineWitness :: PseudoAffineWitness (g p) ) of
           ( PseudoAffineWitness SemimanifoldWitness
            ,PseudoAffineWitness SemimanifoldWitness )
               -> PseudoAffineWitness SemimanifoldWitness
  (pf:*:pg) .-~. (qf:*:qg) = NeedleProductSpace <$> (pf.-~.qf) <*> (pg.-~.qg)
  (pf:*:pg) .-~! (qf:*:qg) = NeedleProductSpace     (pf.-~!qf)     (pg.-~!qg)


type VRep x = Gnrx.Rep x Void



-- | A (closed) cone over a space @x@ is the product of @x@ with the closed interval 'D¹'
--   of “heights”,
--   except on its “tip”: here, @x@ is smashed to a single point.
--   
--   This construct becomes (homeomorphic-to-) an actual geometric cone (and to 'D²') in the
--   special case @x = 'S¹'@.
data CD¹ x = CD¹ { hParamCD¹ :: !(Scalar (Needle x)) -- ^ Range @[0, 1]@
                 , pParamCD¹ :: !x                   -- ^ Irrelevant at @h = 0@.
                 } deriving (Generic)
deriving instance (Show x, Show (Scalar (Needle x))) => Show (CD¹ x)


-- | An open cone is homeomorphic to a closed cone without the “lid”,
--   i.e. without the “last copy” of @x@, at the far end of the height
--   interval. Since that means the height does not include its supremum, it is actually
--   more natural to express it as the entire real ray, hence the name.
data Cℝay x = Cℝay { hParamCℝay :: !(Scalar (Needle x))  -- ^ Range @[0, ∞[@
                   , pParamCℝay :: !x                    -- ^ Irrelevant at @h = 0@.
                   } deriving (Generic)
deriving instance (Show x, Show (Scalar (Needle x))) => Show (Cℝay x)

