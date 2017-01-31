-- |
-- Module      : Data.Manifold.Shade
-- Copyright   : (c) Justus Sagemüller 2016
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsagemue $ uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ParallelListComp           #-}
{-# LANGUAGE UnicodeSyntax              #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE ViewPatterns               #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE CPP                        #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE LiberalTypeSynonyms        #-}
{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE TemplateHaskell            #-}


module Data.Manifold.Shade (
       -- * Shades 
         Shade(..), pattern(:±), Shade'(..), (|±|), IsShade
       -- ** Lenses
       , shadeCtr, shadeExpanse, shadeNarrowness
       -- ** Construction
       , fullShade, fullShade', pointsShades, pointsShade's
       , pointsCovers, pointsCover's, coverAllAround
       -- ** Evaluation
       , occlusion, prettyShowsPrecShade', prettyShowShade', LtdErrorShow
       -- ** Misc
       , factoriseShade, orthoShades, (✠), intersectShade's, linIsoTransformShade
       , embedShade, projectShade
       , Refinable, subShade', refineShade', convolveShade', coerceShade
       , mixShade's, dualShade
       -- * Misc
       , shadesMerge, pointsShades', pseudoECM, convolveMetric
       , WithAny(..), shadeWithAny, shadeWithoutAnything
       , estimateLocalJacobian
       , DifferentialEqn, LocalDifferentialEqn(..)
       , propagateDEqnSolution_loc, LocalDataPropPlan(..)
       , rangeOnGeodesic, rangeWithinVertices
    ) where


import Data.List hiding (filter, all, elem, sum, foldr1)
import Data.Maybe
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE
import Data.Semigroup
import Control.DeepSeq

import Data.VectorSpace
import Data.AffineSpace
import Math.LinearMap.Category
import Data.Tagged
import Linear (_x,_y,_z,_w)

import Data.Manifold.Types
import Data.Manifold.Types.Primitive ((^))
import Data.Manifold.PseudoAffine
import Data.Manifold.Riemannian
import Data.Manifold.Atlas
import Data.Function.Affine
import Data.Manifold.Function.Quadratic

import Data.Embedding

import Control.Lens (Lens', (^.), view, _1, _2, mapping, (&))
import Control.Lens.TH

import qualified Prelude as Hask hiding(foldl, sum, sequence)
import qualified Control.Applicative as Hask
import qualified Data.Foldable       as Hask
import Data.Foldable (all, elem, toList, sum, foldr1)

import Control.Category.Constrained.Prelude hiding
     ((^), all, elem, sum, forM, Foldable(..), foldr1, Traversable, traverse)
import Control.Arrow.Constrained
import Control.Monad.Constrained hiding (forM)

import GHC.Generics (Generic)

import Text.Show.Number


-- | A 'Shade' is a very crude description of a region within a manifold. It
--   can be interpreted as either an ellipsoid shape, or as the Gaussian peak
--   of a normal distribution (use <http://hackage.haskell.org/package/manifold-random>
--   for actually sampling from that distribution).
-- 
--   For a /precise/ description of an arbitrarily-shaped connected subset of a manifold,
--   there is 'Region', whose implementation is vastly more complex.
data Shade x = Shade { _shadeCtr :: !(Interior x)
                     , _shadeExpanse :: !(Metric' x) }
deriving instance (Show (Interior x), Show (Metric' x), WithField ℝ PseudoAffine x)
                => Show (Shade x)

-- | A &#x201c;co-shade&#x201d; can describe ellipsoid regions as well, but unlike
--   'Shade' it can be unlimited / infinitely wide in some directions.
--   It does OTOH need to have nonzero thickness, which 'Shade' needs not.
data Shade' x = Shade' { _shade'Ctr :: !(Interior x)
                       , _shade'Narrowness :: !(Metric x) }

data LocalDifferentialEqn x ð y = LocalDifferentialEqn {
      _predictDerivatives :: Shade' ð -> Maybe (Shade' (LocalLinear x y))
    , _rescanDerivatives :: Shade' (LocalLinear x y)
                             -> Shade' y -> (Maybe (Shade' y), Maybe (Shade' ð))
    }
makeLenses ''LocalDifferentialEqn

type DifferentialEqn x ð y = Shade (x,y) -> LocalDifferentialEqn x ð y

data LocalDataPropPlan x ym yr = LocalDataPropPlan
       { _sourcePosition :: !(Interior x)
       , _targetPosOffset :: !(Needle x)
       , _sourceData, _targetAPrioriData :: !ym
       , _relatedData :: [(Needle x, yr)]
       }
deriving instance (Show (Interior x), Show ym, Show yr, Show (Needle x))
             => Show (LocalDataPropPlan x ym yr)

makeLenses ''LocalDataPropPlan


class IsShade shade where
--  type (*) shade :: *->*
  -- | Access the center of a 'Shade' or a 'Shade''.
  shadeCtr :: Lens' (shade x) (Interior x)
--  -- | Convert between 'Shade' and 'Shade' (which must be neither singular nor infinite).
--  unsafeDualShade :: WithField ℝ Manifold x => shade x -> shade* x
  -- | Check the statistical likelihood-density of a point being within a shade.
  --   This is taken as a normal distribution.
  occlusion :: ( PseudoAffine x, SimpleSpace (Needle x)
               , s ~ (Scalar (Needle x)), RealFloat' s )
                => shade x -> x -> s
  factoriseShade :: ( PseudoAffine x, SimpleSpace (Needle x)
                    , PseudoAffine y, SimpleSpace (Needle y)
                    , Scalar (Needle x) ~ Scalar (Needle y) )
                => shade (x,y) -> (shade x, shade y)
  coerceShade :: (Manifold x, Manifold y, LocallyCoercible x y) => shade x -> shade y
  -- | ASCII version of '✠'.
  orthoShades :: ( PseudoAffine x, SimpleSpace (Needle x)
           , PseudoAffine y, SimpleSpace (Needle y)
           , Scalar (Needle x) ~ Scalar (Needle y) )
                => shade x -> shade y -> shade (x,y)
  linIsoTransformShade :: ( SimpleSpace x, SimpleSpace y, Scalar x ~ Scalar y
                          , Num' (Scalar x) )
                          => (x+>y) -> shade x -> shade y
  -- | Squash a shade down into a lower dimensional space.
  projectShade :: ( Semimanifold x, Semimanifold y
                  , Object (Affine s) (Interior x), Object (Affine s) (Interior y)
                  , SemiInner (Needle x), SemiInner (Needle y) )
                        => Embedding (Affine s) (Interior x) (Interior y)
                              -> shade y -> shade x
  -- | Include a shade in a higher-dimensional space. Notice that this behaves
  --   fundamentally different for 'Shade' and 'Shade''. For 'Shade', it gives
  --   a “flat image” of the region, whereas for 'Shade'' it gives an “extrusion
  --   pillar” pointing in the projection's orthogonal complement.
  embedShade :: ( Semimanifold x, Semimanifold y
                , Object (Affine s) (Interior x), Object (Affine s) (Interior y)
                , SemiInner (Needle x), SemiInner (Needle y) )
                        => Embedding (Affine s) (Interior x) (Interior y)
                              -> shade x -> shade y
  

infixl 5 ✠
-- | Combine two shades on independent subspaces to a shade with the same
--   properties on the subspaces (see 'factoriseShade') and no covariance.
(✠) :: ( IsShade shade, PseudoAffine x, SimpleSpace (Needle x)
       , PseudoAffine y, SimpleSpace (Needle y)
       , Scalar (Needle x) ~ Scalar (Needle y) )
                => shade x -> shade y -> shade (x,y)
(✠) = orthoShades

instance IsShade Shade where
  shadeCtr f (Shade c e) = fmap (`Shade`e) $ f c
  occlusion = occ pseudoAffineWitness dualSpaceWitness
   where occ :: ∀ x s . ( PseudoAffine x, SimpleSpace (Needle x)
                        , Scalar (Needle x) ~ s, RealFloat' s )
                    => PseudoAffineWitness x -> DualNeedleWitness x -> Shade x -> x -> s
         occ (PseudoAffineWitness (SemimanifoldWitness _)) DualSpaceWitness (Shade p₀ δ)
                 = \p -> case toInterior p >>= (.-~.p₀) of
           (Just vd) | mSq <- normSq δinv vd
                     , mSq == mSq  -- avoid NaN
                     -> exp (negate mSq)
           _         -> zeroV
          where δinv = dualNorm δ
  factoriseShade = fs dualSpaceWitness dualSpaceWitness
   where fs :: ∀ x y . ( PseudoAffine x, SimpleSpace (Needle x)
                       , PseudoAffine y, SimpleSpace (Needle y)
                       , Scalar (Needle x) ~ Scalar (Needle y) )
               => DualNeedleWitness x -> DualNeedleWitness y
                       -> Shade (x,y) -> (Shade x, Shade y)
         fs DualSpaceWitness DualSpaceWitness (Shade (x₀,y₀) δxy)
                   = (Shade x₀ δx, Shade y₀ δy)
          where (δx,δy) = summandSpaceNorms δxy
  orthoShades = fs dualSpaceWitness dualSpaceWitness
   where fs :: ∀ x y . ( PseudoAffine x, SimpleSpace (Needle x)
                       , PseudoAffine y, SimpleSpace (Needle y)
                       , Scalar (Needle x) ~ Scalar (Needle y) )
               => DualNeedleWitness x -> DualNeedleWitness y
                       -> Shade x -> Shade y ->  Shade (x,y)
         fs DualSpaceWitness DualSpaceWitness (Shade x δx) (Shade y δy)
             = Shade (x,y) $ sumSubspaceNorms δx δy
  coerceShade = cS dualSpaceWitness dualSpaceWitness
   where cS :: ∀ x y . (LocallyCoercible x y)
                => DualNeedleWitness x -> DualNeedleWitness y -> Shade x -> Shade y
         cS DualSpaceWitness DualSpaceWitness
                    = \(Shade x δxym) -> Shade (internCoerce x) (tN δxym)
          where tN = case oppositeLocalCoercion :: CanonicalDiffeomorphism y x of
                      CanonicalDiffeomorphism ->
                       transformNorm . arr $ coerceNeedle' ([]::[(y,x)])
                internCoerce = case interiorLocalCoercion ([]::[(x,y)]) of
                      CanonicalDiffeomorphism -> locallyTrivialDiffeomorphism
  linIsoTransformShade = lits linearManifoldWitness linearManifoldWitness
                              dualSpaceWitness dualSpaceWitness
   where lits :: ∀ x y . ( LinearSpace x, LinearSpace y
                         , Scalar x ~ Scalar y, Num' (Scalar x) )
               => LinearManifoldWitness x -> LinearManifoldWitness y
                   -> DualSpaceWitness x -> DualSpaceWitness y
                       -> (x+>y) -> Shade x -> Shade y
         lits (LinearManifoldWitness BoundarylessWitness)
              (LinearManifoldWitness BoundarylessWitness)
              DualSpaceWitness DualSpaceWitness
              f (Shade x δx)
                  = Shade (f $ x) (transformNorm (adjoint $ f) δx)
  embedShade = ps' (semimanifoldWitness, semimanifoldWitness)
   where ps' :: ∀ s x y . ( Object (Affine s) (Interior x), Object (Affine s) (Interior y)
                          , SemiInner (Needle x), SemiInner (Needle y) )
                        => (SemimanifoldWitness x, SemimanifoldWitness y)
               -> Embedding (Affine s) (Interior x) (Interior y)
                              -> Shade x -> Shade y
         ps' (SemimanifoldWitness _, SemimanifoldWitness _)
              (Embedding q _) (Shade x e) = Shade y (transformVariance j e)
          where y = q $ x
                (_,j) = evalAffine q x
  projectShade = ps' (semimanifoldWitness, semimanifoldWitness)
   where ps' :: ∀ s x y . ( Object (Affine s) (Interior x), Object (Affine s) (Interior y)
                          , SemiInner (Needle x), SemiInner (Needle y) )
                        => (SemimanifoldWitness x, SemimanifoldWitness y)
               -> Embedding (Affine s) (Interior x) (Interior y)
                              -> Shade y -> Shade x
         ps' (SemimanifoldWitness _, SemimanifoldWitness _)
              (Embedding _ q) (Shade x e) = Shade y (transformVariance j e)
          where y = q $ x
                (_,j) = evalAffine q x


dualShade :: ∀ x . (PseudoAffine x, SimpleSpace (Needle x))
                => Shade x -> Shade' x
dualShade = case dualSpaceWitness :: DualSpaceWitness (Needle x) of
    DualSpaceWitness -> \(Shade c e) -> Shade' c $ dualNorm e

instance ImpliesMetric Shade where
  type MetricRequirement Shade x = (Manifold x, SimpleSpace (Needle x))
  inferMetric' (Shade _ e) = e
  inferMetric = im dualSpaceWitness
   where im :: (Manifold x, SimpleSpace (Needle x))
                   => DualNeedleWitness x -> Shade x -> Metric x
         im DualSpaceWitness (Shade _ e) = dualNorm e

instance ImpliesMetric Shade' where
  type MetricRequirement Shade' x = (Manifold x, SimpleSpace (Needle x))
  inferMetric (Shade' _ e) = e
  inferMetric' (Shade' _ e) = dualNorm e

shadeExpanse :: Lens' (Shade x) (Metric' x)
shadeExpanse f (Shade c e) = fmap (Shade c) $ f e

instance IsShade Shade' where
  shadeCtr f (Shade' c e) = fmap (`Shade'`e) $ f c
  occlusion = occ pseudoAffineWitness
   where occ :: ∀ x s . ( PseudoAffine x, SimpleSpace (Needle x)
                        , Scalar (Needle x) ~ s, RealFloat' s )
                    => PseudoAffineWitness x -> Shade' x -> x -> s
         occ (PseudoAffineWitness (SemimanifoldWitness _)) (Shade' p₀ δinv) p
               = case toInterior p >>= (.-~.p₀) of
           (Just vd) | mSq <- normSq δinv vd
                     , mSq == mSq  -- avoid NaN
                     -> exp (negate mSq)
           _         -> zeroV
  factoriseShade (Shade' (x₀,y₀) δxy) = (Shade' x₀ δx, Shade' y₀ δy)
   where (δx,δy) = summandSpaceNorms δxy
  orthoShades (Shade' x δx) (Shade' y δy) = Shade' (x,y) $ sumSubspaceNorms δx δy
  coerceShade = cS
   where cS :: ∀ x y . (LocallyCoercible x y) => Shade' x -> Shade' y
         cS = \(Shade' x δxym) -> Shade' (internCoerce x) (tN δxym)
          where tN = case oppositeLocalCoercion :: CanonicalDiffeomorphism y x of
                      CanonicalDiffeomorphism ->
                       transformNorm . arr $ coerceNeedle ([]::[(y,x)])
                internCoerce = case interiorLocalCoercion ([]::[(x,y)]) of
                      CanonicalDiffeomorphism -> locallyTrivialDiffeomorphism
  linIsoTransformShade = lits linearManifoldWitness linearManifoldWitness
                              dualSpaceWitness dualSpaceWitness
   where lits :: ∀ x y . ( SimpleSpace x, SimpleSpace y
                         , Scalar x ~ Scalar y, RealFloat' (Scalar x) )
               => LinearManifoldWitness x -> LinearManifoldWitness y
                   -> DualSpaceWitness x -> DualSpaceWitness y
                       -> (x+>y) -> Shade' x -> Shade' y
         lits (LinearManifoldWitness BoundarylessWitness)
              (LinearManifoldWitness BoundarylessWitness)
              DualSpaceWitness DualSpaceWitness
               f (Shade' x δx)
          = Shade' (f $ x) (transformNorm (pseudoInverse f) δx)
  embedShade = ps (semimanifoldWitness, semimanifoldWitness)
   where ps :: ∀ s x y . ( Object (Affine s) (Interior x), Object (Affine s) (Interior y)
                         , SemiInner (Needle x), SemiInner (Needle y) )
                        => (SemimanifoldWitness x, SemimanifoldWitness y)
               -> Embedding (Affine s) (Interior x) (Interior y)
                              -> Shade' x -> Shade' y
         ps (SemimanifoldWitness _, SemimanifoldWitness _)
             (Embedding q p) (Shade' x e) = Shade' y (transformNorm j e)
          where y = q $ x
                (_,j) = evalAffine p y
  projectShade = ps (semimanifoldWitness, semimanifoldWitness)
   where ps :: ∀ s x y . ( Object (Affine s) (Interior x), Object (Affine s) (Interior y)
                         , SemiInner (Needle x), SemiInner (Needle y) )
                        => (SemimanifoldWitness x, SemimanifoldWitness y)
               -> Embedding (Affine s) (Interior x) (Interior y)
                              -> Shade' y -> Shade' x
         ps (SemimanifoldWitness _, SemimanifoldWitness _)
             (Embedding p q) (Shade' x e) = Shade' y (transformNorm j e)
          where y = q $ x
                (_,j) = evalAffine p y


shadeNarrowness :: Lens' (Shade' x) (Metric x)
shadeNarrowness f (Shade' c e) = fmap (Shade' c) $ f e

instance ∀ x . (PseudoAffine x) => Semimanifold (Shade x) where
  type Needle (Shade x) = Needle x
  fromInterior = id
  toInterior = pure
  translateP = Tagged (.+~^)
  (.+~^) = case semimanifoldWitness :: SemimanifoldWitness x of
             SemimanifoldWitness BoundarylessWitness
                   -> \(Shade c e) v -> Shade (c.+~^v) e
  (.-~^) = case semimanifoldWitness :: SemimanifoldWitness x of
             SemimanifoldWitness BoundarylessWitness
                   -> \(Shade c e) v -> Shade (c.-~^v) e
  semimanifoldWitness = case semimanifoldWitness :: SemimanifoldWitness x of
                         (SemimanifoldWitness BoundarylessWitness)
                          -> SemimanifoldWitness BoundarylessWitness

instance (WithField ℝ PseudoAffine x, Geodesic (Interior x), SimpleSpace (Needle x))
             => Geodesic (Shade x) where
  geodesicBetween = gb dualSpaceWitness
   where gb :: DualNeedleWitness x -> Shade x -> Shade x -> Maybe (D¹ -> Shade x)
         gb DualSpaceWitness (Shade c (Norm e)) (Shade ζ (Norm η)) = pure interp
          where interp t@(D¹ q) = Shade (pinterp t)
                                 (Norm . arr . lerp ed ηd $ (q+1)/2)
                ed@(LinearMap _) = arr e
                ηd@(LinearMap _) = arr η
                Just pinterp = geodesicBetween c ζ

instance (AffineManifold x) => Semimanifold (Shade' x) where
  type Needle (Shade' x) = Needle x
  fromInterior = id
  toInterior = pure
  translateP = Tagged (.+~^)
  (.+~^) = case boundarylessWitness :: BoundarylessWitness x of
      BoundarylessWitness -> \(Shade' c e) v -> Shade' (c.+~^v) e
  (.-~^) = case boundarylessWitness :: BoundarylessWitness x of
      BoundarylessWitness -> \(Shade' c e) v -> Shade' (c.-~^v) e
  semimanifoldWitness = case semimanifoldWitness :: SemimanifoldWitness x of
     SemimanifoldWitness BoundarylessWitness -> SemimanifoldWitness BoundarylessWitness

instance ∀ x . (WithField ℝ AffineManifold x, Geodesic x, SimpleSpace (Needle x))
            => Geodesic (Shade' x) where
  geodesicBetween (Shade' c e) (Shade' ζ η) = pure interp
   where sharedSpan = sharedNormSpanningSystem e η
         interp t = Shade' (pinterp t)
                           (spanNorm [ v ^/ (alerpB 1 (recip qη) t)
                                     | (v,qη) <- sharedSpan ])
         Just pinterp = case geodesicWitness :: GeodesicWitness x of
            GeodesicWitness _ -> geodesicBetween c ζ

fullShade :: WithField ℝ PseudoAffine x => Interior x -> Metric' x -> Shade x
fullShade ctr expa = Shade ctr expa

fullShade' :: WithField ℝ PseudoAffine x => Interior x -> Metric x -> Shade' x
fullShade' ctr expa = Shade' ctr expa


infixl 6 :±, |±|

-- | Span a 'Shade' from a center point and multiple deviation-vectors.
#if GLASGOW_HASKELL < 800
pattern (:±) :: ()
#else
pattern (:±) :: (WithField ℝ Manifold x, SimpleSpace (Needle x))
#endif
             => (WithField ℝ Manifold x, SimpleSpace (Needle x))
                         => Interior x -> [Needle x] -> Shade x
pattern x :± shs <- Shade x (varianceSpanningSystem -> shs)
 where x :± shs = fullShade x $ spanVariance shs

-- | Similar to ':±', but instead of expanding the shade, each vector /restricts/ it.
--   Iff these form a orthogonal basis (in whatever sense applicable), then both
--   methods will be equivalent.
-- 
--   Note that '|±|' is only possible, as such, in an inner-product space; in
--   general you need reciprocal vectors ('Needle'') to define a 'Shade''.
(|±|) :: ∀ x . WithField ℝ EuclidSpace x => x -> [Needle x] -> Shade' x
(|±|) = case boundarylessWitness :: BoundarylessWitness x of
   BoundarylessWitness -> \x shs -> Shade' x $ spanNorm [v^/(v<.>v) | v<-shs]



                 


-- | Attempt to find a 'Shade' that describes the distribution of given points.
--   At least in an affine space (and thus locally in any manifold), this can be used to
--   estimate the parameters of a normal distribution from which some points were
--   sampled. Note that some points will be &#x201c;outside&#x201d; of the shade,
--   as happens for a normal distribution with some statistical likelyhood.
--   (Use 'pointsCovers' if you need to prevent that.)
-- 
--   For /nonconnected/ manifolds it will be necessary to yield separate shades
--   for each connected component. And for an empty input list, there is no shade!
--   Hence the result type is a list.
pointsShades :: (WithField ℝ PseudoAffine x, SimpleSpace (Needle x))
                                 => [Interior x] -> [Shade x]
pointsShades = map snd . pointsShades' mempty . map fromInterior

coverAllAround :: ∀ x . (WithField ℝ PseudoAffine x, SimpleSpace (Needle x))
                  => Interior x -> [Needle x] -> Shade x
coverAllAround x₀ offs = Shade x₀
         $ guaranteeIn dualSpaceWitness offs
               (scaleNorm (1/fromIntegral (length offs)) $ spanVariance offs)
 where guaranteeIn :: DualNeedleWitness x -> [Needle x] -> Metric' x -> Metric' x
       guaranteeIn w@DualSpaceWitness offs ex
          = case offs >>= \v -> guard ((ex'|$|v) > 1) >> [(v, spanVariance [v])] of
             []   -> ex
             outs -> guaranteeIn w (fst<$>outs)
                                 ( densifyNorm $
                                    ex <> scaleNorm
                                                (sqrt . recip . fromIntegral
                                                            $ 2 * length outs)
                                                (mconcat $ snd<$>outs)
                                 )
        where ex' = dualNorm ex

-- | Like 'pointsShades', but ensure that all points are actually in
--   the shade, i.e. if @['Shade' x₀ ex]@ is the result then
--   @'metric' (recipMetric ex) (p-x₀) ≤ 1@ for all @p@ in the list.
pointsCovers :: ∀ x . (WithField ℝ PseudoAffine x, SimpleSpace (Needle x))
                          => [Interior x] -> [Shade x]
pointsCovers = case pseudoAffineWitness :: PseudoAffineWitness x of
                 (PseudoAffineWitness (SemimanifoldWitness BoundarylessWitness)) ->
                  \ps -> map (\(ps', Shade x₀ _)
                                -> coverAllAround x₀ [v | p<-ps'
                                                        , let Just v
                                                                 = p.-~.fromInterior x₀])
                             (pointsShades' mempty (fromInterior<$>ps) :: [([x], Shade x)])

pointsShade's :: ∀ x . (WithField ℝ PseudoAffine x, SimpleSpace (Needle x))
                     => [Interior x] -> [Shade' x]
pointsShade's = case dualSpaceWitness :: DualNeedleWitness x of
 DualSpaceWitness -> map (\(Shade c e :: Shade x) -> Shade' c $ dualNorm e) . pointsShades

pointsCover's :: ∀ x . (WithField ℝ PseudoAffine x, SimpleSpace (Needle x))
                     => [Interior x] -> [Shade' x]
pointsCover's = case dualSpaceWitness :: DualNeedleWitness x of
 DualSpaceWitness -> map (\(Shade c e :: Shade x) -> Shade' c $ dualNorm e) . pointsCovers

pseudoECM :: ∀ x p . (WithField ℝ PseudoAffine x, SimpleSpace (Needle x), Hask.Functor p)
                => p x -> NonEmpty x -> (x, ([x],[x]))
pseudoECM = case semimanifoldWitness :: SemimanifoldWitness x of
 SemimanifoldWitness _ ->
   \_ (p₀ NE.:| psr) -> foldl' ( \(acc, (rb,nr)) (i,p)
                                -> case (p.-~.acc, toInterior acc) of 
                                      (Just δ, Just acci)
                                        -> (acci .+~^ δ^/i, (p:rb, nr))
                                      _ -> (acc, (rb, p:nr)) )
                             (p₀, mempty)
                             ( zip [1..] $ p₀:psr )

pointsShades' :: ∀ x . (WithField ℝ PseudoAffine x, SimpleSpace (Needle x))
                                => Metric' x -> [x] -> [([x], Shade x)]
pointsShades' _ [] = []
pointsShades' minExt ps = case (expa, toInterior ctr) of 
                           (Just e, Just c)
                             -> (ps, fullShade c e) : pointsShades' minExt unreachable
                           _ -> pointsShades' minExt inc'd
                                  ++ pointsShades' minExt unreachable
 where (ctr,(inc'd,unreachable)) = pseudoECM ([]::[x]) $ NE.fromList ps
       expa = ( (<>minExt) . spanVariance . map (^/ fromIntegral (length ps)) )
              <$> mapM (.-~.ctr) ps
       

-- | Attempt to reduce the number of shades to fewer (ideally, a single one).
--   In the simplest cases these should guaranteed cover the same area;
--   for non-flat manifolds it only works in a heuristic sense.
shadesMerge :: ∀ x . (WithField ℝ Manifold x, SimpleSpace (Needle x))
                 => ℝ -- ^ How near (inverse normalised distance, relative to shade expanse)
                      --   two shades must be to be merged. If this is zero, any shades
                      --   in the same connected region of a manifold are merged.
                 -> [Shade x] -- ^ A list of /n/ shades.
                 -> [Shade x] -- ^ /m/ &#x2264; /n/ shades which cover at least the same area.
shadesMerge fuzz (sh₁@(Shade c₁ e₁) : shs)
    = case extractJust (tryMerge pseudoAffineWitness dualSpaceWitness)
                 shs of
          (Just mg₁, shs') -> shadesMerge fuzz
                                $ shs'++[mg₁] -- Append to end to prevent undue weighting
                                              -- of first shade and its mergers.
          (_, shs') -> sh₁ : shadesMerge fuzz shs' 
 where tryMerge :: PseudoAffineWitness x -> DualNeedleWitness x
                         -> Shade x -> Maybe (Shade x)
       tryMerge (PseudoAffineWitness (SemimanifoldWitness BoundarylessWitness)) DualSpaceWitness
                    (Shade c₂ e₂)
           | Just v <- c₁.-~.c₂
           , [e₁',e₂'] <- dualNorm<$>[e₁, e₂] 
           , b₁ <- e₂'|$|v
           , b₂ <- e₁'|$|v
           , fuzz*b₁*b₂ <= b₁ + b₂
                  = Just $ let cc = c₂ .+~^ v ^/ 2
                               Just cv₁ = c₁.-~.cc
                               Just cv₂ = c₂.-~.cc
                           in Shade cc $ e₁ <> e₂ <> spanVariance [cv₁, cv₂]
           | otherwise  = Nothing
shadesMerge _ shs = shs

-- | Weakened version of 'intersectShade's'. What this function calculates is
--   rather the /weighted mean/ of ellipsoid regions. If you interpret the
--   shades as uncertain physical measurements with normal distribution,
--   it gives the maximum-likelyhood result for multiple measurements of the
--   same quantity.
mixShade's :: ∀ y . (WithField ℝ Manifold y, SimpleSpace (Needle y))
                 => NonEmpty (Shade' y) -> Maybe (Shade' y)
mixShade's = ms pseudoAffineWitness dualSpaceWitness
 where ms :: PseudoAffineWitness y -> DualNeedleWitness y
                  -> NonEmpty (Shade' y) -> Maybe (Shade' y)
       ms (PseudoAffineWitness (SemimanifoldWitness _)) DualSpaceWitness
                 (Shade' c₀ (Norm e₁):|shs) = sequenceA ciso >> pure mixed
        where ciso = [ci.-~.c₀ | Shade' ci shi <- shs]
              cis = [v | Just v <- ciso]
              σe = arr . sumV $ e₁ : (applyNorm . _shade'Narrowness<$>shs)
              cc = σe \$ sumV [ei $ ci | ci <- cis
                                       | Shade' _ (Norm ei) <- shs]
              mixed = Shade' (c₀+^cc) $ densifyNorm ( mconcat
                             [ Norm $ ei ^/ (1+(normSq ni $ ci^-^cc))
                             | ni@(Norm ei) <- Norm e₁ : (_shade'Narrowness<$>shs)
                             | ci <- zeroV : cis
                             ] )
              Tagged (+^) = translateP :: Tagged y (Interior y->Needle y->Interior y)
  -- cc should minimise the quadratic form
  -- β(cc) = ∑ᵢ ⟨cc−cᵢ|eᵢ|cc−cᵢ⟩
  -- = ⟨cc|e₁|cc⟩ + ∑ᵢ₌₁… ⟨cc−c₂|e₂|cc−c₂⟩
  -- = ⟨cc|e₁|cc⟩ + ∑ᵢ₌₁…( ⟨cc|eᵢ|cc⟩ − 2⋅⟨cᵢ|eᵢ|cc⟩ + ⟨cᵢ|eᵢ|cᵢ⟩ )
  -- It is thus
  -- β(cc + δ⋅v) − β cc
  -- = ⟨cc + δ⋅v|e₁|cc + δ⋅v⟩
  --     + ∑ᵢ₌₁…( ⟨cc + δ⋅v|eᵢ|cc + δ⋅v⟩ − 2⋅⟨cᵢ|eᵢ|cc + δ⋅v⟩ + ⟨cᵢ|eᵢ|cᵢ⟩ )
  --     − ⟨cc|e₁|cc⟩
  --     − ∑ᵢ₌₁…( ⟨cc|eᵢ|cc⟩ + 2⋅⟨cᵢ|eᵢ|cc⟩ − ⟨cᵢ|eᵢ|cᵢ⟩ )
  -- = ⟨cc + δ⋅v|e₁|cc + δ⋅v⟩
  --     + ∑ᵢ₌₁…( ⟨cc + δ⋅v|eᵢ|cc + δ⋅v⟩ − 2⋅⟨cᵢ|eᵢ|δ⋅v⟩ )
  --     − ⟨cc|e₁|cc⟩
  --     − ∑ᵢ₌₁…( ⟨cc|eᵢ|cc⟩ )
  -- = 2⋅⟨δ⋅v|e₁|cc⟩ + ⟨δ⋅v|e₁|δ⋅v⟩
  --     + ∑ᵢ₌₁…( 2⋅⟨δ⋅v|eᵢ|cc⟩ + ⟨δ⋅v|eᵢ|δ⋅v⟩ − 2⋅⟨cᵢ|eᵢ|δ⋅v⟩ )
  -- = 2⋅⟨δ⋅v|∑ᵢeᵢ|cc⟩ − 2⋅∑ᵢ₌₁… ⟨cᵢ|eᵢ|δ⋅v⟩ + 𝓞(δ²)
  -- This should vanish for all v, which is fulfilled by
  -- (∑ᵢeᵢ)|cc⟩ = ∑ᵢ₌₁… eᵢ|cᵢ⟩.

-- | Evaluate the shade as a quadratic form; essentially
-- @
-- minusLogOcclusion sh x = x <.>^ (sh^.shadeExpanse $ x - sh^.shadeCtr)
-- @
-- where 'shadeExpanse' gives a metric (matrix) that characterises the
-- width of the shade.
minusLogOcclusion' :: ∀ x s . ( PseudoAffine x, LinearSpace (Needle x)
                              , s ~ (Scalar (Needle x)), RealFloat' s )
              => Shade' x -> x -> s
minusLogOcclusion' (Shade' p₀ δinv)
        = occ (pseudoAffineWitness :: PseudoAffineWitness x)
              (dualSpaceWitness :: DualNeedleWitness x)
 where occ (PseudoAffineWitness (SemimanifoldWitness _)) DualSpaceWitness
           p = case toInterior p >>= (.-~.p₀) of
         (Just vd) | mSq <- normSq δinv vd
                   , mSq == mSq  -- avoid NaN
                   -> mSq
         _         -> 1/0
minusLogOcclusion :: ∀ x s . ( PseudoAffine x, SimpleSpace (Needle x)
                             , s ~ (Scalar (Needle x)), RealFloat' s )
              => Shade x -> x -> s
minusLogOcclusion (Shade p₀ δ)
        = occ (pseudoAffineWitness :: PseudoAffineWitness x)
              (dualSpaceWitness :: DualNeedleWitness x)
 where occ (PseudoAffineWitness (SemimanifoldWitness _)) DualSpaceWitness
            = \p -> case toInterior p >>= (.-~.p₀) of
         (Just vd) | mSq <- normSq δinv vd
                   , mSq == mSq  -- avoid NaN
                   -> mSq
         _         -> 1/0
        where δinv = dualNorm δ




rangeOnGeodesic :: ∀ i m . 
      ( WithField ℝ PseudoAffine m, Geodesic m, SimpleSpace (Needle m)
      , WithField ℝ IntervalLike i, SimpleSpace (Needle i) )
                     => m -> m -> Maybe (Shade i -> Shade m)
rangeOnGeodesic = case ( semimanifoldWitness :: SemimanifoldWitness i
                       , dualSpaceWitness :: DualNeedleWitness i
                       , dualSpaceWitness :: DualNeedleWitness m ) of
 (SemimanifoldWitness _, DualSpaceWitness, DualSpaceWitness) ->
  \p₀ p₁ -> geodesicBetween p₀ p₁ >>=
      \interp -> case pointsShades =<<
                       [ mapMaybe (toInterior . interp . D¹) [-(1-ε), 1-ε]
                       | ε <- [0.0001, 0.001, 0.01, 0.1] ] of
                      defaultSh:_ -> Just $
                       \(Shade t₀ et) -> case pointsShades
                         . mapMaybe (toInterior
                               . interp . (toClosedInterval :: i -> D¹))
                         $ fromInterior <$> t₀ : [ t₀+^v
                                                 | v<-normSpanningSystem et ] of
                       [sh] -> sh
                       _ -> defaultSh
                      _ -> Nothing
 where Tagged (+^) = translateP :: Tagged i (Interior i->Needle i->Interior i)


rangeWithinVertices :: ∀ s i m t
        . ( RealFrac' s
          , WithField s PseudoAffine i, WithField s PseudoAffine m
          , Geodesic i, Geodesic m
          , SimpleSpace (Needle i), SimpleSpace (Needle m)
          , AffineManifold (Interior i), AffineManifold (Interior m)
          , Object (Affine s) (Interior i), Object (Affine s) (Interior m)
          , Hask.Traversable t )
          => (Interior i,Interior m) -> t (i,m) -> Maybe (Shade i -> Shade m)
rangeWithinVertices
      = case ( semimanifoldWitness :: SemimanifoldWitness i
             , semimanifoldWitness :: SemimanifoldWitness m ) of
  (SemimanifoldWitness BoundarylessWitness, SemimanifoldWitness BoundarylessWitness)
      -> \(cii,cmi) verts ->
       let ci = fromInterior cii
           cm = fromInterior cmi
       in do
           vs <- sequenceA [ fzip ( middleBetween pi ci >>= (.-~.ci)
                                  , middleBetween pm cm >>= (.-~.cm) )
                           | (pi, pm) <- Hask.toList verts ]
           affinSys <- (correspondingDirections (cii,cmi) vs
                                 :: Maybe (Embedding (Affine (Scalar (Needle i)))
                                                     (Interior i) (Interior m)))
           return $ embedShade affinSys
          




data DebugView x where
  DebugView :: ( Show x, Show (Needle x+>Needle' x), LinearShowable (Needle x)
               , Needle' x ~ Needle x ) => DebugView x

-- | Class of manifolds which can use 'Shade'' as a basic set type.
--   This is easily possible for vector spaces with the default implementations.
class (WithField ℝ PseudoAffine y, SimpleSpace (Needle y)) => Refinable y where
  debugView :: Maybe (DebugView y)
  default debugView :: ( Show y, Show (Needle y+>Needle' y)
                       , Needle' y~Needle y, LinearShowable (Needle y) )
                         => Maybe (DebugView y)
  debugView = Just DebugView
  
  -- | @a `subShade'` b ≡ True@ means @a@ is fully contained in @b@, i.e. from
  --   @'minusLogOcclusion'' a p < 1@ follows also @minusLogOcclusion' b p < 1@.
  subShade' :: Shade' y -> Shade' y -> Bool
  subShade' (Shade' ac ae) (Shade' tc te)
        = case pseudoAffineWitness :: PseudoAffineWitness y of
   PseudoAffineWitness (SemimanifoldWitness BoundarylessWitness)
    | Just v <- tc.-~.ac
    , v² <- normSq te v
    , v² <= 1
     -> all (\(y',μ) -> case μ of
            Nothing -> True  -- 'te' has infinite extension in this direction
            Just ξ
              | ξ<1 -> False -- 'ae' would be vaster than 'te' in this direction
              | ω <- abs $ y'<.>^v
                    -> (ω + 1/ξ)^2 <= 1 - v² + ω^2
                 -- See @images/constructions/subellipse-check-heuristic.svg@
         ) $ sharedSeminormSpanningSystem te ae
   _ -> False
  
  -- | Intersection between two shades.
  refineShade' :: Shade' y -> Shade' y -> Maybe (Shade' y)
  refineShade' (Shade' c₀ (Norm e₁)) (Shade' c₀₂ (Norm e₂))
      = case ( dualSpaceWitness :: DualNeedleWitness y
             , pseudoAffineWitness :: PseudoAffineWitness y ) of
          (DualSpaceWitness, PseudoAffineWitness (SemimanifoldWitness BoundarylessWitness))
               -> do
           c₂ <- c₀₂.-~.c₀
           let σe = arr $ e₁^+^e₂
               e₁c₂ = e₁ $ c₂
               e₂c₂ = e₂ $ c₂
               cc = σe \$ e₂c₂
               cc₂ = cc ^-^ c₂
               e₁cc = e₁ $ cc
               e₂cc = e₂ $ cc
               α = 2 + e₂c₂<.>^cc₂
           guard (α > 0)
           let ee = σe ^/ α
               c₂e₁c₂ = e₁c₂<.>^c₂
               c₂e₂c₂ = e₂c₂<.>^c₂
               c₂eec₂ = (c₂e₁c₂ + c₂e₂c₂) / α
           return $ case middle . sort
                $ quadraticEqnSol c₂e₁c₂
                                  (2 * (e₁cc<.>^c₂))
                                  (e₁cc<.>^cc - 1)
                ++quadraticEqnSol c₂e₂c₂
                                  (2 * (e₂cc<.>^c₂ - c₂e₂c₂))
                                  (e₂cc<.>^cc - 2 * (e₂c₂<.>^cc) + c₂e₂c₂ - 1) of
            [γ₁,γ₂] | abs (γ₁+γ₂) < 2 -> let
               cc' = cc ^+^ ((γ₁+γ₂)/2)*^c₂
               rγ = abs (γ₁ - γ₂) / 2
               η = if rγ * c₂eec₂ /= 0 && 1 - rγ^2 * c₂eec₂ > 0
                   then sqrt (1 - rγ^2 * c₂eec₂) / (rγ * c₂eec₂)
                   else 0
             in Shade' (c₀.+~^cc')
                       (Norm (arr ee) <> spanNorm [ee $ c₂^*η])
            _ -> Shade' (c₀.+~^cc) (Norm $ arr ee)
   where quadraticEqnSol a b c
             | a == 0, b /= 0       = [-c/b]
             | a /= 0 && disc == 0  = [- b / (2*a)]
             | a /= 0 && disc > 0   = [ (σ * sqrt disc - b) / (2*a)
                                      | σ <- [-1, 1] ]
             | otherwise            = []
          where disc = b^2 - 4*a*c
         middle (_:x:y:_) = [x,y]
         middle l = l
  -- ⟨x−c₁|e₁|x−c₁⟩ < 1  ∧  ⟨x−c₂|e₂|x−c₂⟩ < 1
  -- We search (cc,ee) such that this implies
  -- ⟨x−cc|ee|x−cc⟩ < 1.
  -- Let WLOG c₁ = 0, so
  -- ⟨x|e₁|x⟩ < 1.
  -- cc should minimise the quadratic form
  -- β(cc) = ⟨cc−c₁|e₁|cc−c₁⟩ + ⟨cc−c₂|e₂|cc−c₂⟩
  -- = ⟨cc|e₁|cc⟩ + ⟨cc−c₂|e₂|cc−c₂⟩
  -- = ⟨cc|e₁|cc⟩ + ⟨cc|e₂|cc⟩ − 2⋅⟨c₂|e₂|cc⟩ + ⟨c₂|e₂|c₂⟩
  -- It is thus
  -- β(cc + δ⋅v) − β cc
  -- = ⟨cc + δ⋅v|e₁|cc + δ⋅v⟩ + ⟨cc + δ⋅v|e₂|cc + δ⋅v⟩ − 2⋅⟨c₂|e₂|cc + δ⋅v⟩ + ⟨c₂|e₂|c₂⟩
  --     − ⟨cc|e₁|cc⟩ − ⟨cc|e₂|cc⟩ + 2⋅⟨c₂|e₂|cc⟩ − ⟨c₂|e₂|c₂⟩
  -- = ⟨cc + δ⋅v|e₁|cc + δ⋅v⟩ + ⟨cc + δ⋅v|e₂|cc + δ⋅v⟩ − 2⋅⟨c₂|e₂|δ⋅v⟩
  --     − ⟨cc|e₁|cc⟩ − ⟨cc|e₂|cc⟩
  -- = 2⋅⟨δ⋅v|e₁|cc⟩ + ⟨δ⋅v|e₁|δ⋅v⟩ + 2⋅⟨δ⋅v|e₂|cc⟩ + ⟨δ⋅v|e₂|δ⋅v⟩ − 2⋅⟨c₂|e₂|δ⋅v⟩
  -- = 2⋅δ⋅⟨v|e₁+e₂|cc⟩ − 2⋅δ⋅⟨v|e₂|c₂⟩ + 𝓞(δ²)
  -- This should vanish for all v, which is fulfilled by
  -- (e₁+e₂)|cc⟩ = e₂|c₂⟩.
  -- 
  -- If we now choose
  -- ee = (e₁+e₂) / α
  -- then
  -- ⟨x−cc|ee|x−cc⟩ ⋅ α
  --  = ⟨x−cc|ee|x⟩ ⋅ α − ⟨x−cc|ee|cc⟩ ⋅ α
  --  = ⟨x|ee|x−cc⟩ ⋅ α − ⟨x−cc|e₂|c₂⟩
  --  = ⟨x|ee|x⟩ ⋅ α − ⟨x|ee|cc⟩ ⋅ α − ⟨x−cc|e₂|c₂⟩
  --  = ⟨x|e₁+e₂|x⟩ − ⟨x|e₂|c₂⟩ − ⟨x−cc|e₂|c₂⟩
  --  = ⟨x|e₁|x⟩ + ⟨x|e₂|x⟩ − ⟨x|e₂|c₂⟩ − ⟨x−cc|e₂|c₂⟩
  --  < 1 + ⟨x|e₂|x−c₂⟩ − ⟨x−cc|e₂|c₂⟩
  --  = 1 + ⟨x−c₂|e₂|x−c₂⟩ + ⟨c₂|e₂|x−c₂⟩ − ⟨x−cc|e₂|c₂⟩
  --  < 2 + ⟨x−c₂−x+cc|e₂|c₂⟩
  --  = 2 + ⟨cc−c₂|e₂|c₂⟩
  -- Really we want
  -- ⟨x−cc|ee|x−cc⟩ ⋅ α < α
  -- So choose α = 2 + ⟨cc−c₂|e₂|c₂⟩.
  -- 
  -- The ellipsoid "cc±√ee" captures perfectly the intersection
  -- of the boundary of the shades, but it tends to significantly
  -- overshoot the interior intersection in perpendicular direction,
  -- i.e. in direction of c₂−c₁. E.g.
  -- https://github.com/leftaroundabout/manifolds/blob/bc0460b9/manifolds/images/examples/ShadeCombinations/EllipseIntersections.png
  -- 1. Really, the relevant points are those where either of the
  --    intersector badnesses becomes 1. The intersection shade should
  --    be centered between those points. We perform according corrections,
  --    but only in c₂ direction, so this can be handled efficiently
  --    as a 1D quadratic equation.
  --    Consider
  --       dⱼ c := ⟨c−cⱼ|eⱼ|c−cⱼ⟩ =! 1
  --       dⱼ (cc + γ⋅c₂)
  --           = ⟨cc+γ⋅c₂−cⱼ|eⱼ|cc+γ⋅c₂−cⱼ⟩
  --           = ⟨cc−cⱼ|eⱼ|cc−cⱼ⟩ + 2⋅γ⋅⟨c₂|eⱼ|cc−cⱼ⟩ + γ²⋅⟨c₂|eⱼ|c₂⟩
  --           =! 1
  --    So
  --    γⱼ = (- b ± √(b²−4⋅a⋅c)) / 2⋅a
  --     where a = ⟨c₂|eⱼ|c₂⟩
  --           b = 2 ⋅ (⟨c₂|eⱼ|cc⟩ − ⟨c₂|eⱼ|cⱼ⟩)
  --           c = ⟨cc|eⱼ|cc⟩ − 2⋅⟨cc|eⱼ|cⱼ⟩ + ⟨cⱼ|eⱼ|cⱼ⟩ − 1
  --    The ± sign should be chosen to get the smaller |γ| (otherwise
  --    we end up on the wrong side of the shade), i.e.
  --    γⱼ = (sgn bⱼ ⋅ √(bⱼ²−4⋅aⱼ⋅cⱼ) − bⱼ) / 2⋅aⱼ
  -- 2. Trim the result in that direction to the actual
  --    thickness of the lens-shaped intersection: we want
  --    ⟨rγ⋅c₂|ee'|rγ⋅c₂⟩ = 1
  --    for a squeezed version of ee,
  --    ee' = ee + ee|η⋅c₂⟩⟨η⋅c₂|ee
  --    ee' = ee + η² ⋅ ee|c₂⟩⟨c₂|ee
  --    ⟨rγ⋅c₂|ee'|rγ⋅c₂⟩
  --        = rγ² ⋅ (⟨c₂|ee|c₂⟩ + η² ⋅ ⟨c₂|ee|c₂⟩²)
  --        = rγ² ⋅ ⟨c₂|ee|c₂⟩ + η² ⋅ rγ² ⋅ ⟨c₂|ee|c₂⟩²
  --    η² = (1 − rγ²⋅⟨c₂|ee|c₂⟩) / (rγ² ⋅ ⟨c₂|ee|c₂⟩²)
  --    η = √(1 − rγ²⋅⟨c₂|ee|c₂⟩) / (rγ ⋅ ⟨c₂|ee|c₂⟩)
  --    With ⟨c₂|ee|c₂⟩ = (⟨c₂|e₁|c₂⟩ + ⟨c₂|e₂|c₂⟩)/α.

  
  -- | If @p@ is in @a@ (red) and @δ@ is in @b@ (green),
  --   then @p.+~^δ@ is in @convolveShade' a b@ (blue).
  -- 
--   Example: https://nbviewer.jupyter.org/github/leftaroundabout/manifolds/blob/master/test/ShadeCombinations.ipynb#shadeConvolutions
-- 
-- <<images/examples/ShadeCombinations/2Dconvolution-skewed.png>>
  convolveMetric :: Hask.Functor p => p y -> Metric y -> Metric y -> Metric y
  convolveMetric _ ey eδ = case wellDefinedNorm result of
          Just r  -> r
          Nothing -> case debugView :: Maybe (DebugView y) of
            Just DebugView -> error $ "Can not convolve norms "
                               ++show (arr (applyNorm ey) :: Needle y+>Needle' y)
                               ++" and "++show (arr (applyNorm eδ) :: Needle y+>Needle' y)
   where eδsp = sharedSeminormSpanningSystem ey eδ
         result = spanNorm [ f ^* ζ crl | (f,crl) <- eδsp ]
         ζ = case filter (>0) . catMaybes $ snd<$>eδsp of
            [] -> const 0
            nzrelap
               -> let cre₁ = 1/minimum nzrelap
                      cre₂ =  maximum nzrelap
                      edgeFactor = sqrt ( (1 + cre₁)^2 + (1 + cre₂)^2 )
                                / (sqrt (1 + cre₁^2) + sqrt (1 + cre₂^2))
                  in \case
                        Nothing -> 0
                        Just 0  -> 0
                        Just sq -> edgeFactor / (recip sq + 1)
  
  convolveShade' :: Shade' y -> Shade' (Needle y) -> Shade' y
  convolveShade' = defaultConvolveShade'
  
defaultConvolveShade' :: ∀ y . Refinable y => Shade' y -> Shade' (Needle y) -> Shade' y
defaultConvolveShade' = case (pseudoAffineWitness :: PseudoAffineWitness y) of
  PseudoAffineWitness (SemimanifoldWitness BoundarylessWitness)
    -> \(Shade' y₀ ey) (Shade' δ₀ eδ) -> Shade' (y₀.+~^δ₀)
                                          $ convolveMetric ([]::[y]) ey eδ

instance Refinable ℝ where
  refineShade' (Shade' cl el) (Shade' cr er)
         = case (normSq el 1, normSq er 1) of
             (0, _) -> return $ Shade' cr er
             (_, 0) -> return $ Shade' cl el
             (ql,qr) | ql>0, qr>0
                    -> let [rl,rr] = sqrt . recip <$> [ql,qr]
                           b = maximum $ zipWith (-) [cl,cr] [rl,rr]
                           t = minimum $ zipWith (+) [cl,cr] [rl,rr]
                       in guard (b<t) >>
                           let cm = (b+t)/2
                               rm = (t-b)/2
                           in return $ Shade' cm (spanNorm [recip rm])
--   convolveShade' (Shade' y₀ ey) (Shade' δ₀ eδ)
--          = case (metricSq ey 1, metricSq eδ 1) of
--              (wy,wδ) | wy>0, wδ>0
--                  -> Shade' (y₀.+~^δ₀)
--                            ( projector . recip
--                                   $ recip (sqrt wy) + recip (sqrt wδ) )
--              (_ , _) -> Shade' y₀ zeroV

instance ∀ a b . ( Refinable a, Refinable b
                 , Scalar (DualVector (DualVector (Needle b)))
                      ~ Scalar (DualVector (DualVector (Needle a))) )
    => Refinable (a,b) where
  debugView = case ( debugView :: Maybe (DebugView a)
                   , debugView :: Maybe (DebugView b)
                   , dualSpaceWitness :: DualSpaceWitness (Needle a)
                   , dualSpaceWitness :: DualSpaceWitness (Needle b) ) of
      (Just DebugView, Just DebugView, DualSpaceWitness, DualSpaceWitness)
              -> Just DebugView
  
instance Refinable ℝ⁰
instance Refinable ℝ¹
instance Refinable ℝ²
instance Refinable ℝ³
instance Refinable ℝ⁴
                            
instance ( SimpleSpace a, SimpleSpace b
         , Refinable a, Refinable b
         , Scalar a ~ ℝ, Scalar b ~ ℝ
         , Scalar (DualVector a) ~ ℝ, Scalar (DualVector b) ~ ℝ
         , Scalar (DualVector (DualVector a)) ~ ℝ, Scalar (DualVector (DualVector b)) ~ ℝ )
            => Refinable (LinearMap ℝ a b) where
  debugView = Nothing

intersectShade's :: ∀ y . Refinable y => NonEmpty (Shade' y) -> Maybe (Shade' y)
intersectShade's (sh:|shs) = Hask.foldrM refineShade' sh shs


estimateLocalJacobian :: ∀ x y . ( WithField ℝ Manifold x, Refinable y
                                 , SimpleSpace (Needle x), SimpleSpace (Needle y) )
            => Metric x -> [(Local x, Shade' y)]
                             -> Maybe (Shade' (LocalLinear x y))
estimateLocalJacobian = elj ( pseudoAffineWitness :: PseudoAffineWitness x
                            , pseudoAffineWitness :: PseudoAffineWitness y )
 where elj ( PseudoAffineWitness (SemimanifoldWitness BoundarylessWitness)
           , PseudoAffineWitness (SemimanifoldWitness BoundarylessWitness) )
        mex [(Local x₁, Shade' y₁ ey₁),(Local x₀, Shade' y₀ ey₀)]
         = return $ Shade' (dx-+|>δy)
                          (Norm . LinearFunction $ \δj -> δx ⊗ (σey<$|δj $ δx))
        where Just δx = x₁.-~.x₀
              δx' = (mex<$|δx)
              dx = δx'^/(δx'<.>^δx)
              Just δy = y₁.-~.y₀
              σey = convolveMetric ([]::[y]) ey₀ ey₁
       elj _ mex (po:ps)
           | DualSpaceWitness <- dualSpaceWitness :: DualNeedleWitness y
           , length ps > 1
               = mixShade's =<< (:|) <$> estimateLocalJacobian mex ps 
                             <*> sequenceA [estimateLocalJacobian mex [po,pi] | pi<-ps]
       elj _ _ _ = return $ Shade' zeroV mempty



data QuadraticModel x y = QuadraticModel {
         _quadraticModelOffset :: Interior y
       , _quadraticModel :: Quadratic (Scalar (Needle x)) (Needle x) (Needle y)
       , _quadraticModelDeviations :: Metric y
       }

estimateLocalHessian :: ∀ x y . ( WithField ℝ Manifold x, Refinable y
                                , AffineManifold (Needle x), AffineManifold (Needle y)
                                , Geodesic (Needle x), Geodesic (Needle y)
                                , SimpleSpace (Needle x), SimpleSpace (Needle y) )
            => NonEmpty (Local x, Shade' y) -> QuadraticModel x y
estimateLocalHessian pts = elj ( pseudoAffineWitness :: PseudoAffineWitness x
                               , pseudoAffineWitness :: PseudoAffineWitness y )
 where elj ( PseudoAffineWitness (SemimanifoldWitness BoundarylessWitness)
           , PseudoAffineWitness (SemimanifoldWitness BoundarylessWitness) )
         = QuadraticModel bcy theModel (dualNorm' theDev)
        where localPts :: NonEmpty (Needle x, Shade' (Needle y))
              localPts = pts >>= \(Local x, Shade' y ey)
                             -> case y.-~.bcy of
                                 Just vy -> pure (x, Shade' vy ey)
              modelDeviations :: [(Needle x, Needle y)]
              modelDeviations = NE.toList localPts >>= \(vx, Shade' vy ey)
                             -> let (ym, _) = evalQuadratic theModel vx
                                in [ (vx, ym^-^vy^+^σ*^δy)
                                   | δy <- normSpanningSystem' ey
                                   , σ <- [-1, 1] ]
              theModel = quadratic_linearRegression mey $ second _shade'Ctr<$>localPts
              Shade _ theDev = coverAllAround zeroV $ snd <$> modelDeviations
                                 :: Shade (Needle y)
              bcy :: Interior y
              -- bcy = pointsBarycenter $ _shade'Ctr . snd <$> pts
              mey :: Metric y
              [Shade' bcy mey] = pointsShade's $ _shade'Ctr . snd <$> NE.toList pts
                                   :: [Shade' y]

evalQuadraticModel :: ∀ x y . ( PseudoAffine x, AffineManifold (Needle x)
                              , PseudoAffine y, SimpleSpace (Needle y)
                              , Scalar (Needle x) ~ Scalar (Needle y) )
          => QuadraticModel x y -> Needle x -> Shade' y
evalQuadraticModel = case ( pseudoAffineWitness :: PseudoAffineWitness x
                          , pseudoAffineWitness :: PseudoAffineWitness y ) of
   ( PseudoAffineWitness (SemimanifoldWitness _)
    ,PseudoAffineWitness (SemimanifoldWitness BoundarylessWitness) )
       -> \(QuadraticModel oy m ey) vx
        -> case evalQuadratic m vx of (vy,_) -> Shade' (oy.+~^vy) ey


propagateDEqnSolution_loc :: ∀ x y ð . ( WithField ℝ Manifold x
                                       , Refinable y, Geodesic (Interior y)
                                       , WithField ℝ AffineManifold ð, Geodesic ð
                                       , SimpleSpace (Needle x), SimpleSpace (Needle ð) )
           => DifferentialEqn x ð y
               -> LocalDataPropPlan x (Shade' y, Shade' ð) (Shade' y)
               -> Maybe (Shade' y)
propagateDEqnSolution_loc f propPlan
                  = pdesl (dualSpaceWitness :: DualNeedleWitness x)
                          (dualSpaceWitness :: DualNeedleWitness y)
                          (boundarylessWitness :: BoundarylessWitness x)
                          (pseudoAffineWitness :: PseudoAffineWitness y)
 where pdesl DualSpaceWitness DualSpaceWitness BoundarylessWitness
             (PseudoAffineWitness (SemimanifoldWitness BoundarylessWitness))
          | Nothing <- jacobian  = Nothing
          | otherwise            = pure result
         where jacobian = f shxy ^. predictDerivatives $ shð
               Just (Shade' j₀ jExpa) = jacobian

               mx = propPlan^.sourcePosition .+~^ propPlan^.targetPosOffset ^/ 2 :: x
               Just shð = middleBetween (propPlan^.sourceData._2)
                                        (propPlan^.targetAPrioriData._2)
               shxy = coverAllAround (mx, mυ)
                                     [ (δx ^-^ propPlan^.targetPosOffset ^/ 2, pυ ^+^ v)
                                     | (δx,neυ) <- (zeroV, propPlan^.sourceData._1)
                                                  : (second id
                                                      <$> propPlan^.relatedData)
                                     , let Just pυ = neυ^.shadeCtr .-~. mυ
                                     , v <- normSpanningSystem' (neυ^.shadeNarrowness)
                                     ]
                where Just mυ = middleBetween (propPlan^.sourceData._1.shadeCtr)
                                              (propPlan^.targetAPrioriData._1.shadeCtr)
               (Shade _ expax' :: Shade x)
                    = coverAllAround (propPlan^.sourcePosition)
                                     [δx | (δx,_) <- propPlan^.relatedData]
               expax = dualNorm expax'
               result :: Shade' y
               Just result = wellDefinedShade' $ convolveShade'
                        (case wellDefinedShade' $ propPlan^.sourceData._1 of {Just s->s})
                        (case wellDefinedShade' $ Shade' δyb $ applyLinMapNorm jExpa dx
                           of {Just s->s})
                where δyb = j₀ $ δx
               δx = propPlan^.targetPosOffset
               dx = δx'^/(δx'<.>^δx)
                where δx' = expax<$|δx

applyLinMapNorm :: ∀ x y . (LSpace x, LSpace y, Scalar x ~ Scalar y)
           => Norm (x+>y) -> DualVector x -> Norm y
applyLinMapNorm = case dualSpaceWitness :: DualSpaceWitness y of
  DualSpaceWitness -> \n dx -> transformNorm (arr $ LinearFunction (dx-+|>)) n

ignoreDirectionalDependence :: ∀ x y . (LSpace x, LSpace y, Scalar x ~ Scalar y)
           => (x, DualVector x) -> Norm (x+>y) -> Norm (x+>y)
ignoreDirectionalDependence = case dualSpaceWitness :: DualSpaceWitness y of
  DualSpaceWitness -> \(v,v') -> transformNorm . arr . LinearFunction $
         \j -> j . arr (LinearFunction $ \x -> x ^-^ v^*(v'<.>^x))








-- | Essentially the same as @(x,y)@, but not considered as a product topology.
--   The 'Semimanifold' etc. instances just copy the topology of @x@, ignoring @y@.
data x`WithAny`y
      = WithAny { _untopological :: y
                , _topological :: !x  }
 deriving (Hask.Functor, Show, Generic)

instance (NFData x, NFData y) => NFData (WithAny x y)

instance ∀ x y . (Semimanifold x) => Semimanifold (x`WithAny`y) where
  type Needle (WithAny x y) = Needle x
  type Interior (WithAny x y) = Interior x `WithAny` y
  WithAny y x .+~^ δx = WithAny y $ x.+~^δx
  fromInterior (WithAny y x) = WithAny y $ fromInterior x
  toInterior (WithAny y x) = fmap (WithAny y) $ toInterior x
  translateP = tpWD
   where tpWD :: ∀ x y . Semimanifold x => Tagged (WithAny x y)
                            (Interior x`WithAny`y -> Needle x -> Interior x`WithAny`y)
         tpWD = Tagged `id` \(WithAny y x) δx -> WithAny y $ tpx x δx
          where Tagged tpx = translateP :: Tagged x (Interior x -> Needle x -> Interior x)
  semimanifoldWitness = case semimanifoldWitness :: SemimanifoldWitness x of
      SemimanifoldWitness BoundarylessWitness -> SemimanifoldWitness BoundarylessWitness
            
instance (PseudoAffine x) => PseudoAffine (x`WithAny`y) where
  WithAny _ x .-~. WithAny _ ξ = x.-~.ξ
  pseudoAffineWitness = case pseudoAffineWitness :: PseudoAffineWitness x of
      PseudoAffineWitness (SemimanifoldWitness BoundarylessWitness)
       -> PseudoAffineWitness (SemimanifoldWitness BoundarylessWitness)

instance (AffineSpace x) => AffineSpace (x`WithAny`y) where
  type Diff (WithAny x y) = Diff x
  WithAny _ x .-. WithAny _ ξ = x.-.ξ
  WithAny y x .+^ δx = WithAny y $ x.+^δx 

instance (VectorSpace x, Monoid y) => VectorSpace (x`WithAny`y) where
  type Scalar (WithAny x y) = Scalar x
  μ *^ WithAny y x = WithAny y $ μ*^x 

instance (AdditiveGroup x, Monoid y) => AdditiveGroup (x`WithAny`y) where
  zeroV = WithAny mempty zeroV
  negateV (WithAny y x) = WithAny y $ negateV x
  WithAny y x ^+^ WithAny υ ξ = WithAny (mappend y υ) (x^+^ξ)

instance (AdditiveGroup x) => Hask.Applicative (WithAny x) where
  pure x = WithAny x zeroV
  WithAny f x <*> WithAny t ξ = WithAny (f t) (x^+^ξ)
  
instance (AdditiveGroup x) => Hask.Monad (WithAny x) where
  return x = WithAny x zeroV
  WithAny y x >>= f = WithAny r $ x^+^q
   where WithAny r q = f y

shadeWithAny :: y -> Shade x -> Shade (x`WithAny`y)
shadeWithAny y (Shade x xe) = Shade (WithAny y x) xe

shadeWithoutAnything :: Shade (x`WithAny`y) -> Shade x
shadeWithoutAnything (Shade (WithAny _ b) e) = Shade b e

                      




extractJust :: (a->Maybe b) -> [a] -> (Maybe b, [a])
extractJust f [] = (Nothing,[])
extractJust f (x:xs) | Just r <- f x  = (Just r, xs)
                     | otherwise      = second (x:) $ extractJust f xs


prettyShowShade' :: LtdErrorShow x => Shade' x -> String
prettyShowShade' sh = prettyShowsPrecShade' 0 sh []



wellDefinedShade' :: LinearSpace (Needle x) => Shade' x -> Maybe (Shade' x)
wellDefinedShade' (Shade' c e) = Shade' c <$> wellDefinedNorm e



data LtdErrorShowWitness m where
   LtdErrorShowWitness :: (LtdErrorShow (Interior m), LtdErrorShow (Needle m))
                  => PseudoAffineWitness m -> LtdErrorShowWitness m

class Refinable m => LtdErrorShow m where
  ltdErrorShowWitness :: LtdErrorShowWitness m
  default ltdErrorShowWitness :: (LtdErrorShow (Interior m), LtdErrorShow (Needle m))
                         => LtdErrorShowWitness m
  ltdErrorShowWitness = LtdErrorShowWitness pseudoAffineWitness
  showsPrecShade'_errorLtdC :: Int -> Shade' m -> ShowS
  prettyShowsPrecShade' :: Int -> Shade' m -> ShowS
  prettyShowsPrecShade' p sh@(Shade' c e)
              = showParen (p>6) $ v
                   . ("|±|["++) . flip (foldr id) (intersperse (',':) u) . (']':)
   where v = showsPrecShade'_errorLtdC 6 sh
         u :: [ShowS] = case ltdErrorShowWitness :: LtdErrorShowWitness m of
           LtdErrorShowWitness (PseudoAffineWitness (SemimanifoldWitness _)) ->
             [ showsPrecShade'_errorLtdC 6 (Shade' δ e :: Shade' (Needle m))
             | δ <- varianceSpanningSystem e']
         e' = dualNorm e

instance LtdErrorShow ℝ⁰ where
  showsPrecShade'_errorLtdC _ _ = ("zeroV"++)
instance LtdErrorShow ℝ where
  showsPrecShade'_errorLtdC _ (Shade' v u) = errorLtdShow (δ/2) v
   where δ = case u<$|1 of
          σ | σ>0 -> sqrt $ 1/σ
          _       -> v*10
instance LtdErrorShow ℝ² where
  showsPrecShade'_errorLtdC _ sh = ("V2 "++) . shshx . (' ':) . shshy
   where shx = projectShade (lensEmbedding _x) sh :: Shade' ℝ
         shy = projectShade (lensEmbedding _y) sh :: Shade' ℝ
         shshx = showsPrecShade'_errorLtdC 0 shx 
         shshy = showsPrecShade'_errorLtdC 0 shy 
instance LtdErrorShow ℝ³ where
  showsPrecShade'_errorLtdC _ sh = ("V3 "++) . shshx . (' ':) . shshy . (' ':) . shshz
   where shx = projectShade (lensEmbedding _x) sh :: Shade' ℝ
         shy = projectShade (lensEmbedding _y) sh :: Shade' ℝ
         shz = projectShade (lensEmbedding _z) sh :: Shade' ℝ
         shshx = showsPrecShade'_errorLtdC 0 shx 
         shshy = showsPrecShade'_errorLtdC 0 shy 
         shshz = showsPrecShade'_errorLtdC 0 shz 
instance LtdErrorShow ℝ⁴ where
  showsPrecShade'_errorLtdC _ sh
           = ("V4 "++) . shshx . (' ':) . shshy . (' ':) . shshz . (' ':) . shshw
   where shx = projectShade (lensEmbedding _x) sh :: Shade' ℝ
         shy = projectShade (lensEmbedding _y) sh :: Shade' ℝ
         shz = projectShade (lensEmbedding _z) sh :: Shade' ℝ
         shw = projectShade (lensEmbedding _w) sh :: Shade' ℝ
         shshx = showsPrecShade'_errorLtdC 0 shx 
         shshy = showsPrecShade'_errorLtdC 0 shy 
         shshz = showsPrecShade'_errorLtdC 0 shz 
         shshw = showsPrecShade'_errorLtdC 0 shw 
instance ∀ x y .
         ( LtdErrorShow x, LtdErrorShow y
         , Scalar (DualVector (Needle' x)) ~ Scalar (DualVector (Needle' y)) )
              => LtdErrorShow (x,y) where
  ltdErrorShowWitness = case ( ltdErrorShowWitness :: LtdErrorShowWitness x
                             , ltdErrorShowWitness :: LtdErrorShowWitness y ) of
   (  LtdErrorShowWitness(PseudoAffineWitness(SemimanifoldWitness BoundarylessWitness))
    , LtdErrorShowWitness(PseudoAffineWitness(SemimanifoldWitness BoundarylessWitness)) )
    ->LtdErrorShowWitness(PseudoAffineWitness(SemimanifoldWitness BoundarylessWitness))
  showsPrecShade'_errorLtdC _ sh = ('(':) . shshx . (',':) . shshy . (')':)
   where (shx,shy) = factoriseShade sh
         shshx = showsPrecShade'_errorLtdC 0 shx 
         shshy = showsPrecShade'_errorLtdC 0 shy 
                       
instance LtdErrorShow x => Show (Shade' x) where
  showsPrec = prettyShowsPrecShade'
