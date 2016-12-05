-- |
-- Module      : Data.Manifold.TreeCover
-- Copyright   : (c) Justus Sagemüller 2015
-- License     : GPL v3
-- 
-- Maintainer  : (@) sagemueller $ geo.uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE ParallelListComp           #-}
{-# LANGUAGE MonadComprehensions        #-}
{-# LANGUAGE UnicodeSyntax              #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE PatternGuards              #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE ViewPatterns               #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE CPP                        #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE LiberalTypeSynonyms        #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE TemplateHaskell            #-}


module Data.Manifold.TreeCover (
       -- * Shades 
         Shade(..), pattern(:±), Shade'(..), (|±|), IsShade
       -- ** Lenses
       , shadeCtr, shadeExpanse, shadeNarrowness
       -- ** Construction
       , fullShade, fullShade', pointsShades, pointsShade's
       , pointsCovers, pointsCover's, coverAllAround
       -- ** Evaluation
       , occlusion
       -- ** Misc
       , factoriseShade, intersectShade's, linIsoTransformShade
       , Refinable, subShade', refineShade', convolveShade', coerceShade
       , mixShade's
       -- * Shade trees
       , ShadeTree(..), fromLeafPoints, onlyLeaves, indexShadeTree, positionIndex
       -- * View helpers
       , onlyNodes
       -- ** Auxiliary types
       , SimpleTree, Trees, NonEmptyTree, GenericTree(..)
       -- * Misc
       , HasFlatView(..), shadesMerge, smoothInterpolate
       , allTwigs, twigsWithEnvirons, Twig, TwigEnviron, seekPotentialNeighbours
       , completeTopShading, flexTwigsShading, coerceShadeTree
       , WithAny(..), Shaded, fmapShaded, joinShaded
       , constShaded, zipTreeWithList, stripShadedUntopological
       , stiAsIntervalMapping, spanShading
       , estimateLocalJacobian
       , DifferentialEqn, LocalDifferentialEqn(..)
       , propagateDEqnSolution_loc, LocalDataPropPlan(..)
       , rangeOnGeodesic
       -- ** Triangulation-builders
       , TriangBuild, doTriangBuild
       , AutoTriang, breakdownAutoTriang
    ) where


import Data.List hiding (filter, all, elem, sum, foldr1)
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Vector as Arr
import Data.List.NonEmpty (NonEmpty(..))
import Data.List.FastNub
import qualified Data.List.NonEmpty as NE
import Data.Semigroup
import Data.Ord (comparing)
import Control.DeepSeq

import Data.VectorSpace
import Data.AffineSpace
import Math.LinearMap.Category
import Data.Tagged

import Data.SimplicialComplex
import Data.Manifold.Types
import Data.Manifold.Types.Primitive ((^), empty)
import Data.Manifold.PseudoAffine
import Data.Manifold.Riemannian
    
import Data.Embedding
import Data.CoNat

import Control.Lens (Lens', (^.), (.~), (%~), (&), _2, swapped)
import Control.Lens.TH

import qualified Prelude as Hask hiding(foldl, sum, sequence)
import qualified Control.Applicative as Hask
import qualified Control.Monad       as Hask hiding(forM_, sequence)
import Data.Functor.Identity
import Control.Monad.Trans.State
import Control.Monad.Trans.Writer
import Control.Monad.Trans.OuterMaybe
import Control.Monad.Trans.Class
import qualified Data.Foldable       as Hask
import Data.Foldable (all, elem, toList, sum, foldr1)
import qualified Data.Traversable as Hask
import Data.Traversable (forM)

import Control.Category.Constrained.Prelude hiding
     ((^), all, elem, sum, forM, Foldable(..), foldr1, Traversable, traverse)
import Control.Arrow.Constrained
import Control.Monad.Constrained hiding (forM)
import Data.Foldable.Constrained
import Data.Traversable.Constrained (traverse)

import GHC.Generics (Generic)
import Data.Type.Coercion


-- | Possibly / Partially / asymPtotically singular metric.
data PSM x = PSM {
       psmExpanse :: !(Metric' x)
     , relevantEigenspan :: ![Needle' x]
     }
       

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
deriving instance (Show (Interior x), Show (Metric x), WithField ℝ PseudoAffine x)
                => Show (Shade' x)

data LocalDifferentialEqn x y = LocalDifferentialEqn {
      _predictDerivatives :: Option (Shade' (LocalLinear x y))
    , _rescanDerivatives :: Shade' (LocalLinear x y) -> Shade' y -> Option (Shade' y)
    }
makeLenses ''LocalDifferentialEqn

type DifferentialEqn x y = Shade (x,y) -> LocalDifferentialEqn x y

data LocalDataPropPlan x y = LocalDataPropPlan
       { _sourcePosition :: !(Interior x)
       , _targetPosOffset :: !(Needle x)
       , _sourceData, _targetAPrioriData :: !y
       , _relatedData :: [(Needle x, y)]
       }
deriving instance (Show (Interior x), Show y, Show (Needle x)) => Show (LocalDataPropPlan x y)

makeLenses ''LocalDataPropPlan

type Depth = Int
data Wall x = Wall { _wallID :: (Depth,(Int,Int))
                   , _wallAnchor :: Interior x
                   , _wallNormal :: Needle' x
                   , _wallDistance :: Scalar (Needle x)
                   }
makeLenses ''Wall


class IsShade shade where
--  type (*) shade :: *->*
  -- | Access the center of a 'Shade' or a 'Shade''.
  shadeCtr :: Lens' (shade x) (Interior x)
--  -- | Convert between 'Shade' and 'Shade' (which must be neither singular nor infinite).
--  unsafeDualShade :: WithField ℝ Manifold x => shade x -> shade* x
  -- | Check the statistical likelihood-density of a point being within a shade.
  --   This is taken as a normal distribution.
  occlusion :: ( PseudoAffine x, SimpleSpace (Needle x)
               , s ~ (Scalar (Needle x)), RealDimension s )
                => shade x -> x -> s
  factoriseShade :: ( Manifold x, SimpleSpace (Needle x)
                    , Manifold y, SimpleSpace (Needle y)
                    , Scalar (Needle x) ~ Scalar (Needle y) )
                => shade (x,y) -> (shade x, shade y)
  coerceShade :: (Manifold x, Manifold y, LocallyCoercible x y) => shade x -> shade y
  linIsoTransformShade :: ( LinearManifold x, LinearManifold y
                          , SimpleSpace x, SimpleSpace y, Scalar x ~ Scalar y )
                          => (x+>y) -> shade x -> shade y

instance IsShade Shade where
  shadeCtr f (Shade c e) = fmap (`Shade`e) $ f c
  occlusion = occ pseudoAffineWitness dualSpaceWitness
   where occ :: ∀ x s . ( PseudoAffine x, SimpleSpace (Needle x)
                        , Scalar (Needle x) ~ s, RealDimension s )
                    => PseudoAffineWitness x -> DualNeedleWitness x -> Shade x -> x -> s
         occ (PseudoAffineWitness (SemimanifoldWitness _)) DualSpaceWitness (Shade p₀ δ)
                 = \p -> case toInterior p >>= (.-~.p₀) of
           Option(Just vd) | mSq <- normSq δinv vd
                           , mSq == mSq  -- avoid NaN
                           -> exp (negate mSq)
           _               -> zeroV
          where δinv = dualNorm δ
  factoriseShade = fs dualSpaceWitness dualSpaceWitness
   where fs :: ∀ x y . ( Manifold x, SimpleSpace (Needle x)
                       , Manifold y, SimpleSpace (Needle y)
                       , Scalar (Needle x) ~ Scalar (Needle y) )
               => DualNeedleWitness x -> DualNeedleWitness y
                       -> Shade (x,y) -> (Shade x, Shade y)
         fs DualSpaceWitness DualSpaceWitness (Shade (x₀,y₀) δxy)
                   = (Shade x₀ δx, Shade y₀ δy)
          where (δx,δy) = summandSpaceNorms δxy
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
  linIsoTransformShade = lits dualSpaceWitness dualSpaceWitness
   where lits :: ∀ x y . ( LinearManifold x, LinearManifold y
                         , Scalar (Needle x) ~ Scalar (Needle y) )
               => DualSpaceWitness x -> DualSpaceWitness y
                       -> (x+>y) -> Shade x -> Shade y
         lits DualSpaceWitness DualSpaceWitness f (Shade x δx)
                  = Shade (f $ x) (transformNorm (adjoint $ f) δx)

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
                        , Scalar (Needle x) ~ s, RealDimension s )
                    => PseudoAffineWitness x -> Shade' x -> x -> s
         occ (PseudoAffineWitness (SemimanifoldWitness _)) (Shade' p₀ δinv) p
               = case toInterior p >>= (.-~.p₀) of
           Option(Just vd) | mSq <- normSq δinv vd
                           , mSq == mSq  -- avoid NaN
                           -> exp (negate mSq)
           _               -> zeroV
  factoriseShade (Shade' (x₀,y₀) δxy) = (Shade' x₀ δx, Shade' y₀ δy)
   where (δx,δy) = summandSpaceNorms δxy
  coerceShade = cS
   where cS :: ∀ x y . (LocallyCoercible x y) => Shade' x -> Shade' y
         cS = \(Shade' x δxym) -> Shade' (internCoerce x) (tN δxym)
          where tN = case oppositeLocalCoercion :: CanonicalDiffeomorphism y x of
                      CanonicalDiffeomorphism ->
                       transformNorm . arr $ coerceNeedle ([]::[(y,x)])
                internCoerce = case interiorLocalCoercion ([]::[(x,y)]) of
                      CanonicalDiffeomorphism -> locallyTrivialDiffeomorphism
  linIsoTransformShade f (Shade' x δx)
          = Shade' (f $ x) (transformNorm (pseudoInverse f) δx)

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
   where gb :: DualNeedleWitness x -> Shade x -> Shade x -> Option (D¹ -> Shade x)
         gb DualSpaceWitness (Shade c (Norm e)) (Shade ζ (Norm η)) = pure interp
          where interp t@(D¹ q) = Shade (pinterp t)
                                 (Norm . arr . lerp ed ηd $ (q+1)/2)
                ed@(LinearMap _) = arr e
                ηd@(LinearMap _) = arr η
                Option (Just pinterp) = geodesicBetween c ζ

instance (AffineManifold x) => Semimanifold (Shade' x) where
  type Needle (Shade' x) = Diff x
  fromInterior = id
  toInterior = pure
  translateP = Tagged (.+~^)
  Shade' c e .+~^ v = Shade' (c.+^v) e
  Shade' c e .-~^ v = Shade' (c.-^v) e

instance (WithField ℝ AffineManifold x, Geodesic x, SimpleSpace (Needle x))
            => Geodesic (Shade' x) where
  geodesicBetween (Shade' c e) (Shade' ζ η) = pure interp
   where sharedSpan = sharedNormSpanningSystem e η
         interp t = Shade' (pinterp t)
                           (spanNorm [ v ^/ (alerpB 1 (recip qη) t)
                                     | (v,qη) <- sharedSpan ])
         Option (Just pinterp) = geodesicBetween c ζ

fullShade :: WithField ℝ PseudoAffine x => Interior x -> Metric' x -> Shade x
fullShade ctr expa = Shade ctr expa

fullShade' :: WithField ℝ PseudoAffine x => Interior x -> Metric x -> Shade' x
fullShade' ctr expa = Shade' ctr expa


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
(|±|) :: WithField ℝ EuclidSpace x => x -> [Needle x] -> Shade' x
x |±| shs = Shade' x $ spanNorm [v^/(v<.>v) | v<-shs]



subshadeId' :: ∀ x . (WithField ℝ PseudoAffine x, LinearSpace (Needle x))
                   => x -> NonEmpty (Needle' x) -> x -> (Int, HourglassBulb)
subshadeId' c expvs x = case ( dualSpaceWitness :: DualNeedleWitness x
                             , x .-~. c ) of
    (DualSpaceWitness, Option (Just v))
                    -> let (iu,vl) = maximumBy (comparing $ abs . snd)
                                      $ zip [0..] (map (v <.>^) $ NE.toList expvs)
                       in (iu, if vl>0 then UpperBulb else LowerBulb)
    _ -> (-1, error "Trying to obtain the subshadeId of a point not actually included in the shade.")

subshadeId :: ( WithField ℝ PseudoAffine x, LinearSpace (Needle x)
              , FiniteDimensional (Needle' x) )
                    => Shade x -> x -> (Int, HourglassBulb)
subshadeId (Shade c expa) = subshadeId' (fromInterior c)
                              . NE.fromList $ normSpanningSystem' expa
                 


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
                                                        , let Option (Just v)
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
                                      (Option (Just δ), Option (Just acci))
                                        -> (acci .+~^ δ^/i, (p:rb, nr))
                                      _ -> (acc, (rb, p:nr)) )
                             (p₀, mempty)
                             ( zip [1..] $ p₀:psr )

pointsShades' :: ∀ x . (WithField ℝ PseudoAffine x, SimpleSpace (Needle x))
                                => Metric' x -> [x] -> [([x], Shade x)]
pointsShades' _ [] = []
pointsShades' minExt ps = case (expa, toInterior ctr) of 
                           (Option (Just e), Option (Just c))
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
           | Option (Just v) <- c₁.-~.c₂
           , [e₁',e₂'] <- dualNorm<$>[e₁, e₂] 
           , b₁ <- e₂'|$|v
           , b₂ <- e₁'|$|v
           , fuzz*b₁*b₂ <= b₁ + b₂
                  = Just $ let cc = c₂ .+~^ v ^/ 2
                               Option (Just cv₁) = c₁.-~.cc
                               Option (Just cv₂) = c₂.-~.cc
                           in Shade cc $ e₁ <> e₂ <> spanVariance [cv₁, cv₂]
           | otherwise  = Nothing
shadesMerge _ shs = shs

-- | Weakened version of 'intersectShade's'. What this function calculates is
--   rather the /weighted mean/ of ellipsoid regions. If you interpret the
--   shades as uncertain physical measurements with normal distribution,
--   it gives the maximum-likelyhood result for multiple measurements of the
--   same quantity.
mixShade's :: ∀ y . (WithField ℝ Manifold y, SimpleSpace (Needle y))
                 => NonEmpty (Shade' y) -> Option (Shade' y)
mixShade's = ms pseudoAffineWitness dualSpaceWitness
 where ms :: PseudoAffineWitness y -> DualNeedleWitness y
                  -> NonEmpty (Shade' y) -> Option (Shade' y)
       ms (PseudoAffineWitness (SemimanifoldWitness _)) DualSpaceWitness
                 (Shade' c₀ (Norm e₁):|shs) = sequenceA ciso >> pure mixed
        where ciso = [ci.-~.c₀ | Shade' ci shi <- shs]
              cis = [v | Option (Just v) <- ciso]
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
                              , s ~ (Scalar (Needle x)), RealDimension s )
              => Shade' x -> x -> s
minusLogOcclusion' (Shade' p₀ δinv)
        = occ (pseudoAffineWitness :: PseudoAffineWitness x)
              (dualSpaceWitness :: DualNeedleWitness x)
 where occ (PseudoAffineWitness (SemimanifoldWitness _)) DualSpaceWitness
           p = case toInterior p >>= (.-~.p₀) of
         Option(Just vd) | mSq <- normSq δinv vd
                         , mSq == mSq  -- avoid NaN
                         -> mSq
         _               -> 1/0
minusLogOcclusion :: ∀ x s . ( PseudoAffine x, SimpleSpace (Needle x)
                             , s ~ (Scalar (Needle x)), RealDimension s )
              => Shade x -> x -> s
minusLogOcclusion (Shade p₀ δ)
        = occ (pseudoAffineWitness :: PseudoAffineWitness x)
              (dualSpaceWitness :: DualNeedleWitness x)
 where occ (PseudoAffineWitness (SemimanifoldWitness _)) DualSpaceWitness
            = \p -> case toInterior p >>= (.-~.p₀) of
         Option(Just vd) | mSq <- normSq δinv vd
                         , mSq == mSq  -- avoid NaN
                         -> mSq
         _               -> 1/0
        where δinv = dualNorm δ




rangeOnGeodesic :: ∀ i m . 
      ( WithField ℝ PseudoAffine m, Geodesic m, SimpleSpace (Needle m)
      , WithField ℝ IntervalLike i, SimpleSpace (Needle i) )
                     => m -> m -> Option (Shade i -> Shade m)
rangeOnGeodesic = case ( semimanifoldWitness :: SemimanifoldWitness i
                       , dualSpaceWitness :: DualNeedleWitness i
                       , dualSpaceWitness :: DualNeedleWitness m ) of
 (SemimanifoldWitness _, DualSpaceWitness, DualSpaceWitness) ->
  \p₀ p₁ -> (`fmap`(geodesicBetween p₀ p₁))
    $ \interp -> \(Shade t₀ et)
                -> case pointsShades
                         . mapMaybe (getOption . toInterior
                               . interp . (toClosedInterval :: i -> D¹))
                         $ fromInterior <$> t₀ : [ t₀+^v
                                                 | v<-normSpanningSystem et ] of
             [sh] -> sh
             _ -> case pointsShades $ mapMaybe (getOption . toInterior . interp . D¹)
                        [-0.999, 0.999] of
                [sh] -> sh
 where Tagged (+^) = translateP :: Tagged i (Interior i->Needle i->Interior i)




-- | Hourglass as the geometric shape (two opposing ~conical volumes, sharing
--   only a single point in the middle); has nothing to do with time.
data Hourglass s = Hourglass { upperBulb, lowerBulb :: !s }
            deriving (Generic, Hask.Functor, Hask.Foldable, Show)
instance (NFData s) => NFData (Hourglass s)
instance (Semigroup s) => Semigroup (Hourglass s) where
  Hourglass u l <> Hourglass u' l' = Hourglass (u<>u') (l<>l')
  sconcat hgs = let (us,ls) = NE.unzip $ (upperBulb&&&lowerBulb) <$> hgs
                in Hourglass (sconcat us) (sconcat ls)
instance (Monoid s, Semigroup s) => Monoid (Hourglass s) where
  mempty = Hourglass mempty mempty; mappend = (<>)
  mconcat hgs = let (us,ls) = unzip $ (upperBulb&&&lowerBulb) <$> hgs
                in Hourglass (mconcat us) (mconcat ls)
instance Hask.Applicative Hourglass where
  pure x = Hourglass x x
  Hourglass f g <*> Hourglass x y = Hourglass (f x) (g y)
instance Foldable Hourglass (->) (->) where
  ffoldl f (x, Hourglass a b) = f (f(x,a), b)
  foldMap f (Hourglass a b) = f a `mappend` f b

flipHour :: Hourglass s -> Hourglass s
flipHour (Hourglass u l) = Hourglass l u

data HourglassBulb = UpperBulb | LowerBulb
oneBulb :: HourglassBulb -> (a->a) -> Hourglass a->Hourglass a
oneBulb UpperBulb f (Hourglass u l) = Hourglass (f u) l
oneBulb LowerBulb f (Hourglass u l) = Hourglass u (f l)



data ShadeTree x = PlainLeaves [x]
                 | DisjointBranches !Int (NonEmpty (ShadeTree x))
                 | OverlappingBranches !Int !(Shade x) (NonEmpty (DBranch x))
  deriving (Generic)
deriving instance ( WithField ℝ PseudoAffine x, Show x
                  , Show (Interior x), Show (Needle' x), Show (Metric' x) )
             => Show (ShadeTree x)
           
data DBranch' x c = DBranch { boughDirection :: !(Needle' x)
                            , boughContents :: !(Hourglass c) }
  deriving (Generic, Hask.Functor, Hask.Foldable)
type DBranch x = DBranch' x (ShadeTree x)
deriving instance ( WithField ℝ PseudoAffine x, Show (Needle' x), Show c )
             => Show (DBranch' x c)

newtype DBranches' x c = DBranches (NonEmpty (DBranch' x c))
  deriving (Generic, Hask.Functor, Hask.Foldable)
deriving instance ( WithField ℝ PseudoAffine x, Show (Needle' x), Show c )
             => Show (DBranches' x c)

-- ^ /Unsafe/: this assumes the direction information of both containers to be equivalent.
instance (Semigroup c) => Semigroup (DBranches' x c) where
  DBranches b1 <> DBranches b2 = DBranches $ NE.zipWith (\(DBranch d1 c1) (DBranch _ c2)
                                                              -> DBranch d1 $ c1<>c2 ) b1 b2

  
directionChoices :: WithField ℝ Manifold x
               => [DBranch x]
                 -> [ ( (Needle' x, ShadeTree x)
                      ,[(Needle' x, ShadeTree x)] ) ]
directionChoices = map (snd *** map snd) . directionIChoices 0

directionIChoices :: (WithField ℝ PseudoAffine x, AdditiveGroup (Needle' x))
               => Int -> [DBranch x]
                 -> [ ( (Int, (Needle' x, ShadeTree x))
                      ,[(Int, (Needle' x, ShadeTree x))] ) ]
directionIChoices _ [] = []
directionIChoices i₀ (DBranch ѧ (Hourglass t b) : hs)
         =  ( top, bot : map fst uds )
          : ( bot, top : map fst uds )
          : map (second $ (top:) . (bot:)) uds
 where top = (i₀,(ѧ,t))
       bot = (i₀+1,(negateV ѧ,b))
       uds = directionIChoices (i₀+2) hs

traverseDirectionChoices :: ( WithField ℝ PseudoAffine x, LSpace (Needle x)
                            , Hask.Applicative f )
               => (    (Int, (Needle' x, ShadeTree x))
                    -> [(Int, (Needle' x, ShadeTree x))]
                    -> f (ShadeTree x) )
                 -> [DBranch x]
                 -> f [DBranch x]
traverseDirectionChoices f dbs
           = td [] . scanLeafNums 0
               $ dbs >>= \(DBranch ѧ (Hourglass τ β))
                              -> [(ѧ,τ), (negateV ѧ,β)]
 where td pds (ѧt@(_,(ѧ,_)):vb:vds)
         = liftA3 (\t' b' -> (DBranch ѧ (Hourglass t' b') :))
             (f ѧt $ vb:uds)
             (f vb $ ѧt:uds)
             $ td (ѧt:vb:pds) vds
        where uds = pds ++ vds
       td _ _ = pure []
       scanLeafNums _ [] = []
       scanLeafNums i₀ ((v,t):vts) = (i₀, (v,t)) : scanLeafNums (i₀ + nLeaves t) vts


indexDBranches :: NonEmpty (DBranch x) -> NonEmpty (DBranch' x (Int, ShadeTree x))
indexDBranches (DBranch d (Hourglass t b) :| l) -- this could more concisely be written as a traversal
              = DBranch d (Hourglass (0,t) (nt,b)) :| ixDBs (nt + nb) l
 where nt = nLeaves t; nb = nLeaves b
       ixDBs _ [] = []
       ixDBs i₀ (DBranch δ (Hourglass τ β) : l)
               = DBranch δ (Hourglass (i₀,τ) (i₀+nτ,β)) : ixDBs (i₀ + nτ + nβ) l
        where nτ = nLeaves τ; nβ = nLeaves β

instance (NFData x, NFData (Needle' x)) => NFData (ShadeTree x) where
  rnf (PlainLeaves xs) = rnf xs
  rnf (DisjointBranches n bs) = n `seq` rnf (NE.toList bs)
  rnf (OverlappingBranches n sh bs) = n `seq` sh `seq` rnf (NE.toList bs)
instance (NFData x, NFData (Needle' x)) => NFData (DBranch x)
  
-- | Experimental. There might be a more powerful instance possible.
instance (AffineManifold x) => Semimanifold (ShadeTree x) where
  type Needle (ShadeTree x) = Diff x
  fromInterior = id
  toInterior = pure
  translateP = Tagged (.+~^)
  PlainLeaves xs .+~^ v = PlainLeaves $ (.+^v)<$>xs 
  OverlappingBranches n sh br .+~^ v
        = OverlappingBranches n (sh.+~^v)
                $ fmap (\(DBranch d c) -> DBranch d $ (.+~^v)<$>c) br
  DisjointBranches n br .+~^ v = DisjointBranches n $ (.+~^v)<$>br

-- | WRT union.
instance (WithField ℝ Manifold x, SimpleSpace (Needle x)) => Semigroup (ShadeTree x) where
  PlainLeaves [] <> t = t
  t <> PlainLeaves [] = t
  t <> s = fromLeafPoints $ onlyLeaves t ++ onlyLeaves s
           -- Could probably be done more efficiently
  sconcat = mconcat . NE.toList
instance (WithField ℝ Manifold x, SimpleSpace (Needle x)) => Monoid (ShadeTree x) where
  mempty = PlainLeaves []
  mappend = (<>)
  mconcat l = case filter ne l of
               [] -> mempty
               [t] -> t
               l' -> fromLeafPoints $ onlyLeaves =<< l'
   where ne (PlainLeaves []) = False; ne _ = True


-- | Build a quite nicely balanced tree from a cloud of points, on any real manifold.
-- 
--   Example: https://nbviewer.jupyter.org/github/leftaroundabout/manifolds/blob/master/test/Trees-and-Webs.ipynb#pseudorandomCloudTree
-- 
-- <<images/examples/simple-2d-ShadeTree.png>>
fromLeafPoints :: ∀ x. (WithField ℝ Manifold x, SimpleSpace (Needle x))
                         => [x] -> ShadeTree x
fromLeafPoints = fromLeafPoints' sShIdPartition


-- | The leaves of a shade tree are numbered. For a given index, this function
--   attempts to find the leaf with that ID, within its immediate environment.
indexShadeTree :: ∀ x . WithField ℝ Manifold x
       => ShadeTree x -> Int -> Either Int ([ShadeTree x], x)
indexShadeTree _ i
    | i<0        = Left i
indexShadeTree sh@(PlainLeaves lvs) i = case length lvs of
  n | i<n       -> Right ([sh], lvs!!i)
    | otherwise -> Left $ i-n
indexShadeTree (DisjointBranches n brs) i
    | i<n        = foldl (\case 
                             Left i' -> (`indexShadeTree`i')
                             result  -> return result
                         ) (Left i) brs
    | otherwise  = Left $ i-n
indexShadeTree sh@(OverlappingBranches n _ brs) i
    | i<n        = first (sh:) <$> foldl (\case 
                             Left i' -> (`indexShadeTree`i')
                             result  -> return result
                         ) (Left i) (toList brs>>=toList)
    | otherwise  = Left $ i-n


-- | “Inverse indexing” of a tree. This is roughly a nearest-neighbour search,
--   but not guaranteed to give the correct result unless evaluated at the
--   precise position of a tree leaf.
positionIndex :: ∀ x . (WithField ℝ Manifold x, SimpleSpace (Needle x))
       => Option (Metric x)  -- ^ For deciding (at the lowest level) what “close” means;
                             --   this is optional for any tree of depth >1.
        -> ShadeTree x       -- ^ The tree to index into
        -> x                 -- ^ Position to look up
        -> Option (Int, ([ShadeTree x], x))
                   -- ^ Index of the leaf near to the query point, the “path” of
                   --   environment trees leading down to its position (in decreasing
                   --   order of size), and actual position of the found node.
positionIndex (Option (Just m)) sh@(PlainLeaves lvs) x
        = case catMaybes [ ((i,p),) . normSq m <$> getOption (p.-~.x)
                            | (i,p) <- zip [0..] lvs] of
           [] -> empty
           l | ((i,p),_) <- minimumBy (comparing snd) l
              -> pure (i, ([sh], p))
positionIndex m (DisjointBranches _ brs) x
        = fst . foldl' (\case
                          (q@(Option (Just _)), i₀) -> const (q, i₀)
                          (_, i₀) -> \t' -> ( first (+i₀) <$> positionIndex m t' x
                                            , i₀+nLeaves t' ) )
                       (empty, 0)
              $        brs
positionIndex _ sh@(OverlappingBranches n (Shade c ce) brs) x
   | PseudoAffineWitness (SemimanifoldWitness _)
               <- pseudoAffineWitness :: PseudoAffineWitness x
   , Option (Just vx) <- toInterior x>>=(.-~.c)
        = let (_,(i₀,t')) = maximumBy (comparing fst)
                       [ (σ*ω, t')
                       | DBranch d (Hourglass t'u t'd) <- NE.toList $ indexDBranches brs
                       , let ω = d<.>^vx
                       , (t',σ) <- [(t'u, 1), (t'd, -1)] ]
          in ((+i₀) *** first (sh:))
                 <$> positionIndex (return $ dualNorm' ce) t' x
positionIndex _ _ _ = empty



fromFnGraphPoints :: ∀ x y . ( WithField ℝ Manifold x, WithField ℝ Manifold y
                             , SimpleSpace (Needle x), SimpleSpace (Needle y) )
                     => [(x,y)] -> ShadeTree (x,y)
fromFnGraphPoints = case ( dualSpaceWitness :: DualNeedleWitness x
                         , boundarylessWitness :: BoundarylessWitness x
                         , dualSpaceWitness :: DualNeedleWitness y
                         , boundarylessWitness :: BoundarylessWitness y ) of
    (DualSpaceWitness,BoundarylessWitness,DualSpaceWitness,BoundarylessWitness)
        -> fromLeafPoints' $
     \(Shade c expa) xs -> case
            [ DBranch (v, zeroV) mempty
            | v <- normSpanningSystem' (transformNorm (id&&&zeroV) expa :: Metric' x) ] of
         (b:bs) -> sShIdPartition' c xs $ b:|bs

fromLeafPoints' :: ∀ x. (WithField ℝ Manifold x, SimpleSpace (Needle x)) =>
    (Shade x -> [x] -> NonEmpty (DBranch' x [x])) -> [x] -> ShadeTree x
fromLeafPoints' sShIdPart = go boundarylessWitness mempty
 where go :: BoundarylessWitness x -> Metric' x -> [x] -> ShadeTree x
       go bw@BoundarylessWitness preShExpa
            = \xs -> case pointsShades' (scaleNorm (1/3) preShExpa) xs of
                     [] -> mempty
                     [(_,rShade)] -> let trials = sShIdPart rShade xs
                                     in case reduce rShade trials of
                                         Just redBrchs
                                           -> OverlappingBranches
                                                  (length xs) rShade
                                                  (branchProc (_shadeExpanse rShade) redBrchs)
                                         _ -> PlainLeaves xs
                     partitions -> DisjointBranches (length xs)
                                   . NE.fromList
                                    $ map (\(xs',pShade) -> go bw mempty xs') partitions
        where 
              branchProc redSh = fmap (fmap $ go bw redSh)
                                 
              reduce :: Shade x -> NonEmpty (DBranch' x [x])
                                      -> Maybe (NonEmpty (DBranch' x [x]))
              reduce sh@(Shade c _) brCandidates
                        = case findIndex deficient cards of
                            Just i | (DBranch _ reBr, o:ok)
                                             <- amputateId i (NE.toList brCandidates)
                                           -> reduce sh
                                                $ sShIdPartition' c (fold reBr) (o:|ok)
                                   | otherwise -> Nothing
                            _ -> Just brCandidates
               where (cards, maxCard) = (NE.toList &&& maximum')
                                $ fmap (fmap length . boughContents) brCandidates
                     deficient (Hourglass u l) = any (\c -> c^2 <= maxCard + 1) [u,l]
                     maximum' = maximum . NE.toList . fmap (\(Hourglass u l) -> max u l)


sShIdPartition' :: (WithField ℝ PseudoAffine x, SimpleSpace (Needle x))
        => Interior x -> [x] -> NonEmpty (DBranch' x [x])->NonEmpty (DBranch' x [x])
sShIdPartition' c xs st
           = foldr (\p -> let (i,h) = ssi p
                          in asList $ update_nth (\(DBranch d c)
                                                    -> DBranch d (oneBulb h (p:) c))
                                      i )
                   st xs
 where ssi = subshadeId' (fromInterior c) (boughDirection<$>st)
sShIdPartition :: (WithField ℝ PseudoAffine x, SimpleSpace (Needle x))
                    => Shade x -> [x] -> NonEmpty (DBranch' x [x])
sShIdPartition (Shade c expa) xs
 | b:bs <- [DBranch v mempty | v <- normSpanningSystem' expa]
    = sShIdPartition' c xs $ b:|bs
                                           

asList :: ([a]->[b]) -> NonEmpty a->NonEmpty b
asList f = NE.fromList . f . NE.toList

update_nth :: (a->a) -> Int -> [a] -> [a]
update_nth _ n l | n<0 = l
update_nth f 0 (c:r) = f c : r
update_nth f n [] = []
update_nth f n (l:r) = l : update_nth f (n-1) r


amputateId :: Int -> [a] -> (a,[a])
amputateId i l = let ([a],bs) = amputateIds [i] l in (a, bs)

deleteIds :: [Int] -> [a] -> [a]
deleteIds kids = snd . amputateIds kids

amputateIds :: [Int]     -- ^ Sorted list of non-negative indices to extract
            -> [a]       -- ^ Input list
            -> ([a],[a]) -- ^ (Extracted elements, remaining elements)
amputateIds = go 0
 where go _ _ [] = ([],[])
       go _ [] l = ([],l)
       go i (k:ks) (x:xs)
         | i==k       = first  (x:) $ go (i+1)    ks  xs
         | otherwise  = second (x:) $ go (i+1) (k:ks) xs




sortByKey :: Ord a => [(a,b)] -> [b]
sortByKey = map snd . sortBy (comparing fst)


trunks :: ∀ x. (WithField ℝ PseudoAffine x, SimpleSpace (Needle x))
                  => ShadeTree x -> [Shade x]
trunks t = case (pseudoAffineWitness :: PseudoAffineWitness x, t) of
  (PseudoAffineWitness (SemimanifoldWitness BoundarylessWitness), PlainLeaves lvs)
                                         -> pointsCovers . catOptions $ toInterior<$>lvs
  (_, DisjointBranches _ brs)            -> Hask.foldMap trunks brs
  (_, OverlappingBranches _ sh _)        -> [sh]


nLeaves :: ShadeTree x -> Int
nLeaves (PlainLeaves lvs) = length lvs
nLeaves (DisjointBranches n _) = n
nLeaves (OverlappingBranches n _ _) = n


instance ImpliesMetric ShadeTree where
  type MetricRequirement ShadeTree x = (WithField ℝ PseudoAffine x, SimpleSpace (Needle x))
  inferMetric = stInfMet
   where stInfMet :: ∀ x . (WithField ℝ PseudoAffine x, SimpleSpace (Needle x))
                                => ShadeTree x -> Metric x
         stInfMet (OverlappingBranches _ (Shade _ e) _) = dualNorm' e
         stInfMet (PlainLeaves lvs)
               = case pointsShades $ Hask.toList . toInterior =<< lvs :: [Shade x] of
             (Shade _ sh:_) -> dualNorm' sh
             _ -> mempty
         stInfMet (DisjointBranches _ (br:|_)) = inferMetric br
  inferMetric' = stInfMet
   where stInfMet :: ∀ x . (WithField ℝ PseudoAffine x, SimpleSpace (Needle x))
                                => ShadeTree x -> Metric' x
         stInfMet (OverlappingBranches _ (Shade _ e) _) = e
         stInfMet (PlainLeaves lvs)
               = case pointsShades $ Hask.toList . toInterior =<< lvs :: [Shade x] of
             (Shade _ sh:_) -> sh
             _ -> mempty
         stInfMet (DisjointBranches _ (br:|_)) = inferMetric' br



overlappingBranches :: Shade x -> NonEmpty (DBranch x) -> ShadeTree x
overlappingBranches shx brs = OverlappingBranches n shx brs
 where n = sum $ fmap (sum . fmap nLeaves) brs

unsafeFmapLeaves :: (x -> x) -> ShadeTree x -> ShadeTree x
unsafeFmapLeaves f (PlainLeaves lvs) = PlainLeaves $ fmap f lvs
unsafeFmapLeaves f (DisjointBranches n brs)
                  = DisjointBranches n $ unsafeFmapLeaves f <$> brs
unsafeFmapLeaves f (OverlappingBranches n sh brs)
                  = OverlappingBranches n sh $ fmap (unsafeFmapLeaves f) <$> brs

unsafeFmapTree :: (NonEmpty x -> NonEmpty y)
               -> (Needle' x -> Needle' y)
               -> (Shade x -> Shade y)
               -> ShadeTree x -> ShadeTree y
unsafeFmapTree _ _ _ (PlainLeaves []) = PlainLeaves []
unsafeFmapTree f _ _ (PlainLeaves lvs) = PlainLeaves . toList . f $ NE.fromList lvs
unsafeFmapTree f fn fs (DisjointBranches n brs)
    = let brs' = unsafeFmapTree f fn fs <$> brs
      in DisjointBranches (sum $ nLeaves<$>brs') brs'
unsafeFmapTree f fn fs (OverlappingBranches n sh brs)
    = let brs' = fmap (\(DBranch dir br)
                      -> DBranch (fn dir) (unsafeFmapTree f fn fs<$>br)
                      ) brs
      in overlappingBranches (fs sh) brs'

coerceShadeTree :: ∀ x y . (LocallyCoercible x y, Manifold x, Manifold y)
                       => ShadeTree x -> ShadeTree y
coerceShadeTree = case ( dualSpaceWitness :: DualNeedleWitness x
                       , dualSpaceWitness :: DualNeedleWitness y ) of
   (DualSpaceWitness,DualSpaceWitness)
      -> unsafeFmapTree (fmap locallyTrivialDiffeomorphism)
                                 (coerceNeedle' ([]::[(x,y)]) $)
                                 coerceShade


-- | Class of manifolds which can use 'Shade'' as a basic set type.
--   This is easily possible for vector spaces with the default implementations.
class (WithField ℝ PseudoAffine y, SimpleSpace (Needle y)) => Refinable y where
  -- | @a `subShade'` b ≡ True@ means @a@ is fully contained in @b@, i.e. from
  --   @'minusLogOcclusion'' a p < 1@ follows also @minusLogOcclusion' b p < 1@.
  subShade' :: Shade' y -> Shade' y -> Bool
  subShade' (Shade' ac ae) (Shade' tc te)
        = case pseudoAffineWitness :: PseudoAffineWitness y of
   PseudoAffineWitness (SemimanifoldWitness BoundarylessWitness)
    | Option (Just v) <- tc.-~.ac
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
  refineShade' :: Shade' y -> Shade' y -> Option (Shade' y)
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
  convolveMetric _ ey eδ = spanNorm [ f ^* ζ crl
                                    | (f,crl) <- eδsp ]
   where eδsp = sharedSeminormSpanningSystem ey eδ
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

instance ( Refinable a, Interior a ~ a, Refinable b, Interior b ~ b
         , Scalar (DualVector (DualVector (Needle b)))
                      ~ Scalar (DualVector (DualVector (Needle a))) )
    => Refinable (a,b)
  
instance Refinable ℝ⁰
instance Refinable ℝ¹
instance Refinable ℝ²
instance Refinable ℝ³
instance Refinable ℝ⁴
                            
instance ( SimpleSpace a, SimpleSpace b
         , Scalar a ~ ℝ, Scalar b ~ ℝ
         , Scalar (DualVector a) ~ ℝ, Scalar (DualVector b) ~ ℝ
         , Scalar (DualVector (DualVector a)) ~ ℝ, Scalar (DualVector (DualVector b)) ~ ℝ )
            => Refinable (LinearMap ℝ a b)

intersectShade's :: ∀ y . Refinable y => NonEmpty (Shade' y) -> Option (Shade' y)
intersectShade's (sh:|shs) = Hask.foldrM refineShade' sh shs


estimateLocalJacobian :: ∀ x y . ( WithField ℝ Manifold x, Refinable y
                                 , SimpleSpace (Needle x), SimpleSpace (Needle y) )
            => Metric x -> [(Local x, Shade' y)]
                             -> Option (Shade' (LocalLinear x y))
estimateLocalJacobian = elj ( pseudoAffineWitness :: PseudoAffineWitness x
                            , pseudoAffineWitness :: PseudoAffineWitness y )
 where elj ( PseudoAffineWitness (SemimanifoldWitness BoundarylessWitness)
           , PseudoAffineWitness (SemimanifoldWitness BoundarylessWitness) )
        mex [(Local x₁, Shade' y₁ ey₁),(Local x₀, Shade' y₀ ey₀)]
         = return $ Shade' (dx-+|>δy)
                          (Norm . LinearFunction $ \δj -> δx ⊗ (σey<$|δj $ δx))
        where Option (Just δx) = x₁.-~.x₀
              δx' = (mex<$|δx)
              dx = δx'^/(δx'<.>^δx)
              Option (Just δy) = y₁.-~.y₀
              σey = convolveMetric ([]::[y]) ey₀ ey₁
       elj _ mex (po:ps)
           | DualSpaceWitness <- dualSpaceWitness :: DualNeedleWitness y
           , length ps > 1
               = mixShade's =<< (:|) <$> estimateLocalJacobian mex ps 
                             <*> sequenceA [estimateLocalJacobian mex [po,pi] | pi<-ps]
       elj _ _ _ = return $ Shade' zeroV mempty



propagateDEqnSolution_loc :: ∀ x y . ( WithField ℝ Manifold x
                                     , Refinable y, Geodesic (Interior y)
                                     , SimpleSpace (Needle x) )
           => DifferentialEqn x y
               -> LocalDataPropPlan x (Shade' y)
               -> Maybe (Shade' y)
propagateDEqnSolution_loc f propPlan
                  = pdesl (dualSpaceWitness :: DualNeedleWitness x)
                          (dualSpaceWitness :: DualNeedleWitness y)
                          (boundarylessWitness :: BoundarylessWitness x)
                          (pseudoAffineWitness :: PseudoAffineWitness y)
 where pdesl DualSpaceWitness DualSpaceWitness BoundarylessWitness
             (PseudoAffineWitness (SemimanifoldWitness BoundarylessWitness))
          | Option Nothing <- jacobian  = Nothing
          | otherwise                   = pure result
         where jacobian = f shxy ^. predictDerivatives
               Option (Just (Shade' j₀ jExpa)) = jacobian

               mx = propPlan^.sourcePosition .+~^ propPlan^.targetPosOffset ^/ 2
               Option (Just my) = middleBetween (propPlan^.sourceData.shadeCtr)
                                                (propPlan^.targetAPrioriData.shadeCtr)
               shxy = coverAllAround (mx, my)
                                     [ (δx ^-^ propPlan^.targetPosOffset ^/ 2, py ^+^ v)
                                     | (δx,ney) <- (zeroV, propPlan^.sourceData)
                                                  : (propPlan^.relatedData)
                                     , let Option (Just py) = ney^.shadeCtr .-~. my
                                     , v <- normSpanningSystem' (ney^.shadeNarrowness)
                                     ]
               (Shade _ expax' :: Shade x)
                    = coverAllAround (propPlan^.sourcePosition)
                                     [δx | (δx,_) <- propPlan^.relatedData]
               expax = dualNorm expax'
               result :: Shade' y
               result = convolveShade'
                        (propPlan^.sourceData)
                        (Shade' δyb $ applyLinMapNorm jExpa dx)
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

type Twig x = (Int, ShadeTree x)
type TwigEnviron x = [Twig x]

allTwigs :: ∀ x . WithField ℝ PseudoAffine x => ShadeTree x -> [Twig x]
allTwigs tree = go 0 tree []
 where go n₀ (DisjointBranches _ dp)
         = snd (foldl' (\(n₀',prev) br -> (n₀'+nLeaves br, prev . go n₀' br)) (n₀,id) dp)
       go n₀ (OverlappingBranches _ _ dp)
         = snd (foldl' (\(n₀',prev) (DBranch _ (Hourglass top bot))
                          -> ( n₀'+nLeaves top+nLeaves bot
                             , prev . go n₀' top . go (n₀'+nLeaves top) bot) )
                        (n₀,id) $ NE.toList dp)
       go n₀ twig = ((n₀,twig):)

-- Formerly, 'twigsWithEnvirons' what has now become 'traverseTwigsWithEnvirons'.
-- The simple list-yielding version (see rev. b4a427d59ec82889bab2fde39225b14a57b694df)
-- may well be more efficient than the current traversal-derived version.

-- | Example: https://nbviewer.jupyter.org/github/leftaroundabout/manifolds/blob/master/test/Trees-and-Webs.ipynb#pseudorandomCloudTree
-- 
--   <<images/examples/TreesAndWebs/2D-scatter_twig-environs.png>>
twigsWithEnvirons :: ∀ x. (WithField ℝ Manifold x, SimpleSpace (Needle x))
    => ShadeTree x -> [(Twig x, TwigEnviron x)]
twigsWithEnvirons = execWriter . traverseTwigsWithEnvirons (writer . (snd.fst&&&pure))

traverseTwigsWithEnvirons :: ∀ x f .
            (WithField ℝ PseudoAffine x, SimpleSpace (Needle x), Hask.Applicative f)
    => ( (Twig x, TwigEnviron x) -> f (ShadeTree x) ) -> ShadeTree x -> f (ShadeTree x)
traverseTwigsWithEnvirons f = fst . go pseudoAffineWitness [] . (0,)
 where go :: PseudoAffineWitness x -> TwigEnviron x -> Twig x -> (f (ShadeTree x), Bool)
       go sw _ (i₀, DisjointBranches nlvs djbs) = ( fmap (DisjointBranches nlvs)
                                                   . Hask.traverse (fst . go sw [])
                                                   $ NE.zip ioffs djbs
                                               , False )
        where ioffs = NE.scanl (\i -> (+i) . nLeaves) i₀ djbs
       go sw@(PseudoAffineWitness (SemimanifoldWitness BoundarylessWitness)) envi
           ct@(i₀, (OverlappingBranches nlvs rob@(Shade robc _) brs))
                = ( case descentResult of
                     OuterNothing -> f
                         $ purgeRemotes
                            (ct, Hask.foldMap (\(io,te)
                                         -> first (+io) <$> twigProximæ sw robc te) envi)
                     OuterJust dR -> fmap (OverlappingBranches nlvs rob . NE.fromList) dR
                  , False )
        where descentResult = traverseDirectionChoices tdc $ NE.toList brs
              tdc (io, (vy, ty)) alts = case go sw envi'' (i₀+io, ty) of
                                   (_, True) -> OuterNothing
                                   (down, _) -> OuterJust down
               where envi'' = filter (snd >>> trunks >>> \(Shade ce _:_)
                                         -> let Option (Just δyenv) = ce.-~.robc
                                                qq = vy<.>^δyenv
                                            in qq > -1
                                       ) envi'
                              ++ map ((+i₀)***snd) alts
              envi' = approach =<< envi
              approach (i₀e, apt@(OverlappingBranches _ (Shade envc _) _))
                  = first (+i₀e) <$> twigsaveTrim hither apt
               where Option (Just δxenv) = robc .-~. envc
                     hither (DBranch bdir (Hourglass bdc₁ bdc₂))
                       =  [(0           , bdc₁) | overlap > -1]
                       ++ [(nLeaves bdc₁, bdc₂) | overlap < 1]
                      where overlap = bdir<.>^δxenv
              approach q = [q]
       go (PseudoAffineWitness (SemimanifoldWitness _)) envi plvs@(i₀, (PlainLeaves _))
                         = (f $ purgeRemotes (plvs, envi), True)
       
       twigProximæ :: PseudoAffineWitness x -> Interior x -> ShadeTree x -> TwigEnviron x
       twigProximæ sw x₀ (DisjointBranches _ djbs)
               = Hask.foldMap (\(i₀,st) -> first (+i₀) <$> twigProximæ sw x₀ st)
                    $ NE.zip ioffs djbs
        where ioffs = NE.scanl (\i -> (+i) . nLeaves) 0 djbs
       twigProximæ sw@(PseudoAffineWitness (SemimanifoldWitness _))
                          x₀ ct@(OverlappingBranches _ (Shade xb qb) brs)
                   = twigsaveTrim hither ct
        where Option (Just δxb) = x₀ .-~. xb
              hither (DBranch bdir (Hourglass bdc₁ bdc₂))
                =  ((guard (overlap > -1)) >> twigProximæ sw x₀ bdc₁)
                ++ ((guard (overlap < 1)) >> first (+nLeaves bdc₁)<$>twigProximæ sw x₀ bdc₂)
               where overlap = bdir<.>^δxb
       twigProximæ _ _ plainLeaves = [(0, plainLeaves)]
       
       twigsaveTrim :: (DBranch x -> TwigEnviron x) -> ShadeTree x -> TwigEnviron x
       twigsaveTrim f ct@(OverlappingBranches _ _ dbs)
                 = case Hask.mapM (\(i₀,dbr) -> noLeaf $ first(+i₀)<$>f dbr)
                                 $ NE.zip ioffs dbs of
                      Just pqe -> Hask.fold pqe
                      _        -> [(0,ct)]
        where noLeaf [(_,PlainLeaves _)] = empty
              noLeaf bqs = pure bqs
              ioffs = NE.scanl (\i -> (+i) . sum . fmap nLeaves . toList) 0 dbs
       
       purgeRemotes :: (Twig x, TwigEnviron x) -> (Twig x, TwigEnviron x)
       purgeRemotes = id -- See 7d1f3a4 for the implementation; this didn't work reliable. 
    
completeTopShading :: ∀ x y . ( WithField ℝ PseudoAffine x, WithField ℝ PseudoAffine y
                              , SimpleSpace (Needle x), SimpleSpace (Needle y) )
                   => x`Shaded`y -> [Shade' (x,y)]
completeTopShading (PlainLeaves plvs) = case ( dualSpaceWitness :: DualNeedleWitness x
                                             , dualSpaceWitness :: DualNeedleWitness y ) of
       (DualSpaceWitness, DualSpaceWitness)
          -> pointsShade's . catOptions
               $ toInterior . (_topological &&& _untopological) <$> plvs
completeTopShading (DisjointBranches _ bqs)
                     = take 1 . completeTopShading =<< NE.toList bqs
completeTopShading t = case ( dualSpaceWitness :: DualNeedleWitness x
                            , dualSpaceWitness :: DualNeedleWitness y ) of
       (DualSpaceWitness, DualSpaceWitness)
          -> pointsCover's . catOptions
                . map (toInterior <<< _topological &&& _untopological) $ onlyLeaves t


transferAsNormsDo :: ∀ v . LSpace v => Norm v -> Variance v -> v-+>v
transferAsNormsDo = case dualSpaceWitness :: DualSpaceWitness v of
                      DualSpaceWitness -> \(Norm m) (Norm n) -> n . m

flexTopShading :: ∀ x y f . ( WithField ℝ Manifold x, WithField ℝ Manifold y
                            , SimpleSpace (Needle x), SimpleSpace (Needle y)
                            , Applicative f (->) (->) )
                  => (Shade' (x,y) -> f (x, (Shade' y, LocalLinear x y)))
                      -> x`Shaded`y -> f (x`Shaded`y)
flexTopShading f tr = seq (assert_onlyToplevDisjoint tr)
                    $ recst (dualSpaceWitness::DualNeedleWitness x
                            ,dualSpaceWitness::DualNeedleWitness y
                            ,pseudoAffineWitness::PseudoAffineWitness y)
                            (completeTopShading tr) tr
 where recst _ qsh@(_:_) (DisjointBranches n bqs)
          = undefined -- DisjointBranches n $ NE.zipWith (recst . (:[])) (NE.fromList qsh) bqs
       recst (DualSpaceWitness,DualSpaceWitness,PseudoAffineWitness (SemimanifoldWitness _))
               [sha@(Shade' (_,yc₀) expa₀)] t = fmap fts $ f sha
        where expa'₀ = dualNorm expa₀
              j₀ :: LocalLinear x y
              j₀ = dependence expa'₀
              (_,expay₀) = summandSpaceNorms expa₀
              fts (xc, (Shade' yc expay, jtg)) = unsafeFmapLeaves applδj t
               where Option (Just δyc) = yc.-~.yc₀
                     tfm = transferAsNormsDo expay₀ (dualNorm expay)
                     applδj (WithAny y x)
                           = WithAny (yc₀ .+~^ ((tfm $ δy) ^+^ (jtg $ δx) ^+^ δyc)) x
                      where Option (Just δx) = x.-~.xc
                            Option (Just δy) = y.-~.(yc₀.+~^(j₀ $ δx))
       
       assert_onlyToplevDisjoint, assert_connected :: x`Shaded`y -> ()
       assert_onlyToplevDisjoint (DisjointBranches _ dp) = rnf (assert_connected<$>dp)
       assert_onlyToplevDisjoint t = assert_connected t
       assert_connected (OverlappingBranches _ _ dp)
           = rnf (Hask.foldMap assert_connected<$>dp)
       assert_connected (PlainLeaves _) = ()

flexTwigsShading :: ∀ x y f . ( WithField ℝ Manifold x, WithField ℝ Manifold y
                              , SimpleSpace (Needle x), SimpleSpace (Needle y)
                              , Hask.Applicative f )
                  => (Shade' (x,y) -> f (x, (Shade' y, LocalLinear x y)))
                      -> x`Shaded`y -> f (x`Shaded`y)
flexTwigsShading f = traverseTwigsWithEnvirons locFlex
 where locFlex :: ∀ μ . ((Int, x`Shaded`y), μ) -> f (x`Shaded`y)
       locFlex ((_,lsh), _) = flexTopShading f lsh
                


seekPotentialNeighbours :: ∀ x . (WithField ℝ PseudoAffine x, SimpleSpace (Needle x))
                => ShadeTree x -> x`Shaded`[Int]
seekPotentialNeighbours tree = zipTreeWithList tree
                     $ snd<$>leavesWithPotentialNeighbours tree

leavesWithPotentialNeighbours :: ∀ x . (WithField ℝ PseudoAffine x, SimpleSpace (Needle x))
                => ShadeTree x -> [(x, [Int])]
leavesWithPotentialNeighbours = map (second snd) . go pseudoAffineWitness 0 0 []
 where go :: PseudoAffineWitness x -> Depth -> Int -> [Wall x] -> ShadeTree x
                -> [(x, ([Wall x], [Int]))]
       go (PseudoAffineWitness (SemimanifoldWitness _)) depth n₀ walls (PlainLeaves lvs)
               = [ (x, ( [ wall & wallDistance .~ d
                         | wall <- walls
                         , Option (Just vw) <- [toInterior x>>=(.-~.wall^.wallAnchor)]
                         , let d = (wall^.wallNormal)<.>^vw
                         , d < wall^.wallDistance ]
                       , [] ))
                 | x <- lvs ]
       go pw depth n₀ walls (DisjointBranches _ dp)
         = snd (foldl' (\(n₀',prev) br -> ( n₀'+nLeaves br
                                          , prev . (go pw depth n₀' walls br++)))
                        (n₀,id) dp) []
       go pw@(PseudoAffineWitness (SemimanifoldWitness _))
               depth n₀ walls (OverlappingBranches _ (Shade brCtr _) dp)
         = reassemble $ snd
             (foldl' assignWalls (n₀,id) . directionIChoices 0 $ NE.toList dp) []
        where assignWalls :: (Int, DList (x, ([Wall x],[Int])))
                     -> ((Int,(Needle' x, ShadeTree x)), [(Int,(Needle' x, ShadeTree x))])
                     -> (Int, DList (x, ([Wall x], [Int])))
              assignWalls (n₀',prev) ((iDir,(thisDir,br)),otherDirs)
                    = ( n₀'+nLeaves br
                      , prev . (go pw (depth+1) n₀'
                                   (newWalls ++ (updWall<$>walls))
                                   br ++) )
               where newWalls = [ Wall (depth,(iDir,iDir'))
                                       brCtr
                                       (thisDir^-^otherDir)
                                       (1/0)
                                | (iDir',(otherDir,_)) <- otherDirs ]
                     updWall wall = wall & wallDistance %~ min bcDist
                      where Option (Just vbw) = brCtr.-~.wall^.wallAnchor
                            bcDist = (wall^.wallNormal)<.>^vbw
              reassemble :: [(x, ([Wall x],[Int]))] -> [(x, ([Wall x],[Int]))]
              reassemble pts = [ (x, (higherWalls, newGroups++deeperGroups))
                               | (x, (allWalls, deeperGroups)) <- pts
                               , let (levelWalls,higherWalls)
                                      = break ((<depth) . fst . _wallID) allWalls
                                     newGroups = concat
                                         [ Map.findWithDefault []
                                              (wall^.wallID._2.swapped) groups
                                         | wall <- levelWalls ]
                               ]
               where groups = ($[]) <$> Map.fromListWith (.)
                               [ (wall^.wallID._2, (i:))
                               | (i,(_, (gsc,_))) <- zip [n₀..] pts
                               , wall <- takeWhile ((==depth) . fst . _wallID) gsc ]






newtype BaryCoords n = BaryCoords { getBaryCoordsTail :: FreeVect n ℝ }

instance (KnownNat n) => AffineSpace (BaryCoords n) where
  type Diff (BaryCoords n) = FreeVect n ℝ
  BaryCoords v .-. BaryCoords w = v ^-^ w
  BaryCoords v .+^ w = BaryCoords $ v ^+^ w
instance (KnownNat n) => Semimanifold (BaryCoords n) where
  type Needle (BaryCoords n) = FreeVect n ℝ
  fromInterior = id
  toInterior = pure
  translateP = Tagged (.+~^)
  (.+~^) = (.+^)
  semimanifoldWitness = undefined
instance (KnownNat n) => PseudoAffine (BaryCoords n) where
  (.-~.) = pure .: (.-.)

getBaryCoords :: BaryCoords n -> ℝ ^ S n
getBaryCoords (BaryCoords (FreeVect bcs)) = FreeVect $ (1 - Arr.sum bcs) `Arr.cons` bcs
  
getBaryCoords' :: BaryCoords n -> [ℝ]
getBaryCoords' (BaryCoords (FreeVect bcs)) = 1 - Arr.sum bcs : Arr.toList bcs

getBaryCoord :: BaryCoords n -> Int -> ℝ
getBaryCoord (BaryCoords (FreeVect bcs)) 0 = 1 - Arr.sum bcs
getBaryCoord (BaryCoords (FreeVect bcs)) i = case bcs Arr.!? i of
    Just a -> a
    _      -> 0

mkBaryCoords :: KnownNat n => ℝ ^ S n -> BaryCoords n
mkBaryCoords (FreeVect bcs) = BaryCoords $ FreeVect (Arr.tail bcs) ^/ Arr.sum bcs

mkBaryCoords' :: KnownNat n => [ℝ] -> Option (BaryCoords n)
mkBaryCoords' bcs = fmap (BaryCoords . (^/sum bcs)) . freeVector . Arr.fromList $ tail bcs

newtype ISimplex n x = ISimplex { iSimplexBCCordEmbed :: Embedding (->) (BaryCoords n) x }




data TriangBuilder n x where
  TriangVerticesSt :: [x] -> TriangBuilder Z x
  TriangBuilder :: Triangulation (S n) x
                    -> [x]
                    -> [(Simplex n x, [x] -> Option x)]
                            -> TriangBuilder (S n) x



              
bottomExtendSuitability :: (KnownNat n, WithField ℝ Manifold x)
                => ISimplex (S n) x -> x -> ℝ
bottomExtendSuitability (ISimplex emb) x = case getBaryCoord (emb >-$ x) 0 of
     0 -> 0
     r -> - recip r

optimalBottomExtension :: (KnownNat n, WithField ℝ Manifold x)
                => ISimplex (S n) x -> [x] -> Option Int
optimalBottomExtension s xs
      = case filter ((>0).snd)
               $ zipWith ((. bottomExtendSuitability s) . (,)) [0..] xs of
             [] -> empty
             qs -> pure . fst . maximumBy (comparing snd) $ qs




fromISimplex :: forall x n . (KnownNat n, WithField ℝ Manifold x)
                   => ISimplex n x -> Simplex n x
fromISimplex (ISimplex emb) = s
 where (Option (Just s))
          = makeSimplex' [ emb $-> jOnly
                         | j <- [0..n]
                         , let (Option (Just jOnly)) = mkBaryCoords' [ if k==j then 1 else 0
                                                                     | k<-[0..n] ]
                         ]
       (Tagged n) = theNatN :: Tagged n Int

iSimplexSideViews :: ∀ n x . KnownNat n => ISimplex n x -> [ISimplex n x]
iSimplexSideViews = \(ISimplex is)
              -> take (n+1) $ [ISimplex $ rot j is | j<-[0..] ]
 where rot j (Embedding emb proj)
            = Embedding ( emb . mkBaryCoords . freeRotate j     . getBaryCoords        )
                        (       mkBaryCoords . freeRotate (n-j) . getBaryCoords . proj )
       (Tagged n) = theNatN :: Tagged n Int


type FullTriang t n x = TriangT t n x
          (State (Map.Map (SimplexIT t n x) (ISimplex n x)))

type TriangBuild t n x = TriangT t (S n) x
          ( State (Map.Map (SimplexIT t n x) (Metric x, ISimplex (S n) x) ))

doTriangBuild :: KnownNat n => (∀ t . TriangBuild t n x ()) -> [Simplex (S n) x]
doTriangBuild t = runIdentity (fst <$>
  doTriangT (unliftInTriangT (`evalStateT`mempty) t >> simplexITList >>= mapM lookSimplex))



hypotheticalSimplexScore :: ∀ t n n' x . (KnownNat n', WithField ℝ Manifold x, n~S n')
          => SimplexIT t Z x
           -> SimplexIT t n x
           -> TriangBuild t n x ( Option Double )
hypotheticalSimplexScore p b = do
   altViews :: [(SimplexIT t Z x, SimplexIT t n x)] <- do
      pSups <- lookSupersimplicesIT p
      nOpts <- forM pSups $ \psup -> fmap (fmap $ \((bq,_p), _b') -> (bq,psup))
                      $ distinctSimplices b psup
      return $ catOptions nOpts
   scores <- forM ((p,b) :| altViews) $ \(p',b') -> do
      x <- lookVertexIT p'
      q <- lift $ Map.lookup b' <$> get
      return $ case q of
         Just(_,is) | s<-bottomExtendSuitability is x, s>0
                 -> pure s
         _       -> empty
   return . fmap sum $ Hask.sequence scores





data AutoTriang n x where
  AutoTriang :: { getAutoTriang :: ∀ t . TriangBuild t n x () } -> AutoTriang (S n) x



breakdownAutoTriang :: ∀ n n' x . (KnownNat n', n ~ S n') => AutoTriang n x -> [Simplex n x]
breakdownAutoTriang (AutoTriang t) = doTriangBuild t
         
                    
   
   
   
       

 
partitionsOfFstLength :: Int -> [a] -> [([a],[a])]
partitionsOfFstLength 0 l = [([],l)]
partitionsOfFstLength n [] = []
partitionsOfFstLength n (x:xs) = ( first (x:) <$> partitionsOfFstLength (n-1) xs )
                              ++ ( second (x:) <$> partitionsOfFstLength n xs )

splxVertices :: Simplex n x -> [x]
splxVertices (ZS x) = [x]
splxVertices (x :<| s') = x : splxVertices s'







-- |
-- @
-- 'SimpleTree' x &#x2245; Maybe (x, 'Trees' x)
-- @
type SimpleTree = GenericTree Maybe []
-- |
-- @
-- 'Trees' x &#x2245; [(x, 'Trees' x)]
-- @
type Trees = GenericTree [] []
-- |
-- @
-- 'NonEmptyTree' x &#x2245; (x, 'Trees' x)
-- @
type NonEmptyTree = GenericTree NonEmpty []
    
newtype GenericTree c b x = GenericTree { treeBranches :: c (x,GenericTree b b x) }
 deriving (Generic, Hask.Functor, Hask.Foldable, Hask.Traversable)
instance (NFData x, Hask.Foldable c, Hask.Foldable b) => NFData (GenericTree c b x) where
  rnf (GenericTree t) = rnf $ toList t
instance (Hask.MonadPlus c) => Semigroup (GenericTree c b x) where
  GenericTree b1 <> GenericTree b2 = GenericTree $ Hask.mplus b1 b2
instance (Hask.MonadPlus c) => Monoid (GenericTree c b x) where
  mempty = GenericTree Hask.mzero
  mappend = (<>)
deriving instance Show (c (x, GenericTree b b x)) => Show (GenericTree c b x)

-- | Imitate the specialised 'ShadeTree' structure with a simpler, generic tree.
onlyNodes :: ∀ x . (WithField ℝ PseudoAffine x, SimpleSpace (Needle x))
                => ShadeTree x -> Trees x
onlyNodes (PlainLeaves []) = GenericTree []
onlyNodes (PlainLeaves ps) = let (ctr,_) = pseudoECM ([]::[x]) $ NE.fromList ps
                             in GenericTree [ (ctr, GenericTree $ (,mempty) <$> ps) ]
onlyNodes (DisjointBranches _ brs) = Hask.foldMap onlyNodes brs
onlyNodes (OverlappingBranches _ (Shade ctr _) brs)
              = GenericTree [ ( fromInterior ctr
                              , Hask.foldMap (Hask.foldMap onlyNodes) brs ) ]


-- | Left (and, typically, also right) inverse of 'fromLeafNodes'.
onlyLeaves :: WithField ℝ PseudoAffine x => ShadeTree x -> [x]
onlyLeaves tree = dismantle tree []
 where dismantle (PlainLeaves xs) = (xs++)
       dismantle (OverlappingBranches _ _ brs)
              = foldr ((.) . dismantle) id $ Hask.foldMap (Hask.toList) brs
       dismantle (DisjointBranches _ brs) = foldr ((.) . dismantle) id $ NE.toList brs








data Sawbones x = Sawbones { sawnTrunk1, sawnTrunk2 :: [x]->[x]
                           , sawdust1,   sawdust2   :: [x]      }
instance Semigroup (Sawbones x) where
  Sawbones st11 st12 sd11 sd12 <> Sawbones st21 st22 sd21 sd22
     = Sawbones (st11.st21) (st12.st22) (sd11<>sd21) (sd12<>sd22)
instance Monoid (Sawbones x) where
  mempty = Sawbones id id [] []
  mappend = (<>)



type DList x = [x]->[x]
    
data DustyEdges x = DustyEdges { sawChunk :: DList x, chunkDust :: DBranches' x [x] }
instance Semigroup (DustyEdges x) where
  DustyEdges c1 d1 <> DustyEdges c2 d2 = DustyEdges (c1.c2) (d1<>d2)

data Sawboneses x = SingleCut (Sawbones x)
                  | Sawboneses (DBranches' x (DustyEdges x))
    deriving (Generic)
instance Semigroup (Sawboneses x) where
  SingleCut c <> SingleCut d = SingleCut $ c<>d
  Sawboneses c <> Sawboneses d = Sawboneses $ c<>d






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

constShaded :: y -> ShadeTree x -> x`Shaded`y
constShaded y = unsafeFmapTree (WithAny y<$>) id (shadeWithAny y)

stripShadedUntopological :: x`Shaded`y -> ShadeTree x
stripShadedUntopological = unsafeFmapTree (fmap _topological) id shadeWithoutAnything

fmapShaded :: (y -> υ) -> (x`Shaded`y) -> (x`Shaded`υ)
fmapShaded f = unsafeFmapTree (fmap $ \(WithAny y x) -> WithAny (f y) x)
                              id
                              (\(Shade yx shx) -> Shade (fmap f yx) shx)

joinShaded :: (x`WithAny`y)`Shaded`z -> x`Shaded`(y,z)
joinShaded = unsafeFmapTree (fmap $ \(WithAny z (WithAny y x)) -> WithAny (y,z) x)
                            id
                            (\(Shade (WithAny z (WithAny y x)) shx)
                                  -> Shade (WithAny (y,z) x) shx )

zipTreeWithList :: ShadeTree x -> [y] -> (x`Shaded`y)
zipTreeWithList tree = go tree . cycle
 where go (PlainLeaves lvs) ys = PlainLeaves $ zipWith WithAny ys lvs
       go (DisjointBranches n brs) ys
             = DisjointBranches n . NE.fromList
                  $ snd (foldl (\(ys',prev) br -> 
                                    (drop (nLeaves br) ys', prev . (go br ys':)) )
                           (ys,id) $ NE.toList brs) []
       go (OverlappingBranches n (Shade xoc shx) brs) ys
             = OverlappingBranches n (Shade (WithAny (head ys) xoc) shx) . NE.fromList
                  $ snd (foldl (\(ys',prev) (DBranch dir (Hourglass top bot))
                        -> case drop (nLeaves top) ys' of
                              ys'' -> ( drop (nLeaves bot) ys''
                                      , prev . (DBranch dir (Hourglass (go top ys')
                                                                       (go bot ys'')):)
                                      ) )
                           (ys,id) $ NE.toList brs) []

-- | This is to 'ShadeTree' as 'Data.Map.Map' is to 'Data.Set.Set'.
type x`Shaded`y = ShadeTree (x`WithAny`y)

stiWithDensity :: ∀ x y . ( WithField ℝ PseudoAffine x, WithField ℝ LinearManifold y
                          , SimpleSpace (Needle x) )
         => x`Shaded`y -> x -> Cℝay y
stiWithDensity (PlainLeaves lvs)
  | [Shade baryc expa :: Shade x] <- pointsShades . catOptions 
                                       $ toInterior . _topological <$> lvs
       = let nlvs = fromIntegral $ length lvs :: ℝ
             indiShapes = [(Shade pi expa, y) | WithAny y p <- lvs
                                              , Option (Just pi) <- [toInterior p]]
         in \x -> let lcCoeffs = [ occlusion psh x | (psh, _) <- indiShapes ]
                      dens = sum lcCoeffs
                  in mkCone dens . linearCombo . zip (snd<$>indiShapes)
                       $ (/dens)<$>lcCoeffs
stiWithDensity (DisjointBranches _ lvs)
           = \x -> foldr1 qGather $ (`stiWithDensity`x)<$>lvs
 where qGather (Cℝay 0 _) o = o
       qGather o _ = o
stiWithDensity (OverlappingBranches n (Shade (WithAny _ bc) extend) brs)
           = ovbSWD (dualSpaceWitness, pseudoAffineWitness)
 where ovbSWD :: (DualNeedleWitness x, PseudoAffineWitness x) -> x -> Cℝay y
       ovbSWD (DualSpaceWitness, PseudoAffineWitness (SemimanifoldWitness _)) x
                     = case toInterior x>>=(.-~.bc) of
           Option (Just v)
             | dist² <- normSq ε v
             , dist² < 9
             , att <- exp(1/(dist²-9)+1/9)
               -> qGather att $ fmap ($ x) downPrepared
           _ -> coneTip
       ε = dualNorm' extend :: Norm (Needle x)
       downPrepared = dp =<< brs
        where dp (DBranch _ (Hourglass up dn))
                 = fmap stiWithDensity $ up:|[dn]
       qGather att contribs = mkCone (att*dens)
                 $ linearCombo [(v, d/dens) | Cℝay d v <- NE.toList contribs]
        where dens = sum (hParamCℝay <$> contribs)

stiAsIntervalMapping :: (x ~ ℝ, y ~ ℝ)
            => x`Shaded`y -> [(x, ((y, Diff y), LinearMap ℝ x y))]
stiAsIntervalMapping = twigsWithEnvirons >=> pure.snd.fst >=> completeTopShading >=> pure.
             \(Shade' (xloc, yloc) shd)
                 -> ( xloc, ( (yloc, recip $ shd|$|(0,1))
                            , dependence (dualNorm shd) ) )

smoothInterpolate :: ( WithField ℝ Manifold x, WithField ℝ LinearManifold y
                     , SimpleSpace (Needle x) )
             => NonEmpty (x,y) -> x -> y
smoothInterpolate l = \x ->
             case ltr x of
               Cℝay 0 _ -> defy
               Cℝay _ y -> y
 where defy = linearCombo [(y, 1/n) | WithAny y _ <- l']
       n = fromIntegral $ length l'
       l' = (uncurry WithAny . swap) <$> NE.toList l
       ltr = stiWithDensity $ fromLeafPoints l'


spanShading :: ∀ x y . ( WithField ℝ Manifold x, WithField ℝ Manifold y
                       , SimpleSpace (Needle x), SimpleSpace (Needle y) )
          => (Shade x -> Shade y) -> ShadeTree x -> x`Shaded`y
spanShading f = unsafeFmapTree addYs id addYSh
 where addYs :: NonEmpty x -> NonEmpty (x`WithAny`y)
       addYs l = foldr (NE.<|) (fmap ( WithAny ymid) l     )
                               (fmap (`WithAny`xmid) yexamp)
          where [xsh@(Shade xmid _)] = pointsCovers $ toList l
                Shade ymid yexpa = f xsh
                yexamp = [ ymid .+~^ σ*^δy
                         | δy <- varianceSpanningSystem yexpa, σ <- [-1,1] ]
       addYSh :: Shade x -> Shade (x`WithAny`y)
       addYSh xsh = shadeWithAny (_shadeCtr $ f xsh) xsh
                      


coneTip :: (AdditiveGroup v) => Cℝay v
coneTip = Cℝay 0 zeroV

mkCone :: AdditiveGroup v => ℝ -> v -> Cℝay v
mkCone 0 _ = coneTip
mkCone h v = Cℝay h v


foci :: [a] -> [(a,[a])]
foci [] = []
foci (x:xs) = (x,xs) : fmap (second (x:)) (foci xs)
       
fociNE :: NonEmpty a -> NonEmpty (a,[a])
fociNE (x:|xs) = (x,xs) :| fmap (second (x:)) (foci xs)
       

(.:) :: (c->d) -> (a->b->c) -> a->b->d 
(.:) = (.) . (.)


catOptions :: [Option a] -> [a]
catOptions = catMaybes . map getOption



class HasFlatView f where
  type FlatView f x
  flatView :: f x -> FlatView f x
  superFlatView :: f x -> [[x]]
      
instance HasFlatView Sawbones where
  type FlatView Sawbones x = [([x],[[x]])]
  flatView (Sawbones t1 t2 d1 d2) = [(t1[],[d1]), (t2[],[d2])]
  superFlatView = foldMap go . flatView
   where go (t,ds) = t : ds

instance HasFlatView Sawboneses where
  type FlatView Sawboneses x = [([x],[[x]])]
  flatView (SingleCut (Sawbones t1 t2 d1 d2)) = [(t1[],[d1]), (t2[],[d2])]
  flatView (Sawboneses (DBranches bs)) = 
        [ (m[], NE.toList ds >>= \(DBranch _ (Hourglass u' l')) -> [u',l'])
        | (DBranch _ (Hourglass u l)) <- NE.toList bs
        , (DustyEdges m (DBranches ds)) <- [u,l]
        ]
  superFlatView = foldMap go . flatView
   where go (t,ds) = t : ds






extractJust :: (a->Maybe b) -> [a] -> (Maybe b, [a])
extractJust f [] = (Nothing,[])
extractJust f (x:xs) | Just r <- f x  = (Just r, xs)
                     | otherwise      = second (x:) $ extractJust f xs

