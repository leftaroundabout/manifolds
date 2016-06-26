{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE UnicodeSyntax              #-}
{-# LANGUAGE LambdaCase                 #-}




module Data.LinearMap.HerMetric (
  -- * Metric operator types
    HerMetric(..), HerMetric'(..)
  -- * Evaluating metrics
  , toDualWith, fromDualWith
  , metricSq, metricSq', metric, metric', metrics, metrics'
  -- * Defining metrics
  , projector, projector', projectors, projector's
  , euclideanMetric'
  -- * Metrics induce inner products
  , spanHilbertSubspace
  , spanSubHilbertSpace
  , IsFreeSpace
  -- * One-dimensional axes and product spaces
  , factoriseMetric, factoriseMetric'
  , productMetric, productMetric'
  , metricAsLength, metricFromLength, metric'AsLength
  -- * Utility for metrics
  , transformMetric, transformMetric', dualCoCoProduct
  , dualiseMetric, dualiseMetric'
  , recipMetric, recipMetric'
  -- ** Eigenvectors
  , eigenSpan, eigenSpan'
  , eigenCoSpan, eigenCoSpan'
  , eigenSystem, HasEigenSystem, EigenVector
  -- ** Scaling operations
  , metriNormalise, metriNormalise'
  , metriScale', metriScale
  , volumeRatio
  , adjoint
  , extendMetric
  , applyLinMapMetric, applyLinMapMetric'
  , imitateMetricSpanChange
  -- * The dual-space class
  , HasMetric
  , HasMetric'(..)
  , (^<.>)
--   , riesz, riesz'
  -- * Fundamental requirements
  , MetricScalar
  , FiniteDimensional(..)
  -- * Misc
  , Stiefel1(..)
  , linMapAsTensProd, linMapFromTensProd
  , covariance
  , outerProducts
  ) where
    

    

import Data.VectorSpace
import Data.LinearMap
import Data.Basis
import Data.Semigroup
import Data.Tagged
import qualified Data.List as List

import qualified Prelude as Hask
import qualified Control.Applicative as Hask
import qualified Control.Monad as Hask

import Control.Category.Constrained.Prelude hiding ((^))
import Control.Arrow.Constrained
    
import Data.Manifold.Types.Primitive
import Data.CoNat

import qualified Data.Vector as Arr
import qualified Numeric.LinearAlgebra.HMatrix as HMat

import Data.VectorSpace.FiniteDimensional
import Data.LinearMap.Category
import Data.Embedding



infixr 7 <.>^, ^<.>


-- | 'HerMetric' is a portmanteau of /Hermitian/ and /metric/ (in the sense as
--   used in e.g. general relativity &#x2013; though those particular ones aren't positive
--   definite and thus not really metrics).
-- 
--   Mathematically, there are two directly equivalent ways to describe such a metric:
--   as a bilinear mapping of two vectors to a scalar, or as a linear mapping from
--   a vector space to its dual space. We choose the latter, though you can always
--   as well think of metrics as &#x201c;quadratic dual vectors&#x201d;.
--   
--   Yet other possible interpretations of this type include /density matrix/ (as in
--   quantum mechanics), /standard range of statistical fluctuations/, and /volume element/.
newtype HerMetric v = HerMetric {
          metricMatrix :: Maybe (Linear (Scalar v) v (DualSpace v)) -- @Nothing@ for zero metric.
                      }

matrixMetric :: HasMetric v => HMat.Matrix (Scalar v) -> HerMetric v
matrixMetric = HerMetric . Just . DenseLinear

-- | Deprecated (this doesn't preserve positive-definiteness)
instance (HasMetric v) => AdditiveGroup (HerMetric v) where
  zeroV = HerMetric Nothing
  negateV (HerMetric m) = HerMetric $ negateV <$> m
  HerMetric Nothing ^+^ HerMetric n = HerMetric n
  HerMetric m ^+^ HerMetric Nothing = HerMetric m
  HerMetric (Just m) ^+^ HerMetric (Just n) = HerMetric . Just $ m ^+^ n
instance HasMetric v => VectorSpace (HerMetric v) where
  type Scalar (HerMetric v) = Scalar v
  s *^ (HerMetric m) = HerMetric $ (s*^) <$> m 

-- | A metric on the dual space; equivalent to a linear mapping from the dual space
--   to the original vector space.
-- 
--   Prime-versions of the functions in this module target those dual-space metrics, so
--   we can avoid some explicit handling of double-dual spaces.
newtype HerMetric' v = HerMetric' {
          metricMatrix' :: Maybe (Linear (Scalar v) (DualSpace v) v)
                      }

extendMetric :: (HasMetric v, Scalar v~ℝ) => HerMetric v -> v -> HerMetric v
extendMetric (HerMetric Nothing) _ = HerMetric Nothing
extendMetric (HerMetric (Just (DenseLinear m))) v
      | isInfinite' detm  = HerMetric . Just $ DenseLinear m
      | isInfinite' detmninv  = singularMetric
      | otherwise         = HerMetric . Just $ DenseLinear mn
 where -- this could probably be done much more efficiently, with only
       -- multiplications, no inverses.
       (minv, (detm, _)) = HMat.invlndet m
       (mn, (detmninv, _)) = HMat.invlndet (minv + HMat.outer vv vv)
       vv = asPackedVector v
                              

matrixMetric' :: HasMetric v => HMat.Matrix (Scalar v) -> HerMetric' v
matrixMetric' = HerMetric' . Just . DenseLinear

-- | Deprecated
instance (HasMetric v) => AdditiveGroup (HerMetric' v) where
  zeroV = HerMetric' Nothing
  negateV (HerMetric' m) = HerMetric' $ negateV <$> m
  HerMetric' Nothing ^+^ HerMetric' n = HerMetric' n
  HerMetric' m ^+^ HerMetric' Nothing = HerMetric' m
  HerMetric' (Just m) ^+^ HerMetric' (Just n) = HerMetric' . Just $ m ^+^ n
instance HasMetric v => VectorSpace (HerMetric' v) where
  type Scalar (HerMetric' v) = Scalar v
  s *^ (HerMetric' m) = HerMetric' $ (s*^) <$> m 
    

-- | A metric on @v@ that simply yields the squared overlap of a vector with the
--   given dual-space reference.
--   
--   It will perhaps be the most common way of defining 'HerMetric' values to start
--   with such dual-space vectors and superimpose the projectors using the 'VectorSpace'
--   instance; e.g. @'projector' (1,0) '^+^' 'projector' (0,2)@ yields a hermitian operator
--   describing the ellipsoid span of the vectors /e/&#x2080; and 2&#x22c5;/e/&#x2081;.
--   Metrics generated this way are positive definite if no negative coefficients have
--   been introduced with the '*^' scaling operator or with '^-^'.
--   
--   Note: @projector a ^+^ projector b ^+^ ...@ is more efficiently written as
--   @projectors [a, b, ...]@
projector :: HasMetric v => DualSpace v -> HerMetric v
projector u = HerMetric . pure $ u ⊗ u

projector' :: HasMetric v => v -> HerMetric' v
projector' v = HerMetric' . pure $ v ⊗ v

-- | Efficient shortcut for the 'sumV' of multiple 'projector's.
projectors :: HasMetric v => [DualSpace v] -> HerMetric v
projectors [] = zeroV
projectors us = HerMetric . pure . outerProducts $ zip us us

projector's :: HasMetric v => [v] -> HerMetric' v
projector's [] = zeroV
projector's vs = HerMetric' . pure . outerProducts $ zip vs vs


singularMetric :: forall v . HasMetric v => HerMetric v
singularMetric = matrixMetric $ HMat.scale (1/0) (HMat.ident dim)
 where (Tagged dim) = dimension :: Tagged v Int
singularMetric' :: forall v . HasMetric v => HerMetric' v
singularMetric' = matrixMetric' $ HMat.scale (1/0) (HMat.ident dim)
 where (Tagged dim) = dimension :: Tagged v Int



-- | Evaluate a vector through a metric. For the canonical metric on a Hilbert space,
--   this will be simply 'magnitudeSq'.
metricSq :: HasMetric v => HerMetric v -> v -> Scalar v
metricSq (HerMetric Nothing) _ = 0
metricSq (HerMetric (Just (DenseLinear m))) v = vDecomp `HMat.dot` HMat.app m vDecomp
 where vDecomp = asPackedVector v


metricSq' :: HasMetric v => HerMetric' v -> DualSpace v -> Scalar v
metricSq' (HerMetric' Nothing) _ = 0
metricSq' (HerMetric' (Just (DenseLinear m))) u = uDecomp `HMat.dot` HMat.app m uDecomp
 where uDecomp = asPackedVector u

-- | Evaluate a vector's &#x201c;magnitude&#x201d; through a metric. This assumes an actual
--   mathematical metric, i.e. positive definite &#x2013; otherwise the internally used
--   square root may get negative arguments (though it can still produce results if the
--   scalars are complex; however, complex spaces aren't supported yet).
metric :: (HasMetric v, Floating (Scalar v)) => HerMetric v -> v -> Scalar v
metric m = sqrt . metricSq m

metric' :: (HasMetric v, Floating (Scalar v)) => HerMetric' v -> DualSpace v -> Scalar v
metric' m = sqrt . metricSq' m


toDualWith :: HasMetric v => HerMetric v -> v -> DualSpace v
toDualWith (HerMetric Nothing) = const zeroV
toDualWith (HerMetric (Just m)) = (m$)

fromDualWith :: HasMetric v => HerMetric' v -> DualSpace v -> v
fromDualWith (HerMetric' Nothing) = const zeroV
fromDualWith (HerMetric' (Just m)) = (m$)

-- | Divide a vector by its own norm, according to metric, i.e. normalise it
--   or &#x201c;project to the metric's boundary&#x201d;.
metriNormalise :: (HasMetric v, Floating (Scalar v)) => HerMetric v -> v -> v
metriNormalise m v = v ^/ metric m v

metriNormalise' :: (HasMetric v, Floating (Scalar v))
                 => HerMetric' v -> DualSpace v -> DualSpace v
metriNormalise' m v = v ^/ metric' m v

-- | &#x201c;Anti-normalise&#x201d; a vector: /multiply/ with its own norm, according to metric.
metriScale :: (HasMetric v, Floating (Scalar v)) => HerMetric v -> v -> v
metriScale m v = metric m v *^ v

metriScale' :: (HasMetric v, Floating (Scalar v))
                 => HerMetric' v -> DualSpace v -> DualSpace v
metriScale' m v = metric' m v *^ v


-- | Square-sum over the metrics for each dual-space vector.
-- 
-- @
-- metrics m vs &#x2261; sqrt . sum $ metricSq m '<$>' vs
-- @
metrics :: (HasMetric v, Floating (Scalar v)) => HerMetric v -> [v] -> Scalar v
metrics m vs = sqrt . sum $ metricSq m <$> vs

metrics' :: (HasMetric v, Floating (Scalar v)) => HerMetric' v -> [DualSpace v] -> Scalar v
metrics' m vs = sqrt . sum $ metricSq' m <$> vs


transformMetric :: ∀ s v w . (HasMetric v, HasMetric w, Scalar v~s, Scalar w~s)
           => Linear s w v -> HerMetric v -> HerMetric w
transformMetric _ (HerMetric Nothing) = HerMetric Nothing
transformMetric t (HerMetric (Just m)) = HerMetric . Just $ adjoint t . m . t

transformMetric' :: ∀ s v w . (HasMetric v, HasMetric w, Scalar v~s, Scalar w~s)
           => Linear s v w -> HerMetric' v -> HerMetric' w
transformMetric' _ (HerMetric' Nothing) = HerMetric' Nothing
transformMetric' t (HerMetric' (Just m)) = HerMetric' . Just $ t . m . adjoint t

-- | This does something vaguely like  @\\s t -> (s⋅t)²@,
--   but without actually requiring an inner product on the covectors.
--   Used for calculating the superaffine term of multiplications in
--   'Differentiable' categories.
dualCoCoProduct :: (HasMetric v, HasMetric w, Scalar v ~ s, Scalar w ~ s)
           => Linear s w v -> Linear s w v -> HerMetric w
dualCoCoProduct (DenseLinear smat) (DenseLinear tmat)
                  = ( (sArr `HMat.dot` (t²PLUSs² HMat.<\> sArr))
                       * (tArr `HMat.dot` (t²PLUSs² HMat.<\> tArr)) )
                    *^ matrixMetric t²PLUSs²
 where tArr = HMat.flatten tmat
       sArr = HMat.flatten smat
       t²PLUSs² = tmat HMat.<> HMat.tr tmat + smat HMat.<> HMat.tr smat


-- | This doesn't really do anything at all, since @'HerMetric' v@ is essentially a
--   synonym for @'HerMetric' ('DualSpace' v)@.
dualiseMetric :: HasMetric v => HerMetric (DualSpace v) -> HerMetric' v
dualiseMetric (HerMetric m) = HerMetric' m

dualiseMetric' :: HasMetric v => HerMetric' v -> HerMetric (DualSpace v)
dualiseMetric' (HerMetric' m) = HerMetric m


-- | The inverse mapping of a metric tensor. Since a metric maps from
--   a space to its dual, the inverse maps from the dual into the
--   (double-dual) space &#x2013; i.e., it is a metric on the dual space.
--   Deprecated: the singular case isn't properly handled.
recipMetric' :: HasMetric v => HerMetric v -> HerMetric' v
recipMetric' (HerMetric Nothing) = singularMetric'
recipMetric' (HerMetric (Just (DenseLinear m)))
          | isInfinite' detm  = singularMetric'
          | otherwise         = matrixMetric' minv
 where (minv, (detm, _)) = HMat.invlndet m

recipMetric :: HasMetric v => HerMetric' v -> HerMetric v
recipMetric (HerMetric' Nothing) = singularMetric
recipMetric (HerMetric' (Just (DenseLinear m)))
          | isInfinite' detm  = singularMetric
          | otherwise         = matrixMetric minv
 where (minv, (detm, _)) = HMat.invlndet m


isInfinite' :: (Eq a, Num a) => a -> Bool
isInfinite' 0 = False
isInfinite' x = x==x*2



-- | The eigenbasis of a metric, with each eigenvector scaled to the
--   square root of the eigenvalue. If the metric is not positive
--   definite (i.e. if it has zero eigenvalues), then the 'eigenSpan'
--   will contain zero vectors.
--   
--   This constitutes, in a sense,
--   a decomposition of a metric into a set of 'projector'' vectors. If those
--   are 'sumV'ed again (use 'projectors's' for this), then the original metric
--   is obtained. (This holds even for non-Hilbert/Banach spaces,
--   although the concept of eigenbasis and
--   &#x201c;scaled length&#x201d; doesn't really make sense there.)
eigenSpan :: (HasMetric v, Scalar v ~ ℝ) => HerMetric' v -> [v]
eigenSpan (HerMetric' Nothing) = []
eigenSpan (HerMetric' (Just (DenseLinear m))) = map fromPackedVector eigSpan
 where (μs,vsm) = HMat.eigSH' m
       eigSpan = zipWith (HMat.scale . sqrt) (HMat.toList μs) (HMat.toColumns vsm)

eigenSpan' :: (HasMetric v, Scalar v ~ ℝ) => HerMetric v -> [DualSpace v]
eigenSpan' (HerMetric Nothing) = []
eigenSpan' (HerMetric (Just (DenseLinear m))) = map fromPackedVector eigSpan
 where (μs,vsm) = HMat.eigSH' m
       eigSpan = zipWith (HMat.scale . sqrt) (HMat.toList μs) (HMat.toColumns vsm)

-- | The reciprocal-space counterparts of the nonzero-EV eigenvectors, as can
--   be obtained from 'eigenSpan'. The systems of vectors/dual vectors
--   behave as orthonormal groups WRT each other, i.e. for each @f@
--   in @'eigenCoSpan' m@ there will be exactly one @v@ in @'eigenSpan' m@
--   such that @f<.>^v ≡ 1@; the other @f<.>^v@ pairings are zero.
-- 
--   Furthermore, @'metric' m f ≡ 1@ for each @f@ in the co-span, which might
--   be seen as the actual defining characteristic of these span/co-span systems.
eigenCoSpan :: (HasMetric v, Scalar v ~ ℝ) => HerMetric' v -> [DualSpace v]
eigenCoSpan (HerMetric' Nothing) = []
eigenCoSpan (HerMetric' (Just (DenseLinear m))) = map fromPackedVector eigSpan
 where (μs,vsm) = HMat.eigSH' m
       eigSpan = map (uncurry $ HMat.scale . recip . sqrt)
                 . filter ((>0) . fst)
                 $ zip (HMat.toList μs) (HMat.toColumns vsm)
eigenCoSpan' :: (HasMetric v, Scalar v ~ ℝ) => HerMetric v -> [v]
eigenCoSpan' (HerMetric Nothing) = []
eigenCoSpan' (HerMetric (Just (DenseLinear m))) = map fromPackedVector eigSpan
 where (μs,vsm) = HMat.eigSH' m
       eigSpan = map (uncurry $ HMat.scale . recip . sqrt)
                 . filter ((>0) . fst)
                 $ zip (HMat.toList μs) (HMat.toColumns vsm)


class HasEigenSystem m where
  type EigenVector m :: *
  -- | Generalised combination of 'eigenSpan' and 'eigenCoSpan'; this will give a
  --   maximum spanning set of vector-covector pairs @(f,v)@ such that @f<.>^v ≡ 1@
  --   and @metric m f ≡ 1@, whereas all @f@ and @v'@ from different tuples
  --   are orthogonal.
  --   It also yields the /kernel/ of singular metric, spanned by a set of stiefel-manifold
  --   points, i.e. vectors of unspecified length that correspond to the eigenvalue 0.
  -- 
  --   You may also consider this as a /factorisation/ of a linear operator
  --   @𝐴 : 𝑉 → 𝑉'@ into mappings @𝑅 : 𝑉 → ℝⁿ@ and @𝐿 : ℝⁿ → 𝑉'@ (or, equivalently
  --   because ℝⁿ is a Hilbert space, @𝑅' : ℝⁿ → V'@ and @𝐿' : V → ℝⁿ@, which
  --   gives you an SVD-style inverse).
  eigenSystem :: m -> ( [Stiefel1 (EigenVector m)]
                      , [(EigenVector m, DualSpace (EigenVector m))] )

instance (HasMetric v, Scalar v ~ ℝ) => HasEigenSystem (HerMetric' v) where
  type EigenVector (HerMetric' v) = v
  eigenSystem (HerMetric' Nothing) = (fmap Stiefel1 completeBasisValues, [])
  eigenSystem (HerMetric' (Just (DenseLinear m))) = concat***concat $ unzip eigSpan
   where (μs,vsm) = HMat.eigSH' m
         eigSpan = zipWith (\μ v
                    -> if μ>0
                        then let sμ = sqrt μ
                             in ([], [( fromPackedVector $ HMat.scale sμ v
                                      , fromPackedVector $ HMat.scale (recip sμ) v )])
                        else ([Stiefel1 $ fromPackedVector v], [])
                   ) (HMat.toList μs) (HMat.toColumns vsm)

instance (HasMetric v, Scalar v ~ ℝ) => HasEigenSystem (HerMetric v) where
  type EigenVector (HerMetric v) = DualSpace v
  eigenSystem (HerMetric Nothing) = (fmap Stiefel1 completeBasisValues, [])
  eigenSystem (HerMetric (Just (DenseLinear m))) = concat***concat $ unzip eigSpan
   where (μs,vsm) = HMat.eigSH' m
         eigSpan = zipWith (\μ v
                    -> if μ>0
                        then let sμ = sqrt μ
                             in ([], [( fromPackedVector $ HMat.scale sμ v
                                      , fromPackedVector $ HMat.scale (recip sμ) v )])
                        else ([Stiefel1 $ fromPackedVector v], [])
                   ) (HMat.toList μs) (HMat.toColumns vsm)

instance (HasMetric v, Scalar v ~ ℝ) => HasEigenSystem (HerMetric' v, HerMetric' v) where
  type EigenVector (HerMetric' v, HerMetric' v) = v
  eigenSystem (n, HerMetric' (Just (DenseLinear m))) | not $ null nSpan
                                      = (++nKernel).concat***concat $ unzip eigSpan
   where (μs,vsm) = HMat.eigSH' $ fromv2ℝn HMat.<> m HMat.<> fromℝn2v'
                    -- m :: v' -> v
         eigSpan = zipWith (\μ v
                    -> if μ>0
                        then let sμ = sqrt μ
                             in ([], [( fromPackedVector $
                                        fromℝn2v HMat.#> HMat.scale sμ v
                                      , fromPackedVector $
                                        fromℝn2v' HMat.#> HMat.scale (recip sμ) v )
                                      ])
                        else ([Stiefel1 $ fromPackedVector v], [])
                   ) (HMat.toList μs) (HMat.toColumns vsm)
         fromv2ℝn = HMat.fromRows $ map (asPackedVector . snd) nSpan
         fromℝn2v' = HMat.tr fromv2ℝn
         fromℝn2v = HMat.fromColumns $ map (asPackedVector . fst) nSpan
         (nKernel, nSpan) = eigenSystem n
  eigenSystem (_, HerMetric' Nothing) = (fmap Stiefel1 completeBasisValues, [])

instance (HasMetric v, Scalar v ~ ℝ) => HasEigenSystem (HerMetric v, HerMetric v) where
  type EigenVector (HerMetric v, HerMetric v) = DualSpace v
  eigenSystem (n, HerMetric (Just (DenseLinear m))) | not $ null nSpan
                                      = (++nKernel).concat***concat $ unzip eigSpan
   where (μs,vsm) = HMat.eigSH' $ fromv'2ℝn HMat.<> m HMat.<> fromℝn2v
                    -- m :: v -> v'
         eigSpan = zipWith (\μ v
                    -> if μ>0
                        then let sμ = sqrt μ
                             in ([], [( fromPackedVector $
                                        fromℝn2v' HMat.#> HMat.scale sμ v
                                      , fromPackedVector $
                                        fromℝn2v HMat.#> HMat.scale (recip sμ) v )
                                      ])
                        else ([Stiefel1 $ fromPackedVector v], [])
                   ) (HMat.toList μs) (HMat.toColumns vsm)
         fromv'2ℝn = HMat.fromRows $ map (asPackedVector . snd) nSpan
         fromℝn2v = HMat.tr fromv'2ℝn
         fromℝn2v' = HMat.fromColumns $ map (asPackedVector . fst) nSpan
         (nKernel, nSpan) = eigenSystem n
  eigenSystem (_, HerMetric Nothing) = (fmap Stiefel1 completeBasisValues, [])


-- | Constraint that a space's scalars need to fulfill so it can be used for 'HerMetric'.
type MetricScalar s = ( SmoothScalar s
                      , Ord s  -- We really rather wouldn't require this...
                      )


type HasMetric v = (HasMetric' v, HasMetric' (DualSpace v), DualSpace (DualSpace v) ~ v)


-- | While the main purpose of this class is to express 'HerMetric', it's actually
--   all about dual spaces.
class ( FiniteDimensional v, FiniteDimensional (DualSpace v)
      , VectorSpace (DualSpace v), HasBasis (DualSpace v)
      , MetricScalar (Scalar v), Scalar v ~ Scalar (DualSpace v) )
    => HasMetric' v where
        
  -- | @'DualSpace' v@ is isomorphic to the space of linear functionals on @v@, i.e.
  --   @v ':-*' 'Scalar' v@.
  --   Typically (for all Hilbert- / 'InnerSpace's) this is in turn isomorphic to @v@
  --   itself, which will be rather more efficient (hence the distinction between a
  --   vector space and its dual is often neglected or reduced to &#x201c;column vs row
  --   vectors&#x201d;).
  --   Mathematically though, it makes sense to keep the concepts apart, even if ultimately
  --   @'DualSpace' v ~ v@ (which needs not /always/ be the case, though!).
  type DualSpace v :: *
  type DualSpace v = v
      
  -- | Apply a dual space vector (aka linear functional) to a vector.
  (<.>^) :: DualSpace v -> v -> Scalar v
            
  -- | Interpret a functional as a dual-space vector. Like 'linear', this /assumes/
  --   (completely unchecked) that the supplied function is linear.
  functional :: (v -> Scalar v) -> DualSpace v
  
  -- | While isomorphism between a space and its dual isn't generally canonical,
  --   the /double-dual/ space should be canonically isomorphic in pretty much
  --   all relevant cases. Indeed, it is recommended that they are the very same type;
  --   this condition is enforced by the 'HasMetric' constraint (which is recommended
  --   over using 'HasMetric'' itself in signatures).
  doubleDual :: HasMetric' (DualSpace v) => v -> DualSpace (DualSpace v)
  doubleDual' :: HasMetric' (DualSpace v) => DualSpace (DualSpace v) -> v
  
  basisInDual :: Tagged v (Basis v -> Basis (DualSpace v))
  basisInDual = bid
   where bid :: ∀ v . HasMetric' v => Tagged v (Basis v -> Basis (DualSpace v))
         bid = Tagged $ bi >>> ib'
          where Tagged bi = basisIndex :: Tagged v (Basis v -> Int)
                Tagged ib' = indexBasis :: Tagged (DualSpace v) (Int -> Basis (DualSpace v))

  
  

-- | Simple flipped version of '<.>^'.
(^<.>) :: HasMetric v => v -> DualSpace v -> Scalar v
ket ^<.> bra = bra <.>^ ket


euclideanMetric' :: forall v . (HasMetric v, InnerSpace v) => HerMetric v
euclideanMetric' = HerMetric . pure . DenseLinear $ HMat.ident n
 where (Tagged n) = dimension :: Tagged v Int

-- -- | Associate a Hilbert space vector canonically with its dual-space counterpart,
-- --   as by the Riesz representation theorem.
-- --   
-- --   Note that usually, Hilbert spaces should just implement @DualSpace v ~ v@,
-- --   according to that same correspondence, so 'riesz' is essentially just a more explicit
-- --   (and less efficient) way of writing @'id' :: v -> DualSpace v'.
-- riesz :: (HasMetric v, InnerSpace v) => v -> DualSpace v
-- riesz v = functional (v<.>)
-- 
-- riesz' :: (HasMetric v, InnerSpace v) => DualSpace v -> v
-- riesz' f = doubleDual' . functional (f<.>^)


instance (MetricScalar k) => HasMetric' (ZeroDim k) where
  Origin<.>^Origin = zeroV
  functional _ = Origin
  doubleDual = id; doubleDual'= id; basisInDual = pure id
instance HasMetric' Double where
  (<.>^) = (<.>)
  functional f = f 1
  doubleDual = id; doubleDual'= id; basisInDual = pure id
instance ( HasMetric v, HasMetric w, Scalar v ~ Scalar w
         ) => HasMetric' (v,w) where
  type DualSpace (v,w) = (DualSpace v, DualSpace w)
  (v,w)<.>^(v',w') = v<.>^v' + w<.>^w'
  functional f = (functional $ f . (,zeroV), functional $ f . (zeroV,))
  doubleDual = id; doubleDual'= id
  basisInDual = bid
   where bid :: ∀ v w . (HasMetric v, HasMetric w) => Tagged (v,w)
                       (Basis v + Basis w -> Basis (DualSpace v) + Basis (DualSpace w))
         bid = Tagged $ \case Left q -> Left $ bidv q
                              Right q -> Right $ bidw q
          where Tagged bidv = basisInDual :: Tagged v (Basis v -> Basis (DualSpace v))
                Tagged bidw = basisInDual :: Tagged w (Basis w -> Basis (DualSpace w))
instance (SmoothScalar s, Ord s, KnownNat n) => HasMetric' (s^n) where
  type DualSpace (s^n) = s^n
  (<.>^) = (<.>)
  functional = fnal
   where fnal :: ∀ s n . (SmoothScalar s, KnownNat n) => (s^n -> s) -> s^n
         fnal f =     FreeVect . Arr.generate n $
            \i -> f . FreeVect . Arr.generate n $ \j -> if i==j then 1 else 0
          where Tagged n = theNatN :: Tagged n Int
  doubleDual = id; doubleDual'= id; basisInDual = pure id
instance (HasMetric v, s~Scalar v) => HasMetric' (FinVecArrRep t v s) where
  type DualSpace (FinVecArrRep t v s) = FinVecArrRep t (DualSpace v) s
  FinVecArrRep v <.>^ FinVecArrRep w = HMat.dot v w
  functional = fnal
   where fnal :: ∀ v . HasMetric v =>
                 (FinVecArrRep t v (Scalar v) -> Scalar v)
                       -> FinVecArrRep t (DualSpace v) (Scalar v)
         fnal f = FinVecArrRep . (n HMat.|>)
                     $ (f . FinVecArrRep) <$> HMat.toRows (HMat.ident n)
         Tagged n = dimension :: Tagged v Int
  doubleDual = id; doubleDual'= id
  basisInDual = bid
   where bid :: ∀ s v t . (HasMetric v, s~Scalar v)
                     => Tagged (FinVecArrRep t v s) (Basis v -> Basis (DualSpace v))
         bid = Tagged bid₀
          where Tagged bid₀ = basisInDual :: Tagged v (Basis v -> Basis (DualSpace v))

instance (HasMetric v, HasMetric w, s ~ Scalar v, s ~ Scalar w)
               => HasMetric' (Linear s v w) where
  type DualSpace (Linear s v w) = Linear s w v
  DenseLinear bw <.>^ DenseLinear fw
                  = HMat.sumElements (HMat.tr bw * fw) -- trace of product
  functional = completeBasisFunctional
  doubleDual = id; doubleDual' = id

completeBasisFunctional :: ∀ v . HasMetric' v => (v -> Scalar v) -> DualSpace v
completeBasisFunctional f = recompose [ (bid b, f $ basisValue b) | b <- cb ]
          where Tagged cb = completeBasis :: Tagged v [Basis v]
                Tagged bid = basisInDual :: Tagged v (Basis v -> Basis (DualSpace v))




-- | Transpose a linear operator. Contrary to popular belief, this does not
--   just inverse the direction of mapping between the spaces, but also switch to
--   their duals.
adjoint :: (HasMetric v, HasMetric w, s~Scalar v, s~Scalar w)
     => (Linear s v w) -> Linear s (DualSpace w) (DualSpace v)
adjoint (DenseLinear m) = DenseLinear $ HMat.tr m

adjoint_fln :: (HasMetric v, HasMetric w, Scalar w ~ Scalar v)
     => (v :-* w) -> DualSpace w :-* DualSpace v
adjoint_fln m = linear $ \w -> functional $ \v
                     -> w <.>^lapply m v



metrConst :: forall v. (HasMetric v, v ~ DualSpace v, Num (Scalar v))
                 => Scalar v -> HerMetric v
metrConst μ = matrixMetric $ HMat.scale μ (HMat.ident dim)
 where (Tagged dim) = dimension :: Tagged v Int

instance (HasMetric v, v ~ DualSpace v, Num (Scalar v)) => Num (HerMetric v) where
  fromInteger = metrConst . fromInteger
  (+) = (^+^)
  negate = negateV
           
  -- | This does /not/ work correctly if the metrics don't share an eigenbasis!
  HerMetric m * HerMetric n = HerMetric . fmap DenseLinear
                              $ liftA2 (HMat.<>) (getDenseMatrix<$>m) (getDenseMatrix<$>n)
                              
  -- | Undefined, though it could actually be done.
  abs = error "abs undefined for HerMetric"
  signum = error "signum undefined for HerMetric"


metrNumFun :: (HasMetric v, v ~ Scalar v, v ~ DualSpace v, Num v)
      => (v -> v) -> HerMetric v -> HerMetric v
metrNumFun f (HerMetric Nothing) = matrixMetric . HMat.scalar $ f 0
metrNumFun f (HerMetric (Just (DenseLinear m)))
              = matrixMetric . HMat.scalar . f $ m HMat.! 0 HMat.! 0

instance (HasMetric v, v ~ Scalar v, v ~ DualSpace v, Fractional v) 
            => Fractional (HerMetric v) where
  fromRational = metrConst . fromRational
  recip = metrNumFun recip

instance (HasMetric v, v ~ Scalar v, v ~ DualSpace v, Floating v)
            => Floating (HerMetric v) where
  pi = metrConst pi
  sqrt = metrNumFun sqrt
  exp = metrNumFun exp
  log = metrNumFun log
  sin = metrNumFun sin
  cos = metrNumFun cos
  tan = metrNumFun tan
  asin = metrNumFun asin
  acos = metrNumFun acos
  atan = metrNumFun atan
  sinh = metrNumFun sinh
  cosh = metrNumFun cosh
  asinh = metrNumFun asinh
  atanh = metrNumFun atanh
  acosh = metrNumFun acosh




normaliseWith :: HasMetric v => HerMetric v -> v -> Option v
normaliseWith m v = case metric m v of
                      0 -> empty
                      μ -> pure (v ^/ μ)

orthonormalPairsWith :: forall v . HasMetric v => HerMetric v -> [v] -> [(v, DualSpace v)]
orthonormalPairsWith met = mkON
 where mkON :: [v] -> [(v, DualSpace v)]    -- Generalised Gram-Schmidt process
       mkON [] = []
       mkON (v:vs) = let onvs = mkON vs
                         v' = List.foldl' (\va (vb,pb) -> va ^-^ vb ^* (pb <.>^ va)) v onvs
                         p' = toDualWith met v'
                     in case sqrt (p' <.>^ v') of
                         0 -> onvs
                         μ -> (v'^/μ, p'^/μ) : onvs
                     


-- | Project a metric on each of the factors of a product space. This works by
--   projecting the eigenvectors into both subspaces.
factoriseMetric :: ∀ v w . (HasMetric v, HasMetric w, Scalar v ~ ℝ, Scalar w ~ ℝ)
               => HerMetric (v,w) -> (HerMetric v, HerMetric w)
factoriseMetric (HerMetric Nothing) = (HerMetric Nothing, HerMetric Nothing)
factoriseMetric met = (projectors *** projectors) . unzip $ eigenSpan' met

factoriseMetric' :: ∀ v w . (HasMetric v, HasMetric w, Scalar v ~ ℝ, Scalar w ~ ℝ)
               => HerMetric' (v,w) -> (HerMetric' v, HerMetric' w)
factoriseMetric' met = (projector's *** projector's) . unzip $ eigenSpan met

productMetric :: ∀ v w . (HasMetric v, HasMetric w, Scalar v ~ ℝ, Scalar w ~ ℝ)
               => HerMetric v -> HerMetric w -> HerMetric (v,w)
productMetric (HerMetric Nothing) (HerMetric Nothing) = HerMetric Nothing
productMetric (HerMetric (Just mv)) (HerMetric (Just mw)) = HerMetric . Just $ mv *** mw
productMetric (HerMetric Nothing) (HerMetric (Just mw)) = HerMetric . Just $ zeroV *** mw
productMetric (HerMetric (Just mv)) (HerMetric Nothing) = HerMetric . Just $ mv *** zeroV

productMetric' :: ∀ v w . (HasMetric v, HasMetric w, Scalar v ~ ℝ, Scalar w ~ ℝ)
               => HerMetric' v -> HerMetric' w -> HerMetric' (v,w)
productMetric' (HerMetric' Nothing) (HerMetric' Nothing) = HerMetric' Nothing
productMetric' (HerMetric' (Just mv)) (HerMetric' (Just mw)) = HerMetric' . Just $ mv***mw
productMetric' (HerMetric' Nothing) (HerMetric' (Just mw)) = HerMetric' . Just $ zeroV***mw
productMetric' (HerMetric' (Just mv)) (HerMetric' Nothing) = HerMetric' . Just $ mv***zeroV


applyLinMapMetric :: ∀ v w . (HasMetric v, HasMetric w, Scalar v ~ ℝ, Scalar w ~ ℝ)
               => HerMetric (Linear ℝ v w) -> DualSpace v -> HerMetric w
applyLinMapMetric met v' = transformMetric ap2v met
 where ap2v :: Linear ℝ w (Linear ℝ v w)
       ap2v = denseLinear $ \w -> denseLinear $ \v -> w ^* (v'<.>^v)

applyLinMapMetric' :: ∀ v w . (HasMetric v, HasMetric w, Scalar v ~ ℝ, Scalar w ~ ℝ)
               => HerMetric' (Linear ℝ v w) -> v -> HerMetric' w
applyLinMapMetric' met v = transformMetric' ap2v met
 where ap2v :: Linear ℝ (Linear ℝ v w) w
       ap2v = denseLinear ($v)



imitateMetricSpanChange :: ∀ v . (HasMetric v, Scalar v ~ ℝ)
                           => HerMetric v -> HerMetric' v -> Linear ℝ v v
imitateMetricSpanChange (HerMetric (Just m)) (HerMetric' (Just n)) = n . m
imitateMetricSpanChange _ _ = zeroV


covariance :: ∀ v w . (HasMetric v, HasMetric w, Scalar v ~ ℝ, Scalar w ~ ℝ)
          => HerMetric' (v,w) -> Option (Linear ℝ v w)
covariance (HerMetric' Nothing) = pure zeroV
covariance (HerMetric' (Just m))
    | isInfinite' detvnm  = empty
    | otherwise           = return $ snd . m . (id&&&zeroV) . DenseLinear vnorml
 where (vnorml, (detvnm, _))
           = HMat.invlndet . getDenseMatrix $ fst . m . (id&&&zeroV)


volumeRatio :: HasMetric v => HerMetric v -> HerMetric v -> Scalar v
volumeRatio (HerMetric Nothing) (HerMetric Nothing) = 1
volumeRatio (HerMetric _) (HerMetric Nothing) = 0
volumeRatio (HerMetric (Just (DenseLinear m₁)))
            (HerMetric (Just (DenseLinear m₂)))
    = HMat.det m₂ / HMat.det m₁
volumeRatio (HerMetric Nothing) (HerMetric _) = 1/0


metricAsLength :: HerMetric ℝ -> ℝ
metricAsLength m = case metricSq m 1 of
   o | o > 0      -> sqrt $ recip o
     | o < 0      -> error "Metric fails to be positive definite!"
     | o == 0     -> error "Trying to use zero metric as length."
     | otherwise  -> error "Metric yields NaN."

metricFromLength :: ℝ -> HerMetric ℝ
metricFromLength = projector . recip

metric'AsLength :: HerMetric' ℝ -> ℝ
metric'AsLength = sqrt . (`metric'`1)


spanHilbertSubspace :: ∀ s v w
   . (HasMetric v, Scalar v ~ s, IsFreeSpace w, Scalar w ~ s)
      => HerMetric v   -- ^ Metric to induce the inner product on the Hilbert space.
          -> [v]       -- ^ @n@ linearly independent vectors, to span the subspace @w@.
          -> Option (Embedding (Linear s) w v)
                  -- ^ An embedding of the @n@-dimensional free subspace @w@ (if the given
                  --   vectors actually span such a space) into the main space @v@.
                  --   Regardless of the structure of @v@ (which doesn't need to have an
                  --   inner product at all!), @w@ will be an 'InnerSpace' with the scalar
                  --   product defined by the given metric.
spanHilbertSubspace met = emb . orthonormalPairsWith met
 where emb onb'
         | n'==n      = return $ Embedding emb prj . arr identityMatrix
         | otherwise  = empty
        where emb = DenseLinear . HMat.fromColumns $ (asPackedVector . fst) <$> onb
              prj = DenseLinear . HMat.fromRows    $ (asPackedVector . snd) <$> onb
              n' = length onb'
              onb = take n onb'
              (Tagged n) = theNatN :: Tagged (FreeDimension w) Int


-- | Same as 'spanHilbertSubspace', but with the standard 'euclideanMetric' (i.e., the
--   basis vectors will be orthonormal in the usual sense, in both @w@ and @v@).
spanSubHilbertSpace :: forall s v w
        . (HasMetric v, InnerSpace v, Scalar v ~ s, IsFreeSpace w, Scalar w ~ s)
      => [v]
          -> Option (Embedding (Linear s) w v)
spanSubHilbertSpace = spanHilbertSubspace euclideanMetric'


-- | The /n/-th Stiefel manifold is the space of all possible configurations of
--   /n/ orthonormal vectors. In the case /n/ = 1, simply the subspace of normalised
--   vectors, i.e. equivalent to the 'UnitSphere'. Even so, it strictly speaking
--   requires the containing space to be at least metric (if not Hilbert); we would
--   however like to be able to use this concept also in spaces with no inner product,
--   therefore we define this space not as normalised vectors, but rather as all
--   vectors modulo scaling by positive factors.
newtype Stiefel1 v = Stiefel1 { getStiefel1N :: DualSpace v }







instance (HasMetric v, Scalar v ~ Double, Show (DualSpace v)) => Show (HerMetric v) where
  showsPrec p m
    | null eigSp  = showString "zeroV"
    | otherwise   = showParen (p>5)
                      . foldr1 ((.) . (.(" ^+^ "++)))
                      $ ((("projector "++).).showsPrec 10)<$>eigSp
   where eigSp = eigenSpan' m

instance (HasMetric v, Scalar v ~ Double, Show v) => Show (HerMetric' v) where
  showsPrec p m
    | null eigSp  = showString "zeroV"
    | otherwise   = showParen (p>5)
                      . foldr1 ((.) . (.(" ^+^ "++)))
                      $ ((("projector' "++).).showsPrec 10)<$>eigSp
   where eigSp = eigenSpan m









linMapAsTensProd :: (FiniteDimensional v, FiniteDimensional w, Scalar v~Scalar w)
                    => v:-*w -> DualSpace v ⊗ w
linMapAsTensProd f = DensTensProd $ asPackedMatrix f

linMapFromTensProd :: (FiniteDimensional v, FiniteDimensional w, Scalar v~Scalar w)
                    => DualSpace v ⊗ w -> v:-*w
linMapFromTensProd (DensTensProd m) = linear $
                         asPackedVector >>> HMat.app m >>> fromPackedVector



(⊗) :: (HasMetric v, FiniteDimensional w, Scalar v ~ s, Scalar w ~ s)
                    => w -> DualSpace v -> Linear s v w
w ⊗ v' = DenseLinear $ HMat.outer wDecomp v'Decomp
 where wDecomp = asPackedVector w
       v'Decomp = asPackedVector v'

outerProducts :: (HasMetric v, FiniteDimensional w, Scalar v ~ s, Scalar w ~ s)
                    => [(w, DualSpace v)] -> Linear s v w
outerProducts [] = zeroV
outerProducts pds = DenseLinear $ HMat.fromColumns (asPackedVector.fst<$>pds)
                          HMat.<> HMat.fromRows    (asPackedVector.snd<$>pds)

instance ∀ v w s . ( HasMetric v, FiniteDimensional w
                   , Show (DualSpace v), Show w, Scalar v ~ s, Scalar w ~ s )
    => Show (Linear s v w) where
  showsPrec p f = showParen (p>9) $ ("outerProducts "++)
        . shows [ (w, v' :: DualSpace v)
                | (v,v') <- zip completeBasisValues completeBasisValues
                , let w = f $ v ]
  

