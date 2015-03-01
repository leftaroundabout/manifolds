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




module Data.LinearMap.HerMetric (
  -- * Metric operator types
    HerMetric, HerMetric'
  -- * Evaluating metrics
  , metricSq, metricSq', metric, metric', metrics, metrics'
  -- * Defining metrics by projectors
  , projector, projector'
  -- * Utility for metrics
  , transformMetric, transformMetric'
  , dualiseMetric, dualiseMetric'
  , recipMetric, recipMetric'
  , metriScale', metriScale
  , adjoint
  -- * The dual-space class
  , HasMetric
  , HasMetric'(..)
  , (^<.>)
  -- * Fundamental requirements
  , MetricScalar
  , FiniteDimensional(..)
  ) where
    

    

import Prelude hiding ((^))

import Data.VectorSpace
import Data.LinearMap
import Data.Basis
import Data.MemoTrie
import Data.Tagged
import Data.Void

import Control.Applicative
    
import Data.Manifold.Types

import qualified Numeric.LinearAlgebra.HMatrix as HMat


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
   -- morally:  @getHerMetric :: v :-* DualSpace v@.
          metricMatrix :: Maybe (HMat.Matrix (Scalar v)) -- @Nothing@ for zero metric.
                      }

matrixMetric :: HasMetric v => HMat.Matrix (Scalar v) -> HerMetric v
matrixMetric = HerMetric . Just

instance (HasMetric v) => AdditiveGroup (HerMetric v) where
  zeroV = HerMetric Nothing
  negateV (HerMetric m) = HerMetric $ negate <$> m
  HerMetric Nothing ^+^ HerMetric n = HerMetric n
  HerMetric m ^+^ HerMetric Nothing = HerMetric m
  HerMetric (Just m) ^+^ HerMetric (Just n) = HerMetric . Just $ m + n
instance HasMetric v => VectorSpace (HerMetric v) where
  type Scalar (HerMetric v) = Scalar v
  s *^ (HerMetric m) = HerMetric $ HMat.scale s <$> m 

-- | A metric on the dual space; equivalent to a linear mapping from the dual space
--   to the original vector space.
-- 
--   Prime-versions of the functions in this module target those dual-space metrics, so
--   we can avoid some explicit handling of double-dual spaces.
newtype HerMetric' v = HerMetric' {
          metricMatrix' :: Maybe (HMat.Matrix (Scalar v))
                      }

matrixMetric' :: HasMetric v => HMat.Matrix (Scalar v) -> HerMetric' v
matrixMetric' = HerMetric' . Just

instance (HasMetric v) => AdditiveGroup (HerMetric' v) where
  zeroV = HerMetric' Nothing
  negateV (HerMetric' m) = HerMetric' $ negate <$> m
  HerMetric' Nothing ^+^ HerMetric' n = HerMetric' n
  HerMetric' m ^+^ HerMetric' Nothing = HerMetric' m
  HerMetric' (Just m) ^+^ HerMetric' (Just n) = matrixMetric' $ m + n
instance HasMetric v => VectorSpace (HerMetric' v) where
  type Scalar (HerMetric' v) = Scalar v
  s *^ (HerMetric' m) = HerMetric' $ HMat.scale s <$> m 
    

-- | A metric on @v@ that simply yields the squared overlap of a vector with the
--   given dual-space reference.
--   
--   It will perhaps be the most common way of defining 'HerMetric' values to start
--   with such dual-space vectors and superimpose the projectors using the 'VectorSpace'
--   instance; e.g. @'projector' (1,0) '^+^' 'projector' (0,2)@ yields a hermitian operator
--   describing the ellipsoid span of the vectors /e/&#x2080; and 2&#x22c5;/e/&#x2081;.
--   Metrics generated this way are positive definite if no negative coefficients have
--   been introduced with the '*^' scaling operator or with '^-^'.
projector :: HasMetric v => DualSpace v -> HerMetric v
projector u = matrixMetric $ HMat.outer uDecomp uDecomp
 where uDecomp = asPackedVector u

projector' :: HasMetric v => v -> HerMetric' v
projector' v = matrixMetric' $ HMat.outer vDecomp vDecomp
 where vDecomp = asPackedVector v


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
metricSq (HerMetric (Just m)) v = vDecomp `HMat.dot` HMat.app m vDecomp
 where vDecomp = asPackedVector v


metricSq' :: HasMetric v => HerMetric' v -> DualSpace v -> Scalar v
metricSq' (HerMetric' Nothing) _ = 0
metricSq' (HerMetric' (Just m)) u = uDecomp `HMat.dot` HMat.app m uDecomp
 where uDecomp = HMat.fromList $ snd <$> decompose u

-- | Evaluate a vector's &#x201c;magnitude&#x201d; through a metric. This assumes an actual
--   mathematical metric, i.e. positive definite &#x2013; otherwise the internally used
--   square root may get negative arguments (though it can still produce results if the
--   scalars are complex; however, complex spaces aren't supported yet).
metric :: (HasMetric v, Floating (Scalar v)) => HerMetric v -> v -> Scalar v
metric m = sqrt . metricSq m

metric' :: (HasMetric v, Floating (Scalar v)) => HerMetric' v -> DualSpace v -> Scalar v
metric' m = sqrt . metricSq' m

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


transformMetric :: (HasMetric v, HasMetric w, Scalar v ~ Scalar w)
           => (w :-* v) -> HerMetric v -> HerMetric w
transformMetric _ (HerMetric Nothing) = HerMetric Nothing
transformMetric t (HerMetric (Just m)) = matrixMetric $ HMat.tr tmat HMat.<> m HMat.<> tmat
 where tmat = asPackedMatrix t

transformMetric' :: ( HasMetric v, HasMetric w, Scalar v ~ Scalar w )
           => (v :-* w) -> HerMetric' v -> HerMetric' w
transformMetric' _ (HerMetric' Nothing) = HerMetric' Nothing
transformMetric' t (HerMetric' (Just m))
                      = matrixMetric' $ HMat.tr tmat HMat.<> m HMat.<> tmat
 where tmat = asPackedMatrix t

-- | This doesn't really do anything at all, since @'HerMetric' v@ is essentially a
--   synonym for @'HerMetric' ('DualSpace' v)@.
dualiseMetric :: HasMetric v => HerMetric (DualSpace v) -> HerMetric' v
dualiseMetric (HerMetric m) = HerMetric' m

dualiseMetric' :: HasMetric v => HerMetric' v -> HerMetric (DualSpace v)
dualiseMetric' (HerMetric' m) = HerMetric m


-- | The inverse mapping of a metric tensor. Since a metric maps from
--   a space to its dual, the inverse maps from the dual into the
--   (double-dual) space &#x2013; i.e., it is a metric on the dual space.
recipMetric' :: HasMetric v => HerMetric v -> HerMetric' v
recipMetric' (HerMetric Nothing) = singularMetric'
recipMetric' (HerMetric (Just m))
          | isInfinite' detm  = singularMetric'
          | otherwise         = matrixMetric' minv
 where (minv, (detm, _)) = HMat.invlndet m

recipMetric :: HasMetric v => HerMetric' v -> HerMetric v
recipMetric (HerMetric' Nothing) = singularMetric
recipMetric (HerMetric' (Just m))
          | isInfinite' detm  = singularMetric
          | otherwise         = matrixMetric minv
 where (minv, (detm, _)) = HMat.invlndet m


isInfinite' :: (Eq a, Num a) => a -> Bool
isInfinite' x = x==x*2


-- | Constraint that a space's scalars need to fulfill so it can be used for 'HerMetric'.
--   It is somewhat wise to just assume this class contains only the type 'Double'...
type MetricScalar s = ( VectorSpace s, HMat.Numeric s, HMat.Field s
                      , Eq s  -- We really rather wouldn't require this...
                      , Num(HMat.Vector s), HMat.Indexable(HMat.Vector s)s )


-- | At the moment, 'HerMetric' is implemented as a packed, dense 'HMat.Matrix'. For one
--   thing, that makes common general vector operations quite efficient, in particular on
--   high-dimensional spaces. More importantly, @hmatrix@ offers linear algebra facilities
--   such as inverse and eigenbasis transformations, which aren't available in the
--   @vector-space@ library yet (whose classes we strongly prefer to plain matrices
--   and arrays).
-- 
--   The 'FiniteDimensional' class is used to convert between both representations.
--   It would be nice not to have the requirement of finite dimension on 'HerMetric',
--   but it's probably not feasible to get rid of it in forseeable time.
class (HasBasis v, HasTrie (Basis v), MetricScalar (Scalar v)) => FiniteDimensional v where
  dimension :: Tagged v Int
  basisIndex :: Tagged v (Basis v -> Int)
  -- | Index must be in @[0 .. dimension-1]@, otherwise this is undefined.
  indexBasis :: Tagged v (Int -> Basis v)
  completeBasis :: Tagged v [Basis v]
  completeBasis = liftA2 (\dim f -> f <$> [0 .. dim - 1]) dimension indexBasis
  
  asPackedVector :: v -> HMat.Vector (Scalar v)
  asPackedVector v = HMat.fromList $ snd <$> decompose v
  
  asPackedMatrix :: (FiniteDimensional w, Scalar w ~ Scalar v)
                       => (v :-* w) -> HMat.Matrix (Scalar v)
  asPackedMatrix = defaultAsPackedMatrix
   where defaultAsPackedMatrix :: forall v w s .
               (FiniteDimensional v, FiniteDimensional w, s~Scalar v, s~Scalar w)
                         => (v :-* w) -> HMat.Matrix s
         defaultAsPackedMatrix m = HMat.fromRows $ asPackedVector . atBasis m <$> cb
          where (Tagged cb) = completeBasis :: Tagged v [Basis v]

instance (MetricScalar k) => FiniteDimensional (ZeroDim k) where
  dimension = Tagged 0
  basisIndex = Tagged absurd
  indexBasis = Tagged $ const undefined
  completeBasis = Tagged []
  asPackedVector Origin = HMat.fromList []
instance FiniteDimensional ℝ where
  dimension = Tagged 1
  basisIndex = Tagged $ \() -> 0
  indexBasis = Tagged $ \0 -> ()
  completeBasis = Tagged [()]
  asPackedVector x = HMat.fromList [x]
  asPackedMatrix f = HMat.asRow . asPackedVector $ atBasis f ()
instance (FiniteDimensional a, FiniteDimensional b, Scalar a~Scalar b)
            => FiniteDimensional (a,b) where
  dimension = tupDim
   where tupDim :: forall a b.(FiniteDimensional a,FiniteDimensional b)=>Tagged(a,b)Int
         tupDim = Tagged $ da+db
          where (Tagged da)=dimension::Tagged a Int; (Tagged db)=dimension::Tagged b Int
  basisIndex = basId
   where basId :: forall a b . (FiniteDimensional a, FiniteDimensional b)
                     => Tagged (a,b) (Either (Basis a) (Basis b) -> Int)
         basId = Tagged basId'
          where basId' (Left ba) = basIda ba
                basId' (Right bb) = da + basIdb bb
                (Tagged da) = dimension :: Tagged a Int
                (Tagged basIda) = basisIndex :: Tagged a (Basis a->Int)
                (Tagged basIdb) = basisIndex :: Tagged b (Basis b->Int)
  indexBasis = basId
   where basId :: forall a b . (FiniteDimensional a, FiniteDimensional b)
                     => Tagged (a,b) (Int -> Either (Basis a) (Basis b))
         basId = Tagged basId'
          where basId' i | i < da     = Left $ basIda i
                         | otherwise  = Right . basIdb $ i - da
                (Tagged da) = dimension :: Tagged a Int
                (Tagged basIda) = indexBasis :: Tagged a (Int->Basis a)
                (Tagged basIdb) = indexBasis :: Tagged b (Int->Basis b)
  completeBasis = cb
   where cb :: forall a b . (FiniteDimensional a, FiniteDimensional b)
                     => Tagged (a,b) [Either (Basis a) (Basis b)]
         cb = Tagged $ map Left cba ++ map Right cbb
          where (Tagged cba) = completeBasis :: Tagged a [Basis a]
                (Tagged cbb) = completeBasis :: Tagged b [Basis b]
  asPackedVector (a,b) = HMat.vjoin [asPackedVector a, asPackedVector b]
              
  
                                                          


type HasMetric v = (HasMetric' v, HasMetric' (DualSpace v), DualSpace (DualSpace v) ~ v)


-- | While the main purpose of this class is to express 'HerMetric', it's actually
--   all about dual spaces.
class ( FiniteDimensional v, FiniteDimensional (DualSpace v)
      , VectorSpace (DualSpace v), HasBasis (DualSpace v)
      , Scalar v ~ Scalar (DualSpace v), Basis v ~ Basis (DualSpace v) )
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
  --   this condition is enforced by the 'HerMetric' constraint (which is recommended
  --   over using 'HerMetric'' itself in signatures).
  doubleDual :: HasMetric' (DualSpace v) => v -> DualSpace (DualSpace v)
  doubleDual' :: HasMetric' (DualSpace v) => DualSpace (DualSpace v) -> v
  
  

-- | Simple flipped version of '<.>^'.
(^<.>) :: HasMetric v => v -> DualSpace v -> Scalar v
ket ^<.> bra = bra <.>^ ket

instance (MetricScalar k) => HasMetric' (ZeroDim k) where
  Origin<.>^Origin = zeroV
  functional _ = Origin
  doubleDual = id; doubleDual'= id
instance HasMetric' Double where
  (<.>^) = (<.>)
  functional f = f 1
  doubleDual = id; doubleDual'= id
instance ( HasMetric v, HasMetric w, Scalar v ~ Scalar w
         ) => HasMetric' (v,w) where
  type DualSpace (v,w) = (DualSpace v, DualSpace w)
  (v,w)<.>^(v',w') = v<.>^v' + w<.>^w'
  functional f = (functional $ f . (,zeroV), functional $ f . (zeroV,))
  doubleDual = id; doubleDual'= id





-- | Transpose a linear operator. Contrary to popular belief, this does not
--   just inverse the direction of mapping between the spaces, but also switch to
--   their duals.
adjoint :: (HasMetric v, HasMetric w, Scalar w ~ Scalar v)
     => (v :-* w) -> DualSpace w :-* DualSpace v
adjoint m = linear $ \w -> functional $ \v
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
  HerMetric m * HerMetric n = HerMetric $ liftA2 (HMat.<>) m n
                              
  -- | Undefined, though it could actually be done.
  abs = error "abs undefined for HerMetric"
  signum = error "signum undefined for HerMetric"


metrNumFun :: (HasMetric v, v ~ Scalar v, v ~ DualSpace v, Num v)
      => (v -> v) -> HerMetric v -> HerMetric v
metrNumFun f (HerMetric Nothing) = matrixMetric . HMat.scalar $ f 0
metrNumFun f (HerMetric (Just m)) = matrixMetric . HMat.scalar . f $ m HMat.! 0 HMat.! 0

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





