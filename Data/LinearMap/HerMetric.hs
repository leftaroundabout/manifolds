{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts           #-}
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
  -- * Utility
  , metriScale
  , adjoint
  , transformMetric
  , transformMetric'
  , dualiseMetric, dualiseMetric'
  , HasMetric(..)
  , (^<.>)
  ) where
    

    

import Data.VectorSpace
import Data.LinearMap
import Data.Basis
import Data.MemoTrie

import Control.Applicative
    


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
newtype HerMetric v = HerMetric { getHerMetric :: v :-* DualSpace v }


instance HasMetric v => AdditiveGroup (HerMetric v) where
  zeroV = HerMetric zeroV
  negateV (HerMetric m) = HerMetric $ negateV m
  HerMetric m ^+^ HerMetric n = HerMetric $ m ^+^ n
instance HasMetric v => VectorSpace (HerMetric v) where
  type Scalar (HerMetric v) = Scalar v
  s *^ (HerMetric m) = HerMetric $ s *^ m 

-- | A metric on the dual space; equivalent to a linear mapping from the dual space
--   to the original vector space.
-- 
--   Prime-versions of the functions in this module target those dual-space metrics, so
--   we can avoid some explicit handling of double-dual spaces.
newtype HerMetric' v = HerMetric' { dualMetric :: DualSpace v :-* v }
instance (HasMetric v) => AdditiveGroup (HerMetric' v) where
  zeroV = HerMetric' zeroV
  negateV (HerMetric' m) = HerMetric' $ negateV m
  HerMetric' m ^+^ HerMetric' n = HerMetric' $ m ^+^ n
instance (HasMetric v) => VectorSpace (HerMetric' v) where
  type Scalar (HerMetric' v) = Scalar v
  s *^ (HerMetric' m) = HerMetric' $ s *^ m 
    

-- | A metric on @v@ that simply yields the squared overlap of a vector with the
--   given dual-space reference.
--   
--   It will perhaps be the most common way of defining 'Hermetric' values to start
--   with such dual-space vectors and superimpose the projectors using the 'VectorSpace'
--   instance; e.g. @'projector' (1,0) '^+^' 'projector' (0,2)@ yields a hermitian operator
--   describing the ellipsoid span of the vectors /e/&#x2080; and 2&#x22c5;/e/&#x2081;.
--   Metrics generated this way are always positive definite.
projector :: HasMetric v => DualSpace v -> HerMetric v
projector u = HerMetric (linear $ \v -> u ^* (u<.>^v))

projector' :: HasMetric v => v -> HerMetric' v
projector' v = HerMetric' . linear $ \u -> v ^* (v^<.>u)



-- | Evaluate a vector through a metric. For the canonical metric on a Hilbert space,
--   this will be simply 'magnitudeSq'.
metricSq :: HasMetric v => HerMetric v -> v -> Scalar v
metricSq (HerMetric m) v = lapply m v <.>^ v

metricSq' :: HasMetric v => HerMetric' v -> DualSpace v -> Scalar v
metricSq' (HerMetric' m) u = lapply m u ^<.> u

-- | Evaluate a vector's &#x201c;magnitude&#x201d; through a metric. This assumes an actual
--   mathematical metric, i.e. positive definite &#x2013; otherwise the internally used
--   square root may get negative arguments (though it can still produce results if the
--   scalars are complex; however, complex spaces aren't supported yet).
metric :: HasMetric v => HerMetric v -> v -> Scalar v
metric (HerMetric m) v = sqrt $ lapply m v <.>^ v

metric' :: HasMetric v => HerMetric' v -> DualSpace v -> Scalar v
metric' (HerMetric' m) u = sqrt $ lapply m u ^<.> u

metriScale :: HasMetric v => HerMetric v -> v -> v
metriScale m v = metric m v *^ v


-- | Square-sum over the metrics for each dual-space vector.
-- 
-- @
-- metrics m vs &#x2261; sqrt . sum $ metricSq m '<$>' vs
-- @
metrics :: HasMetric v => HerMetric v -> [v] -> Scalar v
metrics m vs = sqrt . sum $ metricSq m <$> vs

metrics' :: HasMetric v => HerMetric' v -> [DualSpace v] -> Scalar v
metrics' m vs = sqrt . sum $ metricSq' m <$> vs


transformMetric :: (HasMetric v, HasMetric w, Scalar v ~ Scalar w)
           => (w :-* v) -> HerMetric v -> HerMetric w
transformMetric t (HerMetric m) = HerMetric $ adjoint t *.* m *.* t

transformMetric' :: ( HasMetric v, HasMetric w, Scalar v ~ Scalar w )
           => (v :-* w) -> HerMetric' v -> HerMetric' w
transformMetric' t (HerMetric' m)
    = HerMetric' $ t *.* m *.* adjoint t

dualiseMetric :: (HasMetric v, HasMetric (DualSpace v))
      => HerMetric (DualSpace v) -> HerMetric' v
dualiseMetric (HerMetric m) = HerMetric' $ linear doubleDual' *.* m

dualiseMetric' :: (HasMetric v, HasMetric (DualSpace v))
      => HerMetric' v -> HerMetric (DualSpace v)
dualiseMetric' (HerMetric' m) = HerMetric $ linear doubleDual *.* m


-- | While the main purpose of this class is to express 'HerMetric', it's actually
--   all about dual spaces.
class ( HasBasis v, RealFloat (Scalar v), HasTrie (Basis v)
      , VectorSpace (DualSpace v), HasBasis (DualSpace v)
      , Scalar v ~ Scalar (DualSpace v), Basis v ~ Basis (DualSpace v) )
    => HasMetric v where
        
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
  --   the tuple instance actually assumes this to be able to offer an efficient
  --   implementation (namely, 'id') of the isomorphisms.
  doubleDual :: HasMetric (DualSpace v) => v -> DualSpace (DualSpace v)
  doubleDual' :: HasMetric (DualSpace v) => DualSpace (DualSpace v) -> v
  
  

-- | Simple flipped version of '<.>^'.
(^<.>) :: HasMetric v => v -> DualSpace v -> Scalar v
ket ^<.> bra = bra <.>^ ket

instance HasMetric Double where
  (<.>^) = (<.>)
  functional f = f 1
  doubleDual = id; doubleDual'= id
instance ( HasMetric v, HasMetric w, Scalar v ~ Scalar w
         , HasMetric (DualSpace v), DualSpace (DualSpace v) ~ v
         , HasMetric (DualSpace w), DualSpace (DualSpace w) ~ w
         ) => HasMetric (v,w) where
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

