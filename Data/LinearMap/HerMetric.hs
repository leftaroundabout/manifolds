{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE ConstraintKinds            #-}




module Data.LinearMap.HerMetric (
    HerMetric
  , projector
  , metricSq, metric, metrics
  , metriScale
  , transformMetric
  , HasMetric(..)
  , (^<.>)
  ) where
    

    

import Data.VectorSpace
import Data.LinearMap
import Data.Basis
import Data.MemoTrie

import Control.Applicative
    


infixr 7 <.>^, ^<.>


-- | 'HerMetric' is a portmanteau of /Hermitian/ and /metric/, the latter in the sense as
--   used in e.g. general relativity (though those particular ones aren't positive
--   definite and thus not really metrics).
-- 
--   Mathematically, there are two directly equivalent ways to describe such a metric:
--   as a bilinear mapping of two vectors to a scalar, or as a linear mapping from
--   a vector space to its dual space. In this module, we actually define it as a
--   mapping from the dual space to the space itself (so basically, it is a metric
--   /on the dual space/; it turns out this is a bit more convenient for some applications;
--   in Hilbert spaces, the dual space is represented as the space itself anyway).
newtype HerMetric v = HerMetric { getHerMetric :: DualSpace v :-* v }

instance HasMetric v => AdditiveGroup (HerMetric v) where
  zeroV = HerMetric zeroV
  negateV (HerMetric m) = HerMetric $ negateV m
  HerMetric m ^+^ HerMetric n = HerMetric $ m ^+^ n
instance HasMetric v => VectorSpace (HerMetric v) where
  type Scalar (HerMetric v) = Scalar v
  s *^ (HerMetric m) = HerMetric $ s *^ m 

-- | A metric on @'DualSpace' v@ that simply yields the squared overlap of a dual
--   vector with the given reference.
projector :: HasMetric v => v -> HerMetric v
projector v = HerMetric (linear $ \u -> v ^* (v^<.>u))



-- | Evaluate a (dual) vector through a metric. For the canonical metric on a Hilbert space,
--   this will be simply 'magnitudeSq'.
metricSq :: HasMetric v => HerMetric v -> DualSpace v -> Scalar v
metricSq (HerMetric m) v = v <.>^ lapply m v

-- | Evaluate a vector's magnitude through a metric. This assumes an actual mathematical
--   metric, i.e. positive definite &#x2013; otherwise the internally used square root may
--   get negative arguments (though it can still produce results if the scalars are complex).
metric :: HasMetric v => HerMetric v -> DualSpace v -> Scalar v
metric (HerMetric m) v = sqrt $ v <.>^ lapply m v


metriScale :: HasMetric v => HerMetric v -> DualSpace v -> DualSpace v
metriScale m v = metric m v *^ v


-- | Square-sum over the metrics for each dual-space vector.
-- 
-- @
-- metrics m vs &#x2261; sqrt . sum $ metricSq m '<$>' vs
-- @
metrics :: HasMetric v => HerMetric v -> [DualSpace v] -> Scalar v
metrics m vs = sqrt . sum $ metricSq m <$> vs



transformMetric :: (HasMetric v, HasMetric w, Scalar v ~ Scalar w)
           => (v:-*w) -> HerMetric v -> HerMetric w
transformMetric t (HerMetric m) = HerMetric $ t *.* m *.* adjoint t



class ( HasBasis v, RealFloat (Scalar v), HasTrie (Basis v)
      , VectorSpace (DualSpace v), HasBasis (DualSpace v)
      , Scalar v ~ Scalar (DualSpace v), Basis v ~ Basis (DualSpace v) )
    => HasMetric v where
  type DualSpace v :: *
  type DualSpace v = v
  (<.>^) :: DualSpace v -> v -> Scalar v
  adjoint :: (HasMetric w, Scalar w ~ Scalar v)
       => (v:-*w) -> DualSpace w :-* DualSpace v
  

(^<.>) :: HasMetric v => v -> DualSpace v -> Scalar v
ket ^<.> bra = bra <.>^ ket

instance HasMetric Double where
  (<.>^) = (<.>)
  adjoint m = linear (<.>^ lapply m 1)
instance (HasMetric v, HasMetric w, Scalar v ~ Scalar w) => HasMetric (v,w) where
  type DualSpace (v,w) = (DualSpace v, DualSpace w)
  (v,w)<.>^(v',w') = v<.>^v' + w<.>^w'
  adjoint m = linear
     $ \xd -> ( lapply (adjoint $ linear $ lapply m . (,zeroV)) xd
              , lapply (adjoint $ linear $ lapply m . (zeroV,)) xd )






