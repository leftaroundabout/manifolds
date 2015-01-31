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
  , adjoint
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

-- | A metric on @v@ that simply yields the squared overlap of a vector with the
--   given dual-space reference.
--   
--   It will perhaps be the most common way of defining 'Hermetric' values to start
--   with such dual-space vectors and superimpose the projectors using the 'VectorSpace'
--   instance; e.g. @projector (1,0) '^+^' projector (0,2)@ yields a hermitian operator
--   describing the ellipsoid span of the vectors /e/&#x2080; and 2&#x22c5;/e/&#x2081;.
--   Metrics generated this way are always positive definite.
projector :: HasMetric v => DualSpace v -> HerMetric v
projector u = HerMetric (linear $ \v -> u ^* (u<.>^v))



-- | Evaluate a (dual) vector through a metric. For the canonical metric on a Hilbert space,
--   this will be simply 'magnitudeSq'.
metricSq :: HasMetric v => HerMetric v -> v -> Scalar v
metricSq (HerMetric m) v = lapply m v <.>^ v

-- | Evaluate a vector's magnitude through a metric. This assumes an actual mathematical
--   metric, i.e. positive definite &#x2013; otherwise the internally used square root may
--   get negative arguments (though it can still produce results if the scalars are complex).
metric :: HasMetric v => HerMetric v -> v -> Scalar v
metric (HerMetric m) v = sqrt $ lapply m v <.>^ v


metriScale :: HasMetric v => HerMetric v -> v -> v
metriScale m v = metric m v *^ v


-- | Square-sum over the metrics for each dual-space vector.
-- 
-- @
-- metrics m vs &#x2261; sqrt . sum $ metricSq m '<$>' vs
-- @
metrics :: HasMetric v => HerMetric v -> [v] -> Scalar v
metrics m vs = sqrt . sum $ metricSq m <$> vs



transformMetric :: (HasMetric v, HasMetric w, Scalar v ~ Scalar w)
           => (w :-* v) -> HerMetric v -> HerMetric w
transformMetric t (HerMetric m) = HerMetric $ adjoint t *.* m *.* t



-- | While the main purpose of this class is to express 'HerMetric', it's actually
--   all about dual spaces.
class ( HasBasis v, RealFloat (Scalar v), HasTrie (Basis v)
      , VectorSpace (DualSpace v), HasBasis (DualSpace v)
      , Scalar v ~ Scalar (DualSpace v), Basis v ~ Basis (DualSpace v) )
    => HasMetric v where
        
  -- | @'DualSpace' v@ is isomorphic to @v :-* Scalar v@. Typically (for all Hilbert- /
  --   'InnerSpace's) this is in turn isomorphic to @v@ itself, which will be rather more
  --   efficient (hence the distinction between a vector space and its dual is often
  --   neglected or reduced to &#x201c;column vs row vectors&#x201d;. Mathematically though,
  --   it makes sense to keep the concepts apart, even if ultimately @'DualSpace' v ~ v@
  --   (which need /not/ always be the case, though!).
  type DualSpace v :: *
  type DualSpace v = v
      
  -- | Apply a dual space vector (aka linear functional) to a vector.
  (<.>^) :: DualSpace v -> v -> Scalar v
            
  -- | Interpret a functional as a dual-space vector. Like 'linear', this /assumes/
  --   (completely unchecked) that the supplied function is linear.
  functional :: (v -> Scalar v) -> DualSpace v
  
  

-- | Simple flipped version of '<.>^'.
(^<.>) :: HasMetric v => v -> DualSpace v -> Scalar v
ket ^<.> bra = bra <.>^ ket

instance HasMetric Double where
  (<.>^) = (<.>)
  functional f = f 1
instance (HasMetric v, HasMetric w, Scalar v ~ Scalar w) => HasMetric (v,w) where
  type DualSpace (v,w) = (DualSpace v, DualSpace w)
  (v,w)<.>^(v',w') = v<.>^v' + w<.>^w'
  functional f = (functional $ f . (,zeroV), functional $ f . (zeroV,))





-- | Transpose a linear operator. Contrary to popular belief, this does not
--   just inverse the direction of mapping between the spaces, but also switch to
--   their duals.
adjoint :: (HasMetric v, HasMetric w, Scalar w ~ Scalar v)
     => (v :-* w) -> DualSpace w :-* DualSpace v
adjoint m = linear $ \w -> functional $ \v
                     -> w <.>^lapply m v

