{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE UndecidableInstances     #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE FunctionalDependencies   #-}
{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE RankNTypes               #-}
{-# LANGUAGE TupleSections            #-}
{-# LANGUAGE ConstraintKinds          #-}
{-# LANGUAGE PatternGuards            #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE ScopedTypeVariables      #-}
{-# LANGUAGE RecordWildCards          #-}
{-# LANGUAGE CPP                      #-}


module Data.Manifold.PseudoAffine where
    


import Data.List
import Data.Maybe
import Data.Semigroup
import Data.Function (on)

import Data.VectorSpace
import Data.AffineSpace
import Data.Basis
import Data.Complex hiding (magnitude)
import Data.Void
import Data.Manifold.Types

import qualified Prelude

import Control.Category.Constrained.Prelude hiding ((^))
import Control.Arrow.Constrained
import Control.Monad.Constrained
import Data.Foldable.Constrained




infix 6 .-~.
infixl 6 .+~^

-- | 'PseudoAffine' is intended as an alternative class for 'Manifold's. The interface
--   is actually identical to the better-known 'AffineSpace' class, but unlike in the
--   standard mathematical definition of affine spaces we don't require associativity of
--   '.+~^' with '^+^', except in an asymptotic sense for small vectors.
--   
--   That innocent-looking change makes the class applicable to vastly more general types:
--   while an affine space is basically nothing but a vector space without particularly
--   designated origin, a pseudo-affine space can have nontrivial topology on the global
--   scale, and yet be used in practically the same way as an affine space. At least the
--   usual spheres and tori make good instances, perhaps the class is in fact equivalent to
--   /parallelisable path-connected manifolds/.
class PseudoAffine x where
  type PseudoDiff x :: *
  (.-~.) :: x -> x -> PseudoDiff x
  (.+~^) :: x -> PseudoDiff x -> x


palerp :: (PseudoAffine x, VectorSpace (PseudoDiff x))
    => x -> x -> Scalar (PseudoDiff x) -> x
palerp p1 p2 = \t -> p1 .+~^ t *^ v
 where v = p2 .-~. p1



#define deriveAffine(t)          \
instance PseudoAffine t where {   \
  type PseudoDiff t = Diff t;      \
  (.-~.) = (.-.);                   \
  (.+~^) = (.+^)  }

deriveAffine(Double)
deriveAffine(Rational)

instance (PseudoAffine a, PseudoAffine b) => PseudoAffine (a,b) where
  type PseudoDiff (a,b) = (PseudoDiff a, PseudoDiff b)
  (a,b).-~.(c,d) = (a.-~.c, b.-~.d)
  (a,b).+~^(v,w) = (a.+~^v, b.+~^w)
instance (PseudoAffine a, PseudoAffine b, PseudoAffine c) => PseudoAffine (a,b,c) where
  type PseudoDiff (a,b,c) = (PseudoDiff a, PseudoDiff b, PseudoDiff c)
  (a,b,c).-~.(d,e,f) = (a.-~.d, b.-~.e, c.-~.f)
  (a,b,c).+~^(v,w,x) = (a.+~^v, b.+~^w, c.+~^x)


instance PseudoAffine S¹ where
  type PseudoDiff S¹ = ℝ
  S¹ φ₁ .-~. S¹ φ₂
     | δφ > pi     = δφ - 2*pi
     | δφ < (-pi)  = δφ + 2*pi
     | otherwise   = δφ
   where δφ = φ₂ - φ₁
  S¹ φ₀ .+~^ δφ
     | φ' < 0     = S¹ $ φ' + 2*pi
     | φ' > 2*pi  = S¹ $ φ' - 2*pi
     | otherwise  = S¹ $ φ'
   where φ' = φ₀ + δφ
