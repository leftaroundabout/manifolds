-- |
-- Module      : Data.Manifold.Types
-- Copyright   : (c) Justus Sagemüller 2015
-- License     : GPL v3
-- 
-- Maintainer  : (@) sagemueller $ geo.uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 
-- Several commonly-used manifolds, represented in some simple way as Haskell
-- data types. All these are in the 'PseudoAffine' class.


{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE UndecidableInstances     #-}
{-# LANGUAGE CPP                      #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE FunctionalDependencies   #-}
{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE LiberalTypeSynonyms      #-}
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE RankNTypes               #-}
{-# LANGUAGE TupleSections            #-}
{-# LANGUAGE MultiWayIf               #-}
{-# LANGUAGE ConstraintKinds          #-}
{-# LANGUAGE PatternGuards            #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE ScopedTypeVariables      #-}
{-# LANGUAGE RecordWildCards          #-}


module Data.Manifold.Types (
        -- * Index / ASCII names
          Real0, Real1, RealPlus, Real2, Real3
        , Sphere0, Sphere1, Sphere2
        , Projective1, Projective2
        , Disk1, Disk2, Cone, OpenCone
        -- * Linear manifolds
        , ZeroDim(..)
        , ℝ⁰, ℝ, ℝ², ℝ³
        -- * Hyperspheres
        -- ** General form: Stiefel manifolds
        , Stiefel1, stiefel1Project, stiefel1Embed
        -- ** Specific examples
        , HasUnitSphere(..)
        , S⁰(..), S¹(..), S²(..)
        -- * Projective spaces
        , ℝP¹,  ℝP²(..)
        -- * Intervals\/disks\/cones
        , D¹(..), D²(..)
        , ℝay
        , CD¹(..), Cℝay(..)
        -- * Misc
        -- * Cut-planes
        , Cutplane(..)
        , fathomCutDistance, sideOfCut
   ) where


import Data.VectorSpace
import Data.AffineSpace
import Data.MemoTrie (HasTrie(..))
import Data.Basis
import Data.Fixed
import Data.Void
import Data.Tagged
import Data.Monoid
import Data.Semigroup
import qualified Numeric.LinearAlgebra.HMatrix as HMat
import qualified Data.Vector.Generic as Arr
import qualified Data.Vector

import Data.Manifold.Types.Primitive
import Data.Manifold.PseudoAffine
import Data.LinearMap.HerMetric
import Data.VectorSpace.FiniteDimensional

import qualified Prelude

import Control.Category.Constrained.Prelude hiding ((^))
import Control.Arrow.Constrained
import Control.Monad.Constrained
import Data.Foldable.Constrained

#define deriveAffine(c,t)                \
instance (c) => Semimanifold (t) where {  \
  type Needle (t) = Diff (t);              \
  (.+~^) = (.+^) };                         \
instance (c) => PseudoAffine (t) where {     \
  a.-~.b = pure (a.-.b);      }


-- | The /n/-th Stiefel manifold is the space of all possible configurations of
--   /n/ orthonormal vectors. In the case /n/ = 1, simply the subspace of normalised
--   vectors, i.e. equivalent to the 'UnitSphere'. Even so, it strictly speaking
--   requires the containing space to be at least metric (if not Hilbert); we would
--   however like to be able to use this concept also in spaces with no inner product,
--   therefore we define this space not as normalised vectors, but rather as all
--   vectors modulo scaling by positive factors.
newtype Stiefel1 v = Stiefel1 { getStiefel1N :: DualSpace v }

newtype Stiefel1Needle v = Stiefel1Needle { getStiefel1Tangent :: HMat.Vector (Scalar v) }
newtype Stiefel1Basis v = Stiefel1Basis { getStiefel1Basis :: Int }
s1bTrie :: forall v b. FiniteDimensional v => (Stiefel1Basis v->b) -> Stiefel1Basis v:->:b
s1bTrie = \f -> St1BTrie $ fmap (f . Stiefel1Basis) allIs
 where (Tagged d) = dimension :: Tagged v Int
       allIs = Arr.fromList [0 .. d-2]

instance FiniteDimensional v => HasTrie (Stiefel1Basis v) where
  data (Stiefel1Basis v :->: a) = St1BTrie ( Array a )
  trie = s1bTrie; untrie (St1BTrie a) (Stiefel1Basis i) = a Arr.! i
  enumerate (St1BTrie a) = Arr.ifoldr (\i x l -> (Stiefel1Basis i,x):l) [] a

type Array = Data.Vector.Vector

instance(SmoothScalar(Scalar v),FiniteDimensional v)=>AdditiveGroup(Stiefel1Needle v) where
  Stiefel1Needle v ^+^ Stiefel1Needle w = Stiefel1Needle $ v + w
  zeroV = s1nZ; negateV (Stiefel1Needle v) = Stiefel1Needle $ negate v
s1nZ :: forall v. FiniteDimensional v => Stiefel1Needle v
s1nZ=Stiefel1Needle .HMat.fromList$replicate(d-1)0 where(Tagged d)=dimension::Tagged v Int

instance (SmoothScalar(Scalar v),FiniteDimensional v)=>VectorSpace(Stiefel1Needle v) where
  type Scalar (Stiefel1Needle v) = Scalar v
  μ *^ Stiefel1Needle v = Stiefel1Needle $ HMat.scale μ v

instance (SmoothScalar (Scalar v), FiniteDimensional v)=>HasBasis (Stiefel1Needle v) where
  type Basis (Stiefel1Needle v) = Stiefel1Basis v
  basisValue = s1bV
  decompose (Stiefel1Needle v) = zipWith ((,).Stiefel1Basis) [0..] $ HMat.toList v
  decompose' (Stiefel1Needle v) (Stiefel1Basis i) = v HMat.! i
s1bV :: forall v b. FiniteDimensional v => Stiefel1Basis v -> Stiefel1Needle v
s1bV = \(Stiefel1Basis i) -> Stiefel1Needle
            $ HMat.fromList [ if k==i then 1 else 0 | k<-[0..d-2] ]
 where (Tagged d) = dimension :: Tagged v Int

instance (SmoothScalar (Scalar v), FiniteDimensional v)
             => FiniteDimensional (Stiefel1Needle v) where
  dimension = s1nD
  basisIndex = Tagged $ \(Stiefel1Basis i) -> i
  indexBasis = Tagged Stiefel1Basis
  fromPackedVector = Stiefel1Needle
  asPackedVector = getStiefel1Tangent
s1nD :: forall v. FiniteDimensional v => Tagged (Stiefel1Needle v) Int
s1nD = Tagged (d - 1) where (Tagged d) = dimension :: Tagged v Int

instance (SmoothScalar (Scalar v), FiniteDimensional v)
             => AffineSpace (Stiefel1Needle v) where
  type Diff (Stiefel1Needle v) = Stiefel1Needle v
  (.+^) = (^+^)
  (.-.) = (^-^)

deriveAffine((SmoothScalar (Scalar v), FiniteDimensional v), Stiefel1Needle v)

instance (MetricScalar (Scalar v), FiniteDimensional v)
              => HasMetric' (Stiefel1Needle v) where
  type DualSpace (Stiefel1Needle v) = Stiefel1Needle v
  Stiefel1Needle v <.>^ Stiefel1Needle w = HMat.dot v w 
  functional = s1nF
  doubleDual = id; doubleDual' = id
s1nF :: forall v. FiniteDimensional v => (Stiefel1Needle v->Scalar v)->Stiefel1Needle v
s1nF = \f -> Stiefel1Needle $ HMat.fromList [f $ basisValue b | b <- cb]
 where (Tagged cb) = completeBasis :: Tagged (Stiefel1Needle v) [Stiefel1Basis v]

instance (WithField k LinearManifold v, Real k) => Semimanifold (Stiefel1 v) where 
  type Needle (Stiefel1 v) = Stiefel1Needle v
  Stiefel1 s .+~^ Stiefel1Needle n = Stiefel1 . fromPackedVector . HMat.scale (signum s'i)
   $ if| ν==0      -> s' -- ν'≡0 is a special case of this, so we can otherwise assume ν'>0.
-- --  | ν<=1      -> let -- κ = (-1 − 1/(ν−1)) / ν'
--                        -- m ∝         spro +         κ · n
--                        --   ∝ (1−ν) · spro + (1−ν) · κ · n
--                        --   = (1−ν) · spro + (-(1−ν) − -1)/ν' · n
--                        m = HMat.scale (1-ν) spro + HMat.scale (ν/ν') n
--                    in insi (1-ν) m
       | ν<=2      -> let -- κ = (1/(ν−1) − 1) / ν'
                          -- m ∝       - spro +         κ · n
                          --   ∝ (1−ν) · spro + (ν−1) · κ · n
                          --   = (1−ν) · spro + (1 − (ν−1))/ν' · n
                          m = HMat.scale ιmν spro + HMat.scale ((1-abs ιmν)/ν') n
                          ιmν = 1-ν 
                      in insi ιmν m
       | otherwise -> let m = HMat.scale ιmν spro + HMat.scale ((abs ιmν-1)/ν') n
                          ιmν = ν-3
                      in insi ιmν m
   where d = HMat.size s'
         s'= asPackedVector s
         ν' = l2norm n
         quop = signum s'i / ν'
         ν = ν' `mod'` 4
         im = HMat.maxIndex $ HMat.cmap abs s'
         s'i = s' HMat.! im
         spro = let v = deli s' in HMat.scale (recip s'i) v
         deli v = Arr.take im v Arr.++ Arr.drop (im+1) v
         insi ti v = Arr.generate d $ \i -> if | i<im      -> v Arr.! i
                                               | i>im      -> v Arr.! (i-1) 
                                               | otherwise -> ti
instance (WithField k LinearManifold v, Real k) => PseudoAffine (Stiefel1 v) where 
  Stiefel1 s .-~. Stiefel1 t = pure . Stiefel1Needle $ case s' HMat.! im of
            0 -> HMat.scale (recip $ l2norm delis) delis
            s'i | v <- HMat.scale (recip s'i) delis - tpro
                , absv <- l2norm v
                , absv > 0
                       -> let μ -- = (1 − recip (|v| + 1)) / |v| for sgn sᵢ = sgn tᵢ
                                   = (signum (t'i/s'i) - recip(absv + 1)) / absv
                          in HMat.scale μ v
                | t'i/s'i > 0  -> samePoint
                | otherwise    -> antipode
   where d = HMat.size t'
         s'= asPackedVector s; t' = asPackedVector t
         im = HMat.maxIndex $ HMat.cmap abs t'
         t'i = t' HMat.! im
         tpro = let v = deli t' in HMat.scale (recip t'i) v
         delis = deli s'
         deli v = Arr.take im v Arr.++ Arr.drop (im+1) v
         samePoint = (d-1) HMat.|> repeat 0
         antipode = (d-1) HMat.|> (2 : repeat 0)

l2norm :: MetricScalar s => HMat.Vector s -> s
l2norm = realToFrac . HMat.norm_2


stiefel1Project :: LinearManifold v =>
             DualSpace v       -- ^ Must be nonzero.
                 -> Stiefel1 v
stiefel1Project = Stiefel1

stiefel1Embed :: HilbertSpace v => Stiefel1 v -> v
stiefel1Embed (Stiefel1 n) = normalized n
  

class (PseudoAffine v, InnerSpace v, NaturallyEmbedded (UnitSphere v) (DualSpace v))
          => HasUnitSphere v where
  type UnitSphere v :: *
  stiefel :: UnitSphere v -> Stiefel1 v
  stiefel = Stiefel1 . embed
  unstiefel :: Stiefel1 v -> UnitSphere v
  unstiefel = coEmbed . getStiefel1N

instance HasUnitSphere ℝ  where type UnitSphere ℝ  = S⁰
instance HasUnitSphere ℝ² where type UnitSphere ℝ² = S¹
instance HasUnitSphere ℝ³ where type UnitSphere ℝ³ = S²

instance (HasUnitSphere v, v ~ DualSpace v) => NaturallyEmbedded (Stiefel1 v) v where
  embed = embed . unstiefel
  coEmbed = stiefel . coEmbed






-- | Oriented hyperplanes, na&#xef;vely generalised to 'PseudoAffine' manifolds:
--   @'Cutplane' p w@ represents the set of all points 'q' such that
--   @(q.-~.p) ^\<.\> w &#x2261; 0@.
-- 
--   In vector spaces this is indeed a hyperplane; for general manifolds it should
--   behave locally as a plane, globally as an (/n/−1)-dimensional submanifold.
data Cutplane x = Cutplane { sawHandle :: x
                           , cutNormal :: Stiefel1 (Needle x) }



sideOfCut :: WithField ℝ Manifold x => Cutplane x -> x -> Option S⁰
sideOfCut (Cutplane sh (Stiefel1 cn)) p = decideSide . (cn<.>^) =<< p .-~. sh
 where decideSide 0 = mzero
       decideSide μ | μ > 0      = pure PositiveHalfSphere
                    | otherwise  = pure NegativeHalfSphere


fathomCutDistance :: WithField ℝ Manifold x
        => Cutplane x            -- ^ Hyperplane to measure the distance from.
         -> HerMetric'(Needle x) -- ^ Metric to use for measuring that distance.
                                 --   This can only be accurate if the metric
                                 --   is valid both around the cut-plane's 'sawHandle', and
                                 --   around the points you measure.
                                 --   (Strictly speaking, we would need /parallel transport/
                                 --   to ensure this).
         -> x                    -- ^ Point to measure the distance to.
         -> Option ℝ             -- ^ A signed number, giving the distance from plane
                                 --   to point with indication on which side the point lies.
                                 --   'Nothing' if the point isn't reachable from the plane.
fathomCutDistance (Cutplane sh (Stiefel1 cn)) met = \x -> fmap fathom $ x .-~. sh
 where fathom v = (cn <.>^ v) / scaleDist
       scaleDist = metric' met cn
          

