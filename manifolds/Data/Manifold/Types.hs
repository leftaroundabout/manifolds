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
{-# LANGUAGE StandaloneDeriving       #-}
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE RankNTypes               #-}
{-# LANGUAGE TupleSections            #-}
{-# LANGUAGE MultiWayIf               #-}
{-# LANGUAGE ConstraintKinds          #-}
{-# LANGUAGE PatternGuards            #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE ScopedTypeVariables      #-}
{-# LANGUAGE UnicodeSyntax            #-}


module Data.Manifold.Types (
        -- * Index / ASCII names
          Real0, Real1, RealPlus, Real2, Real3
        , Sphere0, Sphere1, Sphere2
        , Projective0, Projective1, Projective2
        , Disk1, Disk2, Cone, OpenCone
        , FibreBundle(..), TangentBundle
        -- * Linear manifolds
        , ZeroDim(..)
        , ℝ, ℝ⁰, ℝ¹, ℝ², ℝ³, ℝ⁴
        -- * Hyperspheres
        -- ** General form: Stiefel manifolds
        , Stiefel1(..), stiefel1Project, stiefel1Embed
        -- ** Specific examples
        , HasUnitSphere(..)
        , S⁰(..), S¹(..), S²(..)
        -- * Projective spaces
        , ℝP⁰(..), ℝP¹(..),  ℝP²(..)
        -- * Intervals\/disks\/cones
        , D¹(..), D²(..)
        , ℝay
        , CD¹(..), Cℝay(..)
        -- * Affine subspaces
        -- ** Lines
        , Line(..), lineAsPlaneIntersection
        -- ** Hyperplanes
        , Cutplane(..), normalPlane
        , fathomCutDistance, sideOfCut, cutPosBetween
        -- * Linear mappings
        , LinearMap, LocalLinear
        -- * Misc
        , StiefelScalar
   ) where


import Data.VectorSpace
import Data.VectorSpace.Free
import Data.AffineSpace
import Data.MemoTrie (HasTrie(..))
import Data.Basis
import Data.Fixed
import Data.Tagged
import qualified Data.Vector.Generic as Arr
import qualified Data.Vector
import qualified Data.Vector.Unboxed as UArr
import Data.List (maximumBy)
import Data.Ord (comparing)

import Data.Manifold.Types.Primitive
import Data.Manifold.Types.Stiefel
import Data.Manifold.PseudoAffine
import Data.Manifold.Cone
import Math.LinearMap.Category

import qualified Prelude
import qualified Data.Traversable as Hask

import Control.Category.Constrained.Prelude hiding ((^))
import Control.Arrow.Constrained
import Control.Monad.Constrained
import Data.Foldable.Constrained

import Data.Type.Coercion

type StiefelScalar s = (RealFloat s, UArr.Unbox s)

#define deriveAffine(c,t)                \
instance (c) => Semimanifold (t) where {  \
  type Needle (t) = Diff (t);              \
  fromInterior = id;                        \
  toInterior = pure;                         \
  translateP = Tagged (.+~^);                 \
  (.+~^) = (.+^) };                            \
instance (c) => PseudoAffine (t) where {        \
  a.-~.b = pure (a.-.b);      }


newtype Stiefel1Needle v = Stiefel1Needle { getStiefel1Tangent :: UArr.Vector (Scalar v) }
deriving instance (Eq (Scalar v), UArr.Unbox (Scalar v)) => Eq (Stiefel1Needle v)
newtype Stiefel1Basis v = Stiefel1Basis { getStiefel1Basis :: Int }
s1bTrie :: ∀ v b. FiniteFreeSpace v => (Stiefel1Basis v->b) -> Stiefel1Basis v:->:b
s1bTrie = \f -> St1BTrie $ fmap (f . Stiefel1Basis) allIs
 where d = freeDimension ([]::[v])
       allIs = Arr.fromList [0 .. d-2]

instance FiniteFreeSpace v => HasTrie (Stiefel1Basis v) where
  data (Stiefel1Basis v :->: a) = St1BTrie ( Array a )
  trie = s1bTrie; untrie (St1BTrie a) (Stiefel1Basis i) = a Arr.! i
  enumerate (St1BTrie a) = Arr.ifoldr (\i x l -> (Stiefel1Basis i,x):l) [] a

type Array = Data.Vector.Vector

instance (FiniteFreeSpace v, UArr.Unbox (Scalar v))
                        => AdditiveGroup(Stiefel1Needle v) where
  Stiefel1Needle v ^+^ Stiefel1Needle w = Stiefel1Needle $ uarrAdd v w
  Stiefel1Needle v ^-^ Stiefel1Needle w = Stiefel1Needle $ uarrSubtract v w
  zeroV = s1nZ; negateV (Stiefel1Needle v) = Stiefel1Needle $ UArr.map negate v

uarrAdd :: (Num n, UArr.Unbox n) => UArr.Vector n -> UArr.Vector n -> UArr.Vector n
uarrAdd = UArr.zipWith (+)
uarrSubtract :: (Num n, UArr.Unbox n) => UArr.Vector n -> UArr.Vector n -> UArr.Vector n
uarrSubtract = UArr.zipWith (-)

s1nZ :: ∀ v. (FiniteFreeSpace v, UArr.Unbox (Scalar v)) => Stiefel1Needle v
s1nZ = Stiefel1Needle . UArr.fromList $ replicate (d-1) 0
 where d = freeDimension ([]::[v])

instance (FiniteFreeSpace v, UArr.Unbox (Scalar v)) => VectorSpace (Stiefel1Needle v) where
  type Scalar (Stiefel1Needle v) = Scalar v
  μ *^ Stiefel1Needle v = Stiefel1Needle $ uarrScale μ v

uarrScale :: (Num n, UArr.Unbox n) => n -> UArr.Vector n -> UArr.Vector n
uarrScale μ = UArr.map (*μ)

instance (FiniteFreeSpace v, UArr.Unbox (Scalar v)) => HasBasis (Stiefel1Needle v) where
  type Basis (Stiefel1Needle v) = Stiefel1Basis v
  basisValue = s1bV
  decompose (Stiefel1Needle v) = zipWith ((,).Stiefel1Basis) [0..] $ UArr.toList v
  decompose' (Stiefel1Needle v) (Stiefel1Basis i) = v UArr.! i

s1bV :: ∀ v b. (FiniteFreeSpace v, UArr.Unbox (Scalar v))
                  => Stiefel1Basis v -> Stiefel1Needle v
s1bV = \(Stiefel1Basis i) -> Stiefel1Needle
            $ UArr.fromList [ if k==i then 1 else 0 | k<-[0..d-2] ]
 where d = freeDimension ([]::[v])

instance (FiniteFreeSpace v, UArr.Unbox (Scalar v))
                      => FiniteFreeSpace (Stiefel1Needle v) where
  freeDimension = s1nD
  toFullUnboxVect = getStiefel1Tangent
  unsafeFromFullUnboxVect = Stiefel1Needle
s1nD :: ∀ v p . FiniteFreeSpace v => p (Stiefel1Needle v) -> Int
s1nD _ = freeDimension ([]::[v]) - 1

instance (FiniteFreeSpace v, UArr.Unbox (Scalar v)) => AffineSpace (Stiefel1Needle v) where
  type Diff (Stiefel1Needle v) = Stiefel1Needle v
  (.+^) = (^+^)
  (.-.) = (^-^)

deriveAffine((FiniteFreeSpace v, UArr.Unbox (Scalar v)), Stiefel1Needle v)

instance ∀ v . (LSpace v, FiniteFreeSpace v, Eq (Scalar v), UArr.Unbox (Scalar v))
              => TensorSpace (Stiefel1Needle v) where
  type TensorProduct (Stiefel1Needle v) w = Array w
  scalarSpaceWitness = case scalarSpaceWitness :: ScalarSpaceWitness v of
         ScalarSpaceWitness -> ScalarSpaceWitness
  linearManifoldWitness = LinearManifoldWitness BoundarylessWitness
  zeroTensor = Tensor $ Arr.replicate (freeDimension ([]::[v]) - 1) zeroV
  toFlatTensor = LinearFunction $ Tensor . Arr.convert . getStiefel1Tangent
  fromFlatTensor = LinearFunction $ Stiefel1Needle . Arr.convert . getTensorProduct
  addTensors (Tensor a) (Tensor b) = Tensor $ Arr.zipWith (^+^) a b
  scaleTensor = bilinearFunction $ \μ (Tensor a) -> Tensor $ Arr.map (μ*^) a
  negateTensor = LinearFunction $ \(Tensor a) -> Tensor $ Arr.map negateV a
  tensorProduct = bilinearFunction $ \(Stiefel1Needle n) w
                        -> Tensor $ Arr.map (*^w) $ Arr.convert n
  transposeTensor = LinearFunction $ \(Tensor a) -> Arr.foldl' (^+^) zeroV
       $ Arr.imap ( \i w -> (getLinearFunction tensorProduct w) $ Stiefel1Needle
                             $ UArr.generate d (\j -> if i==j then 1 else 0) ) a
   where d = freeDimension ([]::[v]) - 1
  fmapTensor = bilinearFunction $ \f (Tensor a) -> Tensor $ Arr.map (f$) a
  fzipTensorWith = bilinearFunction $ \f (Tensor a, Tensor b)
                     -> Tensor $ Arr.zipWith (curry $ arr f) a b
  coerceFmapTensorProduct _ Coercion = Coercion
  wellDefinedTensor (Tensor a) = Tensor <$> Hask.traverse wellDefinedVector a

asTensor :: Coercion (LinearMap s a b) (Tensor s (DualVector a) b)
asTensor = Coercion
asLinearMap :: Coercion (Tensor s (DualVector a) b) (LinearMap s a b)
asLinearMap = Coercion
infixr 0 +$>
(+$>) :: (LinearSpace a, TensorSpace b, Scalar a ~ s, Scalar b ~ s)
            => LinearMap s a b -> a -> b
(+$>) = getLinearFunction . getLinearFunction applyLinear
  
instance ∀ v . (LSpace v, FiniteFreeSpace v, Eq (Scalar v), UArr.Unbox (Scalar v))
              => LinearSpace (Stiefel1Needle v) where
  type DualVector (Stiefel1Needle v) = Stiefel1Needle v
  linearId = LinearMap . Arr.generate d $ \i -> Stiefel1Needle . Arr.generate d $
                                           \j -> if i==j then 1 else 0
   where d = freeDimension ([]::[v]) - 1
  tensorId = ti dualSpaceWitness
   where ti :: ∀ w . (LinearSpace w, Scalar w ~ Scalar v)
           => DualSpaceWitness w -> (Stiefel1Needle v ⊗ w) +> (Stiefel1Needle v ⊗ w)
         ti DualSpaceWitness = LinearMap . Arr.generate d
           $ \i -> fmap (LinearFunction $ \w -> Tensor . Arr.generate d $
              \j -> if i==j then w else zeroV) $ asTensor $ id
         d = freeDimension ([]::[v]) - 1
  dualSpaceWitness = case dualSpaceWitness :: DualSpaceWitness v of
         DualSpaceWitness -> DualSpaceWitness
  coerceDoubleDual = Coercion
  contractTensorMap = LinearFunction $ \(LinearMap m)
                        -> Arr.ifoldl' (\acc i (Tensor t) -> acc ^+^ t Arr.! i) zeroV m
  contractMapTensor = LinearFunction $ \(Tensor m)
                        -> Arr.ifoldl' (\acc i (LinearMap t) -> acc ^+^ t Arr.! i) zeroV m
  contractLinearMapAgainst = bilinearFunction $ \(LinearMap m) f
                        -> Arr.ifoldl' (\acc i w -> case f $ w of
                                          Stiefel1Needle n -> n UArr.! i ) 0 m
  applyDualVector = bilinearFunction $ \(Stiefel1Needle v) (Stiefel1Needle w)
                        -> UArr.sum $ UArr.zipWith (*) v w
  applyLinear = bilinearFunction $ \(LinearMap m) (Stiefel1Needle v)
                        -> Arr.ifoldl' (\acc i w -> acc ^+^ v UArr.! i *^ w) zeroV m
  applyTensorFunctional = bilinearFunction $ \(LinearMap f) (Tensor t)
                           -> Arr.ifoldl' (\acc i u -> acc + u <.>^ t Arr.! i) 0 f
  applyTensorLinMap = bilinearFunction $ \(LinearMap f) (Tensor t)
         -> Arr.ifoldl' (\w i u -> w ^+^ ((asLinearMap $ f Arr.! i) +$> u)) zeroV t
  composeLinear = bilinearFunction $ \f (LinearMap g)
                     -> LinearMap $ Arr.map (getLinearFunction applyLinear f$) g

instance ∀ v .
   ( LinearSpace v, FiniteFreeSpace v, FiniteFreeSpace (DualVector v)
   , StiefelScalar (Scalar v) ) => Semimanifold (Stiefel1 v) where
  type Needle (Stiefel1 v) = Stiefel1Needle v
  fromInterior = id
  toInterior = pure
  translateP = Tagged (.+~^)
  (.+~^) = tpst dualSpaceWitness
   where tpst :: DualSpaceWitness v -> Stiefel1 v -> Stiefel1Needle v -> Stiefel1 v
         tpst DualSpaceWitness (Stiefel1 s) (Stiefel1Needle n)
             = Stiefel1 . unsafeFromFullUnboxVect . uarrScale (signum s'i)
          $ if| ν==0      -> s' -- ν'≡0 is a special case of this, so if not ν=0
                                --  we can otherwise assume ν'>0.
              | ν<=2      -> let m = uarrScale ιmν spro
                                       `uarrAdd` uarrScale ((1-abs ιmν)/ν') n
                                 ιmν = 1-ν 
                             in insi ιmν m
              | otherwise -> let m = uarrScale ιmν spro
                                       `uarrAdd` uarrScale ((abs ιmν-1)/ν') n
                                 ιmν = ν-3
                             in insi ιmν m
          where d = UArr.length s'
                s'= toFullUnboxVect s
                ν' = l2norm n
                quop = signum s'i / ν'
                ν = ν' `mod'` 4
                im = UArr.maxIndex $ UArr.map abs s'
                s'i = s' UArr.! im
                spro = let v = deli s' in uarrScale (recip s'i) v
                deli v = Arr.take im v Arr.++ Arr.drop (im+1) v
                insi ti v = Arr.generate d $ \i -> if | i<im      -> v Arr.! i
                                                      | i>im      -> v Arr.! (i-1) 
                                                      | otherwise -> ti
instance ∀ v .
   ( LinearSpace v, FiniteFreeSpace v, FiniteFreeSpace (DualVector v)
   , StiefelScalar (Scalar v) ) => PseudoAffine (Stiefel1 v) where
  (.-~.) = dpst dualSpaceWitness
   where dpst :: DualSpaceWitness v -> Stiefel1 v -> Stiefel1 v -> Maybe (Stiefel1Needle v)
         dpst DualSpaceWitness (Stiefel1 s) (Stiefel1 t)
             = pure . Stiefel1Needle $ case s' UArr.! im of
                   0 -> uarrScale (recip $ l2norm delis) delis
                   s'i | v <- uarrScale (recip s'i) delis `uarrSubtract` tpro
                       , absv <- l2norm v
                       , absv > 0
                              -> let μ = (signum (t'i/s'i) - recip(absv + 1)) / absv
                                 in uarrScale μ v
                       | t'i/s'i > 0  -> samePoint
                       | otherwise    -> antipode
          where d = UArr.length t'
                s'= toFullUnboxVect s; t' = toFullUnboxVect t
                im = UArr.maxIndex $ UArr.map abs t'
                t'i = t' UArr.! im
                tpro = let v = deli t' in uarrScale (recip t'i) v
                delis = deli s'
                deli v = Arr.take im v Arr.++ Arr.drop (im+1) v
                samePoint = UArr.replicate (d-1) 0
                antipode = (d-1) `UArr.fromListN` (2 : repeat 0)


-- instance ( WithField ℝ HilbertManifold x ) => ConeSemimfd (Stiefel1 x) where
--   type CℝayInterior (Stiefel1 x) = x


l2norm :: (Floating s, UArr.Unbox s) => UArr.Vector s -> s
l2norm = sqrt . UArr.sum . UArr.map (^2)




data Line x = Line { lineHandle :: x
                   , lineDirection :: Stiefel1 (Needle' x) }



-- | Oriented hyperplanes, na&#xef;vely generalised to 'PseudoAffine' manifolds:
--   @'Cutplane' p w@ represents the set of all points 'q' such that
--   @(q.-~.p) ^\<.\> w &#x2261; 0@.
-- 
--   In vector spaces this is indeed a hyperplane; for general manifolds it should
--   behave locally as a plane, globally as an (/n/−1)-dimensional submanifold.
data Cutplane x = Cutplane { sawHandle :: x
                           , cutNormal :: Stiefel1 (Needle x) }
deriving instance (Show x, Show (Needle' x)) => Show (Cutplane x)

normalPlane :: x         -- ^ Some point lying in the desired plane.
            -> Needle' x -- ^ Co-vector perpendicular to the plane. Must be nonzero.
            -> Cutplane x
normalPlane x n = Cutplane x $ Stiefel1 n


sideOfCut :: (WithField ℝ PseudoAffine x, LinearSpace (Needle x))
                   => Cutplane x -> x -> Maybe S⁰
sideOfCut (Cutplane sh (Stiefel1 cn)) p
              = decideSide . (cn<.>^) =<< p.-~.sh
 where decideSide 0 = mzero
       decideSide μ | μ > 0      = pure PositiveHalfSphere
                    | otherwise  = pure NegativeHalfSphere


fathomCutDistance :: ∀ x . (WithField ℝ PseudoAffine x, LinearSpace (Needle x))
        => Cutplane x        -- ^ Hyperplane to measure the distance from.
         -> Metric' x        -- ^ Metric to use for measuring that distance.
                             --   This can only be accurate if the metric
                             --   is valid both around the cut-plane's 'sawHandle', and
                             --   around the points you measure.
                             --   (Strictly speaking, we would need /parallel transport/
                             --   to ensure this).
         -> x                -- ^ Point to measure the distance to.
         -> Maybe ℝ          -- ^ A signed number, giving the distance from plane
                             --   to point with indication on which side the point lies.
                             --   'Nothing' if the point isn't reachable from the plane.
fathomCutDistance = fcd dualSpaceWitness
 where fcd (DualSpaceWitness :: DualSpaceWitness (Needle x))
           (Cutplane sh (Stiefel1 cn)) met
               = \x -> fmap fathom $ x .-~. sh
        where fathom v = (cn <.>^ v) / scaleDist
              scaleDist = met|$|cn
          

cutPosBetween :: WithField ℝ Manifold x => Cutplane x -> (x,x) -> Maybe D¹
cutPosBetween (Cutplane h (Stiefel1 cn)) (x₀,x₁)
    | Just [d₀,d₁] <- map (cn<.>^) <$> sequenceA [x₀.-~.h, x₁.-~.h]
    , d₀*d₁ < 0  = pure . D¹ $ 2 * d₀ / (d₀ - d₁) - 1
    | otherwise  = empty


lineAsPlaneIntersection :: ∀ x .
       (WithField ℝ Manifold x, FiniteDimensional (Needle' x))
           => Line x -> [Cutplane x]
lineAsPlaneIntersection = lapi dualSpaceWitness
 where lapi (DualSpaceWitness :: DualSpaceWitness (Needle x)) (Line h (Stiefel1 dir))
             = [ Cutplane h . Stiefel1
                     $ candidate ^-^ worstCandidate ^* (overlap/worstOvlp)
               | (i, (candidate, overlap)) <- zip [0..] $ zip candidates overlaps
               , i /= worstId ]
        where candidates = enumerateSubBasis entireBasis
              overlaps = (<.>^dir) <$> candidates
              (worstId, worstOvlp) = maximumBy (comparing $ abs . snd) $ zip [0..] overlaps
              worstCandidate = candidates !! worstId

