-- |
-- Module      : Data.Manifold.WithBoundary.Class
-- Copyright   : (c) Justus Sagemüller 2021
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsag $ hvl.no
-- Stability   : experimental
-- Portability : portable
-- 

{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE UndecidableInstances     #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE DefaultSignatures        #-}
{-# LANGUAGE DeriveGeneric            #-}
{-# LANGUAGE StandaloneDeriving       #-}
{-# LANGUAGE ConstraintKinds          #-}
{-# LANGUAGE UnicodeSyntax            #-}
{-# LANGUAGE ScopedTypeVariables      #-}
{-# LANGUAGE AllowAmbiguousTypes      #-}
{-# LANGUAGE TypeApplications         #-}
{-# LANGUAGE RankNTypes               #-}
{-# LANGUAGE EmptyCase                #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE TypeInType               #-}
{-# LANGUAGE CPP                      #-}


module Data.Manifold.WithBoundary.Class where

import Data.VectorSpace
import Data.AffineSpace
import Data.Basis

import Math.Manifold.Core.PseudoAffine
import Math.Manifold.Core.Types
import Data.Manifold.Types.Primitive
import Math.Manifold.VectorSpace.ZeroDimensional
import Math.LinearMap.Category ( Tensor(..), TensorSpace(..)
                               , LinearMap(..), LinearFunction(..), LinearSpace(..)
                               , Num'
                               )
import Math.VectorSpace.Dual
import Math.VectorSpace.MiscUtil.MultiConstraints (SameScalar)
import Linear (V0, V1, V2, V3, V4)
import qualified Linear.Affine as LinAff
import Data.Monoid.Additive

import Control.Applicative
import Control.Arrow

import qualified GHC.Generics as Gnrx
import GHC.Generics (Generic, (:*:)(..))
import Data.Kind (Type)
import Proof.Propositional (Empty(..))

import Data.CallStack (HasCallStack)


type OpenManifold m = ( SemimanifoldWithBoundary m
                      , SemimanifoldWithBoundary (Needle m)
                      , LinearSpace (Needle m)
                      , SemimanifoldWithBoundary (Scalar (Needle m))
                      , Interior m ~ m
                      , Empty (Boundary m)
                      )

data SmfdWBoundWitness m where
  OpenManifoldWitness :: ∀ m . OpenManifold m
              => SmfdWBoundWitness m
  SmfdWBoundWitness :: ∀ m .
         ( OpenManifold (Interior m), OpenManifold (Boundary m)
         , FullSubspace (HalfNeedle m) ~ Needle (Boundary m) )
              => SmfdWBoundWitness m

-- | The class of spaces with a displacement operation like 'Semimanifold', but there
--   may be a limited range how far it is possible to move before leaving the space.
-- 
--   Such spaces decompose into two 'Semimanifold' spaces: the 'Interior' and the 'Boundary'.
class -- ( Semimanifold (Interior m), Semimanifold (Boundary m)
      -- , HalfSpace (HalfNeedle m) ) =>
    SemimanifoldWithBoundary m where
  -- | Subspace of @m@ representing the set of points where it is possible to move at
  --   least a small distance in any direction (with '.+^|') without leaving @m@.
  type Interior m :: Type
  -- | The set of points where an infinitesimal movement is sufficient to leave @m@.
  type Boundary m :: Type
  type HalfNeedle m :: Type
  -- | Boundary-aware pendant to '.+~^'.
  (.+^|) :: m
         -- ^ Starting point @p@
         -> Needle (Interior m)
         -- ^ Displacement @v@
         -> Either (Boundary m, Scalar (Needle (Interior m)))
                   (Interior m)
         -- ^ If @v@ is enough to leave @m@, yield the point where it does and what
         --   fraction of the length is still left (i.e. how much of @v@ “pokes out
         --   of the space”). If it stays within the space, just give back the result.
  fromInterior :: Interior m -> m
  fromBoundary :: Boundary m -> m
  (|+^) :: Boundary m -> HalfNeedle m -> m
  separateInterior :: m -> Either (Boundary m) (Interior m)
  separateInterior p = case smfdWBoundWitness @m of
   OpenManifoldWitness -> Right p
   SmfdWBoundWitness -> case p .+^| zeroV of
    Left (b,_) -> Left b 
    Right i -> Right i
  toInterior :: m -> Maybe (Interior m)
  toInterior p = case separateInterior p of
    Right i -> Just i
    Left _  -> Nothing
  extendToBoundary :: Interior m -> Needle (Interior m) -> Maybe (Boundary m)
  default extendToBoundary :: ( VectorSpace (Needle (Interior m))
                              , Num (Scalar (Needle (Interior m))) )
           => Interior m -> Needle (Interior m) -> Maybe (Boundary m)
  extendToBoundary p dir = case fromInterior @m p .+^| dir of
    Right _ -> extendToBoundary @m p $ dir^*2
    Left (p, _) -> Just p
  smfdWBoundWitness :: SmfdWBoundWitness m
  default smfdWBoundWitness 
              :: ( OpenManifold (Interior m)
                 , OpenManifold (Boundary m)
                 , FullSubspace (HalfNeedle m) ~ Needle (Boundary m) )
                   => SmfdWBoundWitness m
  smfdWBoundWitness = SmfdWBoundWitness @m
  needleIsOpenMfd :: (OpenManifold (Needle (Interior m)) => r) -> r
  default needleIsOpenMfd :: OpenManifold (Needle (Interior m))
                                 => (OpenManifold (Needle (Interior m)) => r) -> r
  needleIsOpenMfd q = q
  scalarIsOpenMfd :: (OpenManifold (Scalar (Needle (Interior m))) => r) -> r
  default scalarIsOpenMfd :: OpenManifold (Scalar (Needle (Interior m)))
                                 => (OpenManifold (Scalar (Needle (Interior m))) => r) -> r
  scalarIsOpenMfd q = q
  boundaryHasSameScalar
        :: ( ( LinearSpace (Needle (Boundary m))
             , Scalar (Needle (Boundary m)) ~ Scalar (Needle (Interior m)) )
                                => r)-> r
  default boundaryHasSameScalar
           :: (( LinearSpace (Needle (Boundary m))
               , Scalar (Needle (Boundary m)) ~ Scalar (Needle (Interior m))))
     => (( LinearSpace (Needle (Boundary m))
         , Scalar (Needle (Boundary m)) ~ Scalar (Needle (Interior m))) => r) -> r
  boundaryHasSameScalar q = q
  

class (SemimanifoldWithBoundary m, PseudoAffine (Interior m), PseudoAffine (Boundary m))
          => PseudoAffineWithBoundary m where
  -- | Inverse of '.+^|', provided the space is connected. For @p :: Interior m@, @q :: m@
  --   and @v = fromInterior p.--!q@,
  -- 
  --   @
  --   q '.+^|' v ≡ Right p
  --   @
  --
  --   (up to floating-point). Similary, for @b :: Boundary m@ and @w = fromBoundary m.--!q@,
  -- 
  --   @
  --   q '.+^|' w ≡ Left (b, 0)
  --   @
  (.--!) :: m -> m -> Needle (Interior m)
  
  (.-|) :: m -> Boundary m -> Maybe (HalfNeedle m)
  p.-|b = Just $ p!-|b
  (!-|) :: m -> Boundary m -> HalfNeedle m
  (.--.) :: m -> m -> Maybe (Needle (Interior m))
  p.--.q = Just $ p.--!q


class PseudoAffineWithBoundary m => ProjectableBoundary m where
  projectToBoundary :: m
                    -- ^ Point @p@ to project
                    -> Boundary m 
                    -- ^ Intended “course region” representative @r@ on boundary – we
                    --   seek a point that is reachable from there.
                    -> Maybe ( Needle (Boundary m)
                             , Scalar (Needle (Interior m)) )
                    -- ^ Needle @δr@ connecting @r@ to projection of the @p@, and
                    --   a measure @d@ of normal-distance such that
                    --   @'marginFromBoundary' (r.+~^δr) d == p@.
  marginFromBoundary :: Boundary m -> Scalar (Needle (Interior m)) -> m
  needleBoundaryIsTrivallyProjectible :: ∀ r .
        (ProjectableBoundary (Needle (Interior m)) => r) -> r
  default needleBoundaryIsTrivallyProjectible :: ProjectableBoundary (Needle (Interior m))
           => (ProjectableBoundary (Needle (Interior m)) => r) -> r
  needleBoundaryIsTrivallyProjectible q = q
  scalarBoundaryIsTrivallyProjectible :: ∀ r .
        (ProjectableBoundary (Scalar (Needle (Interior m))) => r) -> r
  default scalarBoundaryIsTrivallyProjectible
                      :: ProjectableBoundary (Scalar (Needle (Interior m)))
           => (ProjectableBoundary (Scalar (Needle (Interior m))) => r) -> r
  scalarBoundaryIsTrivallyProjectible q = q

instance ∀ k . ( LinearSpace k, OpenManifold k, OpenManifold (Scalar k) )
             => SemimanifoldWithBoundary (EmptyMfd k) where
  type Interior (EmptyMfd k) = EmptyMfd k
  type Boundary (EmptyMfd k) = EmptyMfd k
  type HalfNeedle (EmptyMfd k) = ZeroDim (Scalar k)
  smfdWBoundWitness = OpenManifoldWitness @(EmptyMfd k)
  q|+^_ = case q of {}
  q.+^|_ = case q of {}
  fromInterior = id
  fromBoundary = id
  scalarIsOpenMfd q = scalarIsOpenMfd @k q

instance ∀ k . (Num' k, OpenManifold k)
            => SemimanifoldWithBoundary (ZeroDim k) where
  type Interior (ZeroDim k) = ZeroDim k
  type Boundary (ZeroDim k) = EmptyMfd (ZeroDim k)
  type HalfNeedle (ZeroDim k) = ZeroDim k
  fromInterior = id
  fromBoundary b = case b of {}
  separateInterior = Right
  p|+^_ = case p of {}
  Origin .+^| Origin = Right Origin
  extendToBoundary _ _ = Nothing
  smfdWBoundWitness = scalarIsOpenMfd @k SmfdWBoundWitness
  scalarIsOpenMfd q = scalarIsOpenMfd @k q

instance (Num' k, OpenManifold k) => PseudoAffineWithBoundary (ZeroDim k) where
  _.-|p = case p of {}
  Origin .--! Origin = Origin
  _!-|q = case q of {}

instance (Num' k, ProjectableBoundary k, OpenManifold k)
            => ProjectableBoundary (ZeroDim k) where
  projectToBoundary Origin b = case b of {}
  marginFromBoundary b _ = case b of {}
