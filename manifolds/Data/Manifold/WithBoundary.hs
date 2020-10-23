-- |
-- Module      : Data.Manifold.WithBoundary
-- Copyright   : (c) Justus Sagemüller 2020
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
{-# LANGUAGE UnicodeSyntax            #-}
{-# LANGUAGE ScopedTypeVariables      #-}
{-# LANGUAGE AllowAmbiguousTypes      #-}
{-# LANGUAGE TypeApplications         #-}
{-# LANGUAGE EmptyCase                #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE TypeInType               #-}


module Data.Manifold.WithBoundary where

import Data.VectorSpace
import Data.AffineSpace
import Data.Basis

import Math.Manifold.Core.PseudoAffine
import Math.Manifold.Core.Types
import Data.Manifold.Types.Primitive
import Math.Manifold.VectorSpace.ZeroDimensional

import Control.Applicative
import Control.Arrow

import qualified GHC.Generics as Gnrx
import GHC.Generics (Generic, (:*:)(..))
import Data.Kind (Type)

import Data.CallStack (HasCallStack)


class AdditiveMonoid h where
  zeroHV :: h
  addHVs :: h -> h -> h

class (AdditiveMonoid h, VectorSpace (FullSubspace h)) => HalfSpace h where
  type FullSubspace h :: Type
  scaleNonNeg :: ℝay -> h -> h
  fromFullSubspace :: FullSubspace h -> h
  projectToFullSubspace :: h -> FullSubspace h

instance AdditiveMonoid (ZeroDim k) where
  zeroHV = Origin
  addHVs Origin Origin = Origin
instance HalfSpace (ZeroDim k) where
  type FullSubspace (ZeroDim k) = ZeroDim k
  scaleNonNeg _ Origin = Origin
  fromFullSubspace _ = Origin
  projectToFullSubspace Origin = Origin

instance AdditiveMonoid ℝay where
  zeroHV = Cℝay 0 Origin
  addHVs (Cℝay a Origin) (Cℝay b Origin) = Cℝay (a+b) Origin
instance HalfSpace ℝay where
  type FullSubspace ℝay = ℝ⁰
  scaleNonNeg (Cℝay μ Origin) (Cℝay l Origin) = Cℝay (μ*l) Origin
  fromFullSubspace o = Cℝay 0 o
  projectToFullSubspace (Cℝay _ o) = o

class ( Semimanifold (Interior m), Semimanifold (Boundary m)
      , HalfSpace (HalfNeedle m), FullSubspace (HalfNeedle m) ~ Needle (Boundary m)
      ) => SemimanifoldWithBoundary m where
  type Interior m :: Type
  type Boundary m :: Type
  type HalfNeedle m :: Type
  (|+^) :: Boundary m -> HalfNeedle m -> m
  (.+^|) :: m -> Needle (Interior m)
           -> Either (Boundary m, Scalar (Needle (Interior m))) (Interior m)
  fromInterior :: Interior m -> m
  separateInterior :: m -> Either (Boundary m) (Interior m)
  separateInterior p = case p .+^| zeroV of
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

class (SemimanifoldWithBoundary m, PseudoAffine (Interior m), PseudoAffine (Boundary m))
          => PseudoAffineWithBoundary m where
  (.-|) :: m -> Boundary m -> HalfNeedle m
  (.--.) :: m -> m -> Needle (Interior m)

instance SemimanifoldWithBoundary (ZeroDim k) where
  type Interior (ZeroDim k) = ZeroDim k
  type Boundary (ZeroDim k) = EmptyMfd (ZeroDim k)
  type HalfNeedle (ZeroDim k) = ZeroDim k
  fromInterior = id
  separateInterior = Right
  p|+^_ = case p of {}
  Origin .+^| Origin = Right Origin
  extendToBoundary _ _ = Nothing

instance PseudoAffineWithBoundary (ZeroDim k) where
  _.-|p = case p of {}
  Origin .--. Origin = Origin

instance SemimanifoldWithBoundary ℝ where
  type Interior ℝ = ℝ
  type Boundary ℝ = EmptyMfd ℝ⁰
  type HalfNeedle ℝ = ℝay
  fromInterior = id
  separateInterior = Right
  p|+^_ = case p of {}
  a.+^|b = Right $ a+b
  extendToBoundary _ _ = Nothing

instance PseudoAffineWithBoundary ℝ where
  _.-|p = case p of {}
  (.--.) = (-)

data ProductBoundary a b
  = P₀Boundary (Boundary a) (Interior b)
  | P₁Boundary a (Boundary b)

instance ∀ a b . (SemimanifoldWithBoundary a, SemimanifoldWithBoundary b)
   => Semimanifold (ProductBoundary a b) where
  type Needle (ProductBoundary a b) = (Needle (Boundary a), Needle (Interior b))
  (.+~^) = case semimanifoldWitness @(Interior b) of
   SemimanifoldWitness -> 
      \(P₀Boundary ba ib) (δa, δb) -> case fromInterior @b ib .+^| δb of
         Right ib' -> P₀Boundary (ba.+~^δa) ib'
         Left q -> undefined
  semimanifoldWitness = case ( semimanifoldWitness @(Boundary a)
                             , semimanifoldWitness @(Interior b) ) of
    (SemimanifoldWitness, SemimanifoldWitness)
       -> SemimanifoldWitness
