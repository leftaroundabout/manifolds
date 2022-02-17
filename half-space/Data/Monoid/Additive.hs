-- |
-- Module      : Data.Monoid.Additive
-- Copyright   : (c) Justus Sagemüller 2022
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


module Data.Monoid.Additive (AdditiveMonoid(..), HalfSpace(..)) where

import Data.VectorSpace
import Data.AffineSpace
import Data.Int
import Data.Word

import Math.Manifold.Core.PseudoAffine
import Math.Manifold.Core.Types
import Math.Manifold.VectorSpace.ZeroDimensional
import Control.Applicative
import Control.Arrow
import Data.Void

import qualified GHC.Generics as Gnrx
import GHC.Generics (Generic, (:*:)(..))
import Data.Kind (Type)
import Proof.Propositional (Empty(..))



type AMRep h = Gnrx.Rep h Void

class AdditiveMonoid h where
  zeroHV :: h
  default zeroHV :: (Generic h, AdditiveMonoid (AMRep h)) => h
  zeroHV = Gnrx.to (zeroHV :: AMRep h)
  addHVs :: h -> h -> h
  default addHVs :: (Generic h, AdditiveMonoid (AMRep h)) => h -> h -> h
  addHVs p q = Gnrx.to (addHVs (Gnrx.from p) (Gnrx.from q) :: AMRep h)

instance AdditiveMonoid h => AdditiveMonoid (Gnrx.Rec0 h s) where
  zeroHV = Gnrx.K1 zeroHV
  addHVs (Gnrx.K1 p) (Gnrx.K1 q) = Gnrx.K1 $ addHVs p q
instance AdditiveMonoid (f p) => AdditiveMonoid (Gnrx.M1 i c f p) where
  zeroHV = Gnrx.M1 zeroHV
  addHVs (Gnrx.M1 p) (Gnrx.M1 q) = Gnrx.M1 $ addHVs p q
instance (AdditiveMonoid (f p), AdditiveMonoid (g p))
            => AdditiveMonoid ((f:*:g) p) where
  zeroHV = zeroHV :*: zeroHV
  addHVs (x:*:y) (ξ:*:υ) = addHVs x ξ :*: addHVs y υ

#define AdditiveGroupMonoid(g)     \
instance AdditiveMonoid (g) where { \
  zeroHV = zeroV;                    \
  addHVs = (^+^) }

#define NumAdditiveMonoid(g)       \
instance AdditiveMonoid (g) where { \
  zeroHV = 0;                        \
  addHVs = (+) }

NumAdditiveMonoid(Int)
NumAdditiveMonoid(Integer)
NumAdditiveMonoid(Float)
NumAdditiveMonoid(Double)
NumAdditiveMonoid(Int16)
NumAdditiveMonoid(Int32)
NumAdditiveMonoid(Int64)
NumAdditiveMonoid(Word16)
NumAdditiveMonoid(Word32)
NumAdditiveMonoid(Word64)

instance (AdditiveMonoid h, AdditiveMonoid i) => AdditiveMonoid (h,i)
instance (AdditiveMonoid h, AdditiveMonoid i, AdditiveMonoid j) => AdditiveMonoid (h,i,j)

class AdditiveMonoid h => HalfSpace h where
  type FullSubspace h :: Type
  type Ray h :: Type
  type Ray h = Cℝay ℝ⁰
  scaleNonNeg :: Ray h -> h -> h
  fromFullSubspace :: FullSubspace h -> h
  projectToFullSubspace :: h -> FullSubspace h
  fullSubspaceIsVectorSpace :: (VectorSpace (FullSubspace h) => r) -> r
  default fullSubspaceIsVectorSpace :: VectorSpace (FullSubspace h)
                              => (VectorSpace (FullSubspace h) => r) -> r
  fullSubspaceIsVectorSpace q = q

instance AdditiveMonoid (ZeroDim k) where
  zeroHV = Origin
  addHVs Origin Origin = Origin
instance HalfSpace (ZeroDim k) where
  type FullSubspace (ZeroDim k) = ZeroDim k
  scaleNonNeg _ Origin = Origin
  fromFullSubspace _ = Origin
  projectToFullSubspace Origin = Origin

