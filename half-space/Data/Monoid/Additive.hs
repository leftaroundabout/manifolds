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
NumAdditiveMonoid(Int8)
NumAdditiveMonoid(Int16)
NumAdditiveMonoid(Int32)
NumAdditiveMonoid(Int64)
NumAdditiveMonoid(Word)
NumAdditiveMonoid(Word8)
NumAdditiveMonoid(Word16)
NumAdditiveMonoid(Word32)
NumAdditiveMonoid(Word64)

instance (AdditiveMonoid h, AdditiveMonoid i) => AdditiveMonoid (h,i)
instance (AdditiveMonoid h, AdditiveMonoid i, AdditiveMonoid j) => AdditiveMonoid (h,i,j)

class AdditiveMonoid h => HalfSpace h where
  type FullSubspace h :: Type
  type FullSubspace h = GenericFullSubspace h
  type Ray h :: Type
  type Ray h = Ray (AMRep h)
  scaleNonNeg :: Ray h -> h -> h
  default scaleNonNeg :: ( Generic h, HalfSpace (AMRep h)
                         , FullSubspace h ~ GenericFullSubspace h
                         , Ray h ~ Ray (AMRep h) )
             => Ray h -> h -> h
  scaleNonNeg μ p = Gnrx.to (scaleNonNeg μ (Gnrx.from p) :: AMRep h)
  fromFullSubspace :: FullSubspace h -> h
  default fromFullSubspace :: ( Generic h, HalfSpace (AMRep h)
                              , FullSubspace h ~ GenericFullSubspace h
                              , Ray h ~ Ray (AMRep h) )
             => FullSubspace h -> h
  fromFullSubspace (GenericFullSubspace x) = Gnrx.to (fromFullSubspace x :: AMRep h)
  projectToFullSubspace :: h -> FullSubspace h
  fullSubspaceIsVectorSpace :: (VectorSpace (FullSubspace h) => r) -> r
  default fullSubspaceIsVectorSpace :: VectorSpace (FullSubspace h)
                              => (VectorSpace (FullSubspace h) => r) -> r
  fullSubspaceIsVectorSpace q = q

newtype GenericFullSubspace h = GenericFullSubspace
    { getGenericFullSubspace :: FullSubspace (AMRep h) }
  deriving (Generic)
instance AdditiveGroup (FullSubspace (AMRep h)) => AdditiveGroup (GenericFullSubspace h)
instance VectorSpace (FullSubspace (AMRep h)) => VectorSpace (GenericFullSubspace h)

instance ∀ h s . HalfSpace h => HalfSpace (Gnrx.Rec0 h s) where
  type FullSubspace (Gnrx.Rec0 h s) = FullSubspace h
  type Ray (Gnrx.Rec0 h s) = Ray h
  scaleNonNeg μ (Gnrx.K1 p) = Gnrx.K1 $ scaleNonNeg μ p
  fullSubspaceIsVectorSpace c = fullSubspaceIsVectorSpace @h c
  fromFullSubspace x = Gnrx.K1 $ fromFullSubspace x
  projectToFullSubspace (Gnrx.K1 p) = projectToFullSubspace p
instance HalfSpace (f p) => HalfSpace (Gnrx.M1 i c f p) where
  type FullSubspace (Gnrx.M1 i c f p) = FullSubspace (f p)
  type Ray (Gnrx.M1 i c f p) = Ray (f p)
  scaleNonNeg μ (Gnrx.M1 p) = Gnrx.M1 $ scaleNonNeg μ p
  fullSubspaceIsVectorSpace c = fullSubspaceIsVectorSpace @(f p) c
  fromFullSubspace x = Gnrx.M1 $ fromFullSubspace x
  projectToFullSubspace (Gnrx.M1 p) = projectToFullSubspace p

data GenericProductFullSubspace f g p
   = GenericProductFullSubspace { lFullSubspace :: !(FullSubspace (f p))
                                , rFullSpace :: !(g p) }

-- instance (HalfSpace (f p), VectorSpace (g p), Scalar (Ray (f p)), FullScalar) => HalfSpace ((f:*:g) p) where
--   type FullSubspace ((f:*:g) p) = GenericProductFullSubspace f g p
--   type Ray (Gnrx.Rec0 h s) = Ray h

instance AdditiveMonoid (ZeroDim k) where
  zeroHV = Origin
  addHVs Origin Origin = Origin
instance HalfSpace (ZeroDim k) where
  type FullSubspace (ZeroDim k) = ZeroDim k
  scaleNonNeg _ Origin = Origin
  fromFullSubspace _ = Origin
  projectToFullSubspace Origin = Origin

#define WordHalfSpace(w)             \
instance HalfSpace (w) where {        \
  type FullSubspace (w) = ZeroDim (w); \
  type Ray (w) = (w);                   \
  scaleNonNeg = (*);                     \
  fromFullSubspace Origin = 0;            \
  projectToFullSubspace _ = Origin }

WordHalfSpace(Word)
WordHalfSpace(Word8)
WordHalfSpace(Word16)
WordHalfSpace(Word32)
WordHalfSpace(Word64)


newtype GnTestHS = GnTestHS Word
  deriving (Generic)

instance AdditiveMonoid GnTestHS
instance HalfSpace GnTestHS