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
{-# LANGUAGE DeriveAnyClass           #-}
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
  type MirrorJoin h :: Type
  type MirrorJoin h = GenericMirrorJoin h
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
  default projectToFullSubspace :: ( Generic h, HalfSpace (AMRep h)
                                   , FullSubspace h ~ GenericFullSubspace h
                                   , Ray h ~ Ray (AMRep h) )
             => h -> FullSubspace h
  projectToFullSubspace p
           = GenericFullSubspace (projectToFullSubspace (Gnrx.from p :: AMRep h))
  fullSubspaceIsVectorSpace
   :: ((VectorSpace (FullSubspace h), Scalar (FullSubspace h) ~ MirrorJoin (Ray h)) => r) -> r
  default fullSubspaceIsVectorSpace
       :: ( VectorSpace (FullSubspace h), Scalar (FullSubspace h) ~ MirrorJoin (Ray h) )
   => ( (VectorSpace (FullSubspace h), Scalar (FullSubspace h) ~ MirrorJoin (Ray h)) => r) -> r
  fullSubspaceIsVectorSpace q = q
  rayIsHalfSpace :: (HalfSpace (Ray h) => r) -> r
  default rayIsHalfSpace :: HalfSpace (Ray h) => (HalfSpace (Ray h) => r) -> r
  rayIsHalfSpace q = q
  mirrorJoinIsVectorSpace
   :: ((VectorSpace (MirrorJoin h), Scalar (MirrorJoin h) ~ MirrorJoin (Ray h)) => r) -> r
  default mirrorJoinIsVectorSpace
       :: ( VectorSpace (MirrorJoin h), Scalar (MirrorJoin h) ~ MirrorJoin (Ray h) )
   => ((VectorSpace (MirrorJoin h), Scalar (MirrorJoin h) ~ MirrorJoin (Ray h)) => r) -> r
  mirrorJoinIsVectorSpace q = q
  fromPositiveHalf :: h -> MirrorJoin h
  default fromPositiveHalf :: ( Generic h, HalfSpace (AMRep h)
                              , MirrorJoin h ~ GenericMirrorJoin h
                              , Ray h ~ Ray (AMRep h) )
             => h -> MirrorJoin h
  fromPositiveHalf p = GenericMirrorJoin $ fromPositiveHalf (Gnrx.from p :: AMRep h)
  fromNegativeHalf :: h -> MirrorJoin h
  default fromNegativeHalf :: ( Generic h, HalfSpace (AMRep h)
                              , MirrorJoin h ~ GenericMirrorJoin h
                              , Ray h ~ Ray (AMRep h) )
             => h -> MirrorJoin h
  fromNegativeHalf p = GenericMirrorJoin $ fromNegativeHalf (Gnrx.from p :: AMRep h)

newtype GenericFullSubspace h = GenericFullSubspace
    { getGenericFullSubspace :: FullSubspace (AMRep h) }
  deriving (Generic)
instance AdditiveGroup (FullSubspace (AMRep h)) => AdditiveGroup (GenericFullSubspace h)
instance VectorSpace (FullSubspace (AMRep h)) => VectorSpace (GenericFullSubspace h)

newtype GenericMirrorJoin h = GenericMirrorJoin
    { getGenericMirrorJoin :: MirrorJoin (AMRep h) }
  deriving (Generic)
instance AdditiveGroup (MirrorJoin (AMRep h)) => AdditiveGroup (GenericMirrorJoin h)
instance VectorSpace (MirrorJoin (AMRep h)) => VectorSpace (GenericMirrorJoin h)

instance ∀ h s . HalfSpace h => HalfSpace (Gnrx.Rec0 h s) where
  type FullSubspace (Gnrx.Rec0 h s) = FullSubspace h
  type Ray (Gnrx.Rec0 h s) = Ray h
  type MirrorJoin (Gnrx.Rec0 h s) = MirrorJoin h
  scaleNonNeg μ (Gnrx.K1 p) = Gnrx.K1 $ scaleNonNeg μ p
  fullSubspaceIsVectorSpace c = fullSubspaceIsVectorSpace @h c
  mirrorJoinIsVectorSpace c = mirrorJoinIsVectorSpace @h c
  rayIsHalfSpace c = rayIsHalfSpace @h c
  fromFullSubspace x = Gnrx.K1 $ fromFullSubspace x
  projectToFullSubspace (Gnrx.K1 p) = projectToFullSubspace p
  fromPositiveHalf (Gnrx.K1 p) = fromPositiveHalf p
  fromNegativeHalf (Gnrx.K1 p) = fromNegativeHalf p
instance HalfSpace (f p) => HalfSpace (Gnrx.M1 i c f p) where
  type FullSubspace (Gnrx.M1 i c f p) = FullSubspace (f p)
  type Ray (Gnrx.M1 i c f p) = Ray (f p)
  type MirrorJoin (Gnrx.M1 i c f p) = MirrorJoin (f p)
  scaleNonNeg μ (Gnrx.M1 p) = Gnrx.M1 $ scaleNonNeg μ p
  fullSubspaceIsVectorSpace c = fullSubspaceIsVectorSpace @(f p) c
  mirrorJoinIsVectorSpace c = mirrorJoinIsVectorSpace @(f p) c
  rayIsHalfSpace c = rayIsHalfSpace @(f p) c
  fromFullSubspace x = Gnrx.M1 $ fromFullSubspace x
  projectToFullSubspace (Gnrx.M1 p) = projectToFullSubspace p
  fromPositiveHalf (Gnrx.M1 p) = fromPositiveHalf p
  fromNegativeHalf (Gnrx.M1 p) = fromNegativeHalf p

data GenericProductFullSubspace f g p
   = GenericProductFullSubspace { lFullSubspace :: !(FullSubspace (f p))
                                , rFullSpace :: !(g p) }
  deriving (Generic)
deriving instance (AdditiveGroup (FullSubspace (f p)), AdditiveGroup (g p))
           => AdditiveGroup (GenericProductFullSubspace f g p)
deriving instance ( VectorSpace (FullSubspace (f p)), VectorSpace (g p)
                  , Scalar (FullSubspace (f p)) ~ Scalar (g p) )
           => VectorSpace (GenericProductFullSubspace f g p)

data GenericProductMirrorJoin f g p
   = GenericProductMirrorJoin { lPMJcomponent :: !(MirrorJoin (f p))
                              , rPMJcomponent :: !(g p) }
  deriving (Generic)
deriving instance (AdditiveGroup (MirrorJoin (f p)), AdditiveGroup (g p))
           => AdditiveGroup (GenericProductMirrorJoin f g p)
deriving instance ( VectorSpace (MirrorJoin (f p)), VectorSpace (g p)
                  , Scalar (MirrorJoin (f p)) ~ Scalar (g p) )
           => VectorSpace (GenericProductMirrorJoin f g p)

instance ∀ f g p . ( HalfSpace (f p), VectorSpace (g p), AdditiveMonoid (g p)
                   , Ray (f p) ~ Cℝay (ZeroDim (Scalar (g p))) )
             => HalfSpace ((f:*:g) p) where
  type FullSubspace ((f:*:g) p) = GenericProductFullSubspace f g p
  type Ray ((f:*:g) p) = Cℝay (ZeroDim (Scalar (g p)))
  type MirrorJoin ((f:*:g) p) = GenericProductMirrorJoin f g p
  scaleNonNeg (Cℝay μ Origin) (x:*:y) = scaleNonNeg (Cℝay μ Origin) x :*: (μ*^y)
  fromFullSubspace (GenericProductFullSubspace xf y) = fromFullSubspace xf :*: y
  fullSubspaceIsVectorSpace c = fullSubspaceIsVectorSpace @(f p) c
  mirrorJoinIsVectorSpace c = mirrorJoinIsVectorSpace @(f p) c
  rayIsHalfSpace c = rayIsHalfSpace @(f p) c
  fromPositiveHalf (x:*:y) = GenericProductMirrorJoin (fromPositiveHalf x) y
  fromNegativeHalf (x:*:y) = GenericProductMirrorJoin (fromNegativeHalf x) y
  projectToFullSubspace (x:*:y) = GenericProductFullSubspace (projectToFullSubspace x) y

instance AdditiveMonoid (ZeroDim k) where
  zeroHV = Origin
  addHVs Origin Origin = Origin

instance ∀ k . Num k => AdditiveMonoid (Cℝay (ZeroDim k)) where
  zeroHV = Cℝay 0 Origin
  addHVs (Cℝay a Origin) (Cℝay b Origin) = Cℝay (a+b) Origin
instance (Num k, VectorSpace k, Scalar k ~ k) => HalfSpace (Cℝay (ZeroDim k)) where
  type FullSubspace (Cℝay (ZeroDim k)) = ZeroDim k
  type Ray (Cℝay (ZeroDim k)) = Cℝay (ZeroDim k)
  type MirrorJoin (Cℝay (ZeroDim k)) = k
  scaleNonNeg (Cℝay μ Origin) (Cℝay l Origin) = Cℝay (μ*l) Origin
  fromFullSubspace Origin = Cℝay 0 Origin
  projectToFullSubspace (Cℝay _ Origin) = Origin
  fromPositiveHalf (Cℝay l Origin) = l
  fromNegativeHalf (Cℝay l Origin) = -l
  
instance ∀ x y . ( HalfSpace x, VectorSpace y, AdditiveMonoid y
                 , Ray x ~ Cℝay (ZeroDim (Scalar y)) ) => HalfSpace (x,y) where
  fullSubspaceIsVectorSpace c = fullSubspaceIsVectorSpace @x c
  rayIsHalfSpace c = rayIsHalfSpace @x c
  mirrorJoinIsVectorSpace c = mirrorJoinIsVectorSpace @x c

