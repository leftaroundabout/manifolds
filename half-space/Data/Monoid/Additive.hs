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


module Data.Monoid.Additive where

import Data.VectorSpace
import Data.AffineSpace
import Data.Basis

import Math.Manifold.Core.PseudoAffine
import Math.Manifold.Core.Types
import Control.Applicative
import Control.Arrow

import qualified GHC.Generics as Gnrx
import GHC.Generics (Generic, (:*:)(..))
import Data.Kind (Type)
import Proof.Propositional (Empty(..))

import Data.CallStack (HasCallStack)


class AdditiveMonoid h where
  zeroHV :: h
  addHVs :: h -> h -> h

class AdditiveMonoid h => HalfSpace h where
  type FullSubspace h :: Type
  type Ray h :: Type
  type Ray h = ℝay
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

