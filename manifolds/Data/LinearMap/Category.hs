-- |
-- Module      : Data.LinearMap.Category
-- Copyright   : (c) Justus Sagemüller 2015
-- License     : GPL v3
-- 
-- Maintainer  : (@) sagemueller $ geo.uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE UnicodeSyntax              #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE PatternGuards              #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE DataKinds                  #-}

module Data.LinearMap.Category where

import Data.Tagged
import Data.Semigroup

import Data.MemoTrie
import Data.VectorSpace
import Data.VectorSpace.FiniteDimensional
import Data.AffineSpace
import Data.Basis
import Data.AdditiveGroup
    
import qualified Prelude as Hask hiding(foldl)
import qualified Control.Applicative as Hask
import qualified Control.Monad       as Hask
import qualified Data.Foldable       as Hask


import Control.Category.Constrained.Prelude hiding ((^))
import Control.Arrow.Constrained

import Data.Manifold.Types.Primitive
import Data.CoNat
import Data.Embedding

import qualified Data.Vector as Arr
import qualified Numeric.LinearAlgebra.HMatrix as HMat


    
-- | A linear mapping between finite-dimensional spaces, implemeted as a dense matrix.
data Linear s a b = DenseLinear { getDenseMatrix :: HMat.Matrix s }

identMat :: forall v w . FiniteDimensional v => Linear (Scalar v) w v
identMat = DenseLinear $ HMat.ident n
 where (Tagged n) = dimension :: Tagged v Int

instance (SmoothScalar s) => Category (Linear s) where
  type Object (Linear s) v = (FiniteDimensional v, Scalar v~s)
  id = identMat
  DenseLinear f . DenseLinear g = DenseLinear $ HMat.mul f g

instance (SmoothScalar s) => Cartesian (Linear s) where
  type UnitObject (Linear s) = ZeroDim s
  swap = lSwap
   where lSwap :: forall v w s
              . (FiniteDimensional v, FiniteDimensional w, Scalar v~s, Scalar w~s)
                   => Linear s (v,w) (w,v)
         lSwap = DenseLinear $ HMat.assoc (n,n) 0 l
          where l = [ ((i,i+nv), 1) | i<-[0.. nw-1] ] ++ [ ((i+nw,i), 1) | i<-[0.. nv-1] ] 
                (Tagged nv) = dimension :: Tagged v Int
                (Tagged nw) = dimension :: Tagged w Int
                n = nv + nw
  attachUnit = identMat
  detachUnit = identMat
  regroup = identMat
  regroup' = identMat

instance (SmoothScalar s) => Morphism (Linear s) where
  DenseLinear f *** DenseLinear g = DenseLinear $ HMat.diagBlock [f,g]

instance (SmoothScalar s) => PreArrow (Linear s) where
  DenseLinear f &&& DenseLinear g = DenseLinear $ HMat.fromBlocks [[f], [g]]
  fst = lFst
   where lFst :: forall v w s
              . (FiniteDimensional v, FiniteDimensional w, Scalar v~s, Scalar w~s)
                   => Linear s (v,w) v
         lFst = DenseLinear $ HMat.assoc (nv,n) 0 l
          where l = [ ((i,i), 1) | i<-[0.. nv-1] ]
                (Tagged nv) = dimension :: Tagged v Int
                (Tagged nw) = dimension :: Tagged w Int
                n = nv + nw
  snd = lSnd
   where lSnd :: forall v w s
              . (FiniteDimensional v, FiniteDimensional w, Scalar v~s, Scalar w~s)
                   => Linear s (v,w) w
         lSnd = DenseLinear $ HMat.assoc (nw,n) 0 l
          where l = [ ((i,i+nv), 1) | i<-[0.. nw-1] ]
                (Tagged nv) = dimension :: Tagged v Int
                (Tagged nw) = dimension :: Tagged w Int
                n = nv + nw
  terminal = lTerminal
   where lTerminal :: forall v s . (FiniteDimensional v, Scalar v~s)
                         => Linear s v (ZeroDim s)
         lTerminal = DenseLinear $ (0 HMat.>< n) []
          where (Tagged n) = dimension :: Tagged v Int

instance (SmoothScalar s) => EnhancedCat (->) (Linear s) where
  arr (DenseLinear mat) = fromPackedVector . HMat.app mat . asPackedVector




canonicalIdentityMatrix :: forall n v s
                 . (KnownNat n, IsFreeSpace v, FreeDimension v ~ n, Scalar v ~ s)
           => Linear s v (FreeVect n s)
canonicalIdentityMatrix = DenseLinear $ HMat.ident n
 where (Tagged n) = theNatN :: Tagged n Int

-- | Class of spaces that directly represent a free vector space, i.e. that are simply
--   @n@-fold products of the base field.
--   This class basically contains 'ℝ', 'ℝ²', 'ℝ³' etc., in future also the complex and
--   probably integral versions.
class (FiniteDimensional v, KnownNat (FreeDimension v)) => IsFreeSpace v where
  type FreeDimension v :: Nat
  identityMatrix :: Isomorphism (Linear (Scalar v))
                      v
                      (FreeVect (FreeDimension v) (Scalar v))
  identityMatrix = fromInversePair emb proj
   where emb@(DenseLinear i) = canonicalIdentityMatrix
         proj = DenseLinear i

instance (KnownNat n, Num s, SmoothScalar s) => IsFreeSpace (FreeVect n s) where 
  type FreeDimension (FreeVect n s) = n
  identityMatrix = fromInversePair id id

instance IsFreeSpace ℝ where
  type FreeDimension ℝ = S Z
  
instance ( SmoothScalar s, IsFreeSpace v, Scalar v ~ s, FiniteDimensional s, s ~ Scalar s )
             => IsFreeSpace (v,s) where
  type FreeDimension (v,s) = S (FreeDimension v)


