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
{-# LANGUAGE CPP                        #-}
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
newtype Linear s a b = DenseLinear { getDenseMatrix :: HMat.Matrix s }

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

type DenseLinearFuncValue s = GenericAgent (Linear s)

instance (SmoothScalar s) => HasAgent (Linear s) where
  alg = genericAlg
  ($~) = genericAgentMap
instance (SmoothScalar s) => CartesianAgent (Linear s) where
  alg1to2 = genericAlg1to2
  alg2to1 = genericAlg2to1
  alg2to2 = genericAlg2to2


instance (FiniteDimensional v, Scalar v~s, FiniteDimensional w, Scalar w~s, SmoothScalar s)
                     => AffineSpace (Linear s v w) where
  type Diff (Linear s v w) = Linear s v w
  DenseLinear m.-.DenseLinear n = DenseLinear (m-n)
  DenseLinear m.+^DenseLinear n = DenseLinear (m+n)

instance (FiniteDimensional v, Scalar v~s, FiniteDimensional w, Scalar w~s, SmoothScalar s)
                       => AdditiveGroup (Linear s v w) where
  zeroV = zx
   where zx :: ∀ v w . (FiniteDimensional v, FiniteDimensional w) => Linear s v w
         zx = DenseLinear $ HMat.konst 0 (dw,dv)
          where Tagged dv = dimension :: Tagged v Int
                Tagged dw = dimension :: Tagged w Int
  negateV (DenseLinear m) = DenseLinear $ negate m
  DenseLinear m^+^DenseLinear n = DenseLinear (m+n)
  DenseLinear m^-^DenseLinear n = DenseLinear (m-n)

instance (FiniteDimensional v, Scalar v~s, FiniteDimensional w, Scalar w~s, SmoothScalar s)
             => VectorSpace (Linear s v w) where
  type Scalar (Linear s v w) = s
  μ *^ DenseLinear m = DenseLinear $ HMat.scale μ m

instance (FiniteDimensional v, Scalar v~s, FiniteDimensional w, Scalar w~s, SmoothScalar s)
             => HasBasis (Linear s v w) where
  type Basis (Linear s v w) = (Basis v, Basis w)
  basisValue = bx
   where bx :: ∀ v w . (FiniteDimensional v, FiniteDimensional w)
                          => (Basis v, Basis w)->Linear s v w
         bx = \(bv,bw) -> DenseLinear $ HMat.assoc (dw,dv) 0 [((biw bw, biv bv),1)]
          where Tagged dv = dimension :: Tagged v Int
                Tagged dw = dimension :: Tagged w Int
                Tagged biv = basisIndex :: Tagged v (Basis v->Int)
                Tagged biw = basisIndex :: Tagged w (Basis w->Int)
  decompose = dc
   where dc :: ∀ s v w . ( FiniteDimensional v, Scalar v ~ s
                         , FiniteDimensional w, Scalar w ~ s )
                 => Linear s v w -> [((Basis v, Basis w), s)]
         dc lm = map (id &&& decompose' lm) cb
          where Tagged cb = completeBasis :: Tagged (Linear s v w) [(Basis v, Basis w)]
  decompose' = dc
   where dc :: ∀ s v w . (FiniteDimensional v, FiniteDimensional w, Scalar w ~ s)
               => Linear s v w -> (Basis v, Basis w) -> s
         dc (DenseLinear m) = \(bv,bw) -> m HMat.! biw bw HMat.! biv bv
          where Tagged biv = basisIndex :: Tagged v (Basis v->Int)
                Tagged biw = basisIndex :: Tagged w (Basis w->Int)

instance (FiniteDimensional v, Scalar v ~ s, FiniteDimensional w, Scalar w ~ s)
                => FiniteDimensional (Linear s v w) where
  dimension = d
   where d :: ∀ s v w . (FiniteDimensional v, FiniteDimensional w)
               => Tagged (Linear s v w) Int
         d = Tagged (dv*dw)
          where Tagged dv = dimension::Tagged v Int; Tagged dw = dimension::Tagged w Int
  basisIndex = bi
   where bi :: ∀ s v w . (FiniteDimensional v, FiniteDimensional w)
               => Tagged (Linear s v w) ((Basis v, Basis w) -> Int)
         bi = Tagged $ \(bv,bw) -> dv * biv bv + biw bw where 
          Tagged dv=dimension::Tagged v Int; Tagged biv=basisIndex::Tagged v (Basis v->Int)
          Tagged biw = basisIndex :: Tagged w (Basis w -> Int)
  indexBasis = ib
   where ib :: ∀ s v w . (FiniteDimensional v, FiniteDimensional w)
               => Tagged (Linear s v w) (Int -> (Basis v, Basis w))
         ib = Tagged $ (`divMod`dv) >>> \(iv,iw) -> (ibv iv, ibw iw) where
          Tagged dv=dimension::Tagged v Int; Tagged ibv=indexBasis::Tagged v (Int->Basis v)
          Tagged ibw = indexBasis :: Tagged w (Int->Basis w)
  completeBasis = cb
   where cb :: ∀ s v w . (FiniteDimensional v, FiniteDimensional w)
               => Tagged (Linear s v w) [(Basis v, Basis w)]
         cb = Tagged $ liftA2 (,) cbv cbw where
          Tagged cbv = completeBasis :: Tagged v [Basis v]
          Tagged cbw = completeBasis :: Tagged w [Basis w]
  asPackedVector = getDenseMatrix >>> HMat.flatten
  fromPackedVector = fpv
   where fpv :: ∀ s v w . (FiniteDimensional v, Scalar v ~ s, FiniteDimensional w, Scalar w ~ s)
               => HMat.Vector s -> Linear s v w
         fpv = HMat.reshape dv >>> DenseLinear
          where Tagged dv = dimension :: Tagged v Int

instance (FiniteDimensional v, Scalar v ~ s, FiniteDimensional a, Scalar a ~ s)
    => AdditiveGroup (DenseLinearFuncValue s a v) where
  zeroV = GenericAgent zeroV
  GenericAgent f ^+^ GenericAgent g = GenericAgent $ f ^+^ g
  negateV (GenericAgent f) = GenericAgent $ negateV f



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



class VectorSpace v => FreeTuple v where
  type Tuplity v :: Nat
  freeTuple :: Isomorphism (->) v (FreeVect (Tuplity v) (Scalar v))

#define FreeScalar(s)                                                             \
instance FreeTuple (s) where {                                                     \
  type Tuplity (s) = S Z;                                                           \
  freeTuple = fromInversePair (FreeVect . pure) (\(FreeVect v) -> v Arr.! 0); }

#define FreePair(s)                                                         \
FreeScalar(s);                                                               \
instance FreeTuple (s,s) where {                                              \
  type Tuplity (s,s) = S(S Z);                                                 \
  freeTuple = fromInversePair (\(a,b) -> FreeVect $ Arr.fromList[a,b])          \
                              (\(FreeVect v) -> (v Arr.! 0, v Arr.! 1)); }

#define FreeTriple(s)                                                            \
FreePair(s);                                                                      \
instance FreeTuple (s,s,s) where {                                                 \
  type Tuplity (s,s,s) = S(S(S Z));                                                 \
  freeTuple = fromInversePair (\(a,b,c) -> FreeVect $ Arr.fromList[a,b,c])           \
                              (\(FreeVect v) -> (v Arr.! 0, v Arr.! 1, v Arr.! 2)); };\
instance FreeTuple (s,(s,s)) where {                                                 \
  type Tuplity (s,(s,s)) = S(S(S Z));                                                 \
  freeTuple = fromInversePair (\(a,(b,c)) -> FreeVect $ Arr.fromList[a,b,c])           \
                              (\(FreeVect v) -> (v Arr.! 0, (v Arr.! 1, v Arr.! 2))); };\
instance FreeTuple ((s,s),s) where {                                                 \
  type Tuplity ((s,s),s) = S(S(S Z));                                                 \
  freeTuple = fromInversePair (\((a,b),c) -> FreeVect $ Arr.fromList[a,b,c])           \
                              (\(FreeVect v) -> ((v Arr.! 0, v Arr.! 1), v Arr.! 2)); }

FreeTriple(ℝ)
FreeTriple(Int)


