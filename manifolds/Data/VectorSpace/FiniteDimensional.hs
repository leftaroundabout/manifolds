-- |
-- Module      : Data.VectorSpace.FiniteDimensional
-- Copyright   : (c) Justus Sagemüller 2015
-- License     : GPL v3
-- 
-- Maintainer  : (@) sagemueller $ geo.uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE UnicodeSyntax              #-}




module Data.VectorSpace.FiniteDimensional (
    FiniteDimensional(..)
  , SmoothScalar 
  , FinVecArrRep(..), concreteArrRep, (⊕), splitArrRep
  ) where
    

    

import Prelude hiding ((^))

import Data.AffineSpace
import Data.VectorSpace
import Data.LinearMap
import Data.Basis
import Data.MemoTrie
import Data.Tagged
import Data.Void

import Control.Applicative
    
import Data.Manifold.Types.Primitive
import Data.CoNat
import Data.Embedding

import Control.Arrow

import qualified Data.Vector as Arr
import qualified Numeric.LinearAlgebra.HMatrix as HMat




-- | Constraint that a space's scalars need to fulfill so it can be used for efficient linear algebra.
--   Fulfilled pretty much only by the basic real and complex floating-point types.
type SmoothScalar s = ( VectorSpace s, HMat.Numeric s, HMat.Field s
                      , Num(HMat.Vector s), HMat.Indexable(HMat.Vector s)s
                      , HMat.Normed(HMat.Vector s) )

-- | Many linear algebra operations are best implemented via packed, dense 'HMat.Matrix'es.
--   For one thing, that makes common general vector operations quite efficient,
--   in particular on high-dimensional spaces.
--   More importantly, @hmatrix@ offers linear facilities
--   such as inverse and eigenbasis transformations, which aren't available in the
--   @vector-space@ library yet. But the classes from that library are strongly preferrable
--   to plain matrices and arrays, conceptually.
-- 
--   The 'FiniteDimensional' class is used to convert between both representations.
--   It would be nice not to have the requirement of finite dimension on 'HerMetric',
--   but it's probably not feasible to get rid of it in forseeable time.
--   
--   Instead of the run-time 'dimension' information, we would rather have a compile-time
--   @type Dimension v :: Nat@, but type-level naturals are not mature enough yet. This
--   will almost certainly change in the future.
class (HasBasis v, HasTrie (Basis v), SmoothScalar (Scalar v)) => FiniteDimensional v where
  dimension :: Tagged v Int
  basisIndex :: Tagged v (Basis v -> Int)
  -- | Index must be in @[0 .. dimension-1]@, otherwise this is undefined.
  indexBasis :: Tagged v (Int -> Basis v)
  completeBasis :: Tagged v [Basis v]
  completeBasis = liftA2 (\dim f -> f <$> [0 .. dim - 1]) dimension indexBasis
  
  asPackedVector :: v -> HMat.Vector (Scalar v)
  asPackedVector v = HMat.fromList $ snd <$> decompose v
  
  asPackedMatrix :: (FiniteDimensional w, Scalar w ~ Scalar v)
                       => (v :-* w) -> HMat.Matrix (Scalar v)
  asPackedMatrix = defaultAsPackedMatrix
   where defaultAsPackedMatrix :: forall v w s .
               (FiniteDimensional v, FiniteDimensional w, s~Scalar v, s~Scalar w)
                         => (v :-* w) -> HMat.Matrix s
         defaultAsPackedMatrix m = HMat.fromRows $ asPackedVector . atBasis m <$> cb
          where (Tagged cb) = completeBasis :: Tagged v [Basis v]
  
  fromPackedVector :: HMat.Vector (Scalar v) -> v
  fromPackedVector v = result
   where result = recompose $ zip cb (HMat.toList v)
         cb = witness completeBasis result

instance (SmoothScalar k) => FiniteDimensional (ZeroDim k) where
  dimension = Tagged 0
  basisIndex = Tagged absurd
  indexBasis = Tagged $ const undefined
  completeBasis = Tagged []
  asPackedVector Origin = HMat.fromList []
  fromPackedVector _ = Origin
instance FiniteDimensional ℝ where
  dimension = Tagged 1
  basisIndex = Tagged $ \() -> 0
  indexBasis = Tagged $ \0 -> ()
  completeBasis = Tagged [()]
  asPackedVector x = HMat.fromList [x]
  asPackedMatrix f = HMat.asRow . asPackedVector $ atBasis f ()
  fromPackedVector v = v HMat.! 0
instance (FiniteDimensional a, FiniteDimensional b, Scalar a~Scalar b)
            => FiniteDimensional (a,b) where
  dimension = tupDim
   where tupDim :: ∀ a b.(FiniteDimensional a,FiniteDimensional b)=>Tagged(a,b)Int
         tupDim = Tagged $ da+db
          where (Tagged da)=dimension::Tagged a Int; (Tagged db)=dimension::Tagged b Int
  basisIndex = basId
   where basId :: ∀ a b . (FiniteDimensional a, FiniteDimensional b)
                     => Tagged (a,b) (Either (Basis a) (Basis b) -> Int)
         basId = Tagged basId'
          where basId' (Left ba) = basIda ba
                basId' (Right bb) = da + basIdb bb
                (Tagged da) = dimension :: Tagged a Int
                (Tagged basIda) = basisIndex :: Tagged a (Basis a->Int)
                (Tagged basIdb) = basisIndex :: Tagged b (Basis b->Int)
  indexBasis = basId
   where basId :: ∀ a b . (FiniteDimensional a, FiniteDimensional b)
                     => Tagged (a,b) (Int -> Either (Basis a) (Basis b))
         basId = Tagged basId'
          where basId' i | i < da     = Left $ basIda i
                         | otherwise  = Right . basIdb $ i - da
                (Tagged da) = dimension :: Tagged a Int
                (Tagged basIda) = indexBasis :: Tagged a (Int->Basis a)
                (Tagged basIdb) = indexBasis :: Tagged b (Int->Basis b)
  completeBasis = cb
   where cb :: ∀ a b . (FiniteDimensional a, FiniteDimensional b)
                     => Tagged (a,b) [Either (Basis a) (Basis b)]
         cb = Tagged $ map Left cba ++ map Right cbb
          where (Tagged cba) = completeBasis :: Tagged a [Basis a]
                (Tagged cbb) = completeBasis :: Tagged b [Basis b]
  asPackedVector (a,b) = HMat.vjoin [asPackedVector a, asPackedVector b]
  fromPackedVector = fPV
   where fPV :: ∀ a b . (FiniteDimensional a, FiniteDimensional b, Scalar a~Scalar b)
                     => HMat.Vector (Scalar a) -> (a,b)
         fPV v = (fromPackedVector l, fromPackedVector r)
          where (Tagged da) = dimension :: Tagged a Int
                (Tagged db) = dimension :: Tagged b Int
                l = HMat.subVector 0 da v
                r = HMat.subVector da db v
              
instance (FiniteDimensional y, FiniteDimensional x) => AdditiveGroup (x⊗y) where
  zeroV = DensTensProd $ (0 HMat.>< 0) []
  negateV (DensTensProd v) = DensTensProd $ negate v
  DensTensProd v ^+^ DensTensProd w
   | HMat.size v == (0,0)  = DensTensProd w
   | HMat.size w == (0,0)  = DensTensProd v
   | otherwise             = DensTensProd $ v + w

instance (FiniteDimensional y, FiniteDimensional x) => VectorSpace (x⊗y) where
  type Scalar (x⊗y) = Scalar y
  μ *^ DensTensProd v = DensTensProd $ HMat.scale μ v

instance (FiniteDimensional y, FiniteDimensional x) => InnerSpace (x⊗y) where
  DensTensProd v <.> DensTensProd w
   | HMat.size v == (0,0)  = 0
   | HMat.size w == (0,0)  = 0
   | otherwise             = HMat.flatten v `HMat.dot` HMat.flatten w

instance (FiniteDimensional y, FiniteDimensional x) => HasBasis (x⊗y) where
  type Basis (x⊗y) = (Basis x, Basis y)
  basisValue = bvt
   where bvt :: ∀ x y . (FiniteDimensional x, FiniteDimensional y)
                       => (Basis x, Basis y) -> x ⊗ y
         bvt (bx,by) = DensTensProd $ HMat.assoc (nx,ny) 0 [((i,j),1)]
          where Tagged nx = dimension :: Tagged x Int
                Tagged ny = dimension :: Tagged y Int
                Tagged i = ($bx) <$> basisIndex :: Tagged x Int
                Tagged j = ($by) <$> basisIndex :: Tagged y Int
  decompose = dct
   where dct :: ∀ x y . (FiniteDimensional x, FiniteDimensional y)
                       => x ⊗ y -> [((Basis x, Basis y), Scalar y)]
         dct (DensTensProd m) = zip [(i,j) | i <- cbx, j <- cby]
                                (HMat.toList $ HMat.flatten m)
          where Tagged cbx = completeBasis :: Tagged x [Basis x]
                Tagged cby = completeBasis :: Tagged y [Basis y]
  decompose' = dct
   where dct :: ∀ x y . (FiniteDimensional x, FiniteDimensional y)
                       => x ⊗ y -> (Basis x, Basis y) -> Scalar y
         dct (DensTensProd m) (bi, bj) = m `HMat.atIndex` (bxi bi, byj bj)
          where Tagged bxi = basisIndex :: Tagged x (Basis x -> Int)
                Tagged byj = basisIndex :: Tagged y (Basis y -> Int)
               
instance (FiniteDimensional a, FiniteDimensional b, Scalar a ~ Scalar b)
                                     => FiniteDimensional (a⊗b) where
  dimension = tensDim
   where tensDim :: ∀ a b.(FiniteDimensional a,FiniteDimensional b)=>Tagged(a⊗b)Int
         tensDim = Tagged $ da*db
          where (Tagged da)=dimension::Tagged a Int; (Tagged db)=dimension::Tagged b Int
  basisIndex = basId
   where basId :: ∀ a b . (FiniteDimensional a, FiniteDimensional b)
                     => Tagged (a⊗b) ((Basis a, Basis b) -> Int)
         basId = Tagged basId'
          where basId' (ba,bb) = db*basIda ba + basIdb bb
                (Tagged db) = dimension :: Tagged b Int
                (Tagged basIda) = basisIndex :: Tagged a (Basis a->Int)
                (Tagged basIdb) = basisIndex :: Tagged b (Basis b->Int)
  indexBasis = basId
   where basId :: ∀ a b . (FiniteDimensional a, FiniteDimensional b)
                     => Tagged (a⊗b) (Int -> (Basis a, Basis b))
         basId = Tagged basId'
          where basId' i = let (ia,ib) = i`divMod`db
                           in (basIda ia, basIdb ib)
                (Tagged db) = dimension :: Tagged b Int
                (Tagged basIda) = indexBasis :: Tagged a (Int->Basis a)
                (Tagged basIdb) = indexBasis :: Tagged b (Int->Basis b)
  completeBasis = cb
   where cb :: ∀ a b . (FiniteDimensional a, FiniteDimensional b)
                     => Tagged (a⊗b) [(Basis a, Basis b)]
         cb = Tagged $ [(ba,bb) | ba<-cba, bb<-cbb]
          where (Tagged cba) = completeBasis :: Tagged a [Basis a]
                (Tagged cbb) = completeBasis :: Tagged b [Basis b]
  asPackedVector (DensTensProd m) = HMat.flatten m
  fromPackedVector = fPV
   where fPV :: ∀ a b . (FiniteDimensional a, FiniteDimensional b, Scalar a~Scalar b)
                     => HMat.Vector (Scalar a) -> (a⊗b)
         fPV v = DensTensProd $ HMat.reshape db v
          where (Tagged db) = dimension :: Tagged b Int
  
  
instance (SmoothScalar x, KnownNat n) => FiniteDimensional (FreeVect n x) where
  dimension = natTagPænultimate
  basisIndex = Tagged getInRange
  indexBasis = Tagged InRange
  asPackedVector (FreeVect arr) = Arr.convert arr
  fromPackedVector arr = FreeVect (Arr.convert arr)
  -- asPackedMatrix = _ -- could be done quite efficiently here!
                                                          


-- | Semantically the same as @'Tagged' tag refvs@, but directly uses the
--   packed-vector array representation.
-- 
--   The tag should really be kind-polymorphic, but at least GHC-7.8 doesn't quite
--   handle the associated types of the manifold classes then.
newtype FinVecArrRep (tag :: * -> *) refvs scalar
      = FinVecArrRep { getFinVecArrRep :: HMat.Vector scalar }

instance (SmoothScalar s) => AffineSpace (FinVecArrRep t b s) where
  type Diff (FinVecArrRep t b s) = FinVecArrRep t b s
  (.-.) = (^-^)
  (.+^) = (^+^)
  
instance (SmoothScalar s) => AdditiveGroup (FinVecArrRep t b s) where
  zeroV = FinVecArrRep $ 0 HMat.|> []
  negateV (FinVecArrRep v) = FinVecArrRep $ negate v
  FinVecArrRep v ^+^ FinVecArrRep w
   | HMat.size v == 0  = FinVecArrRep w
   | HMat.size w == 0  = FinVecArrRep v
   | otherwise         = FinVecArrRep $ v + w

instance (SmoothScalar s) => VectorSpace (FinVecArrRep t b s) where
  type Scalar (FinVecArrRep t b s) = s
  μ *^ FinVecArrRep v = FinVecArrRep $ HMat.scale μ v

instance (SmoothScalar s) => InnerSpace (FinVecArrRep t b s) where
  FinVecArrRep v <.> FinVecArrRep w
   | HMat.size v == 0  = 0
   | HMat.size w == 0  = 0
   | otherwise         = v`HMat.dot`w

concreteArrRep :: (SmoothScalar s, FiniteDimensional r, Scalar r ~ s)
           => Isomorphism (->) r (FinVecArrRep t r s)
concreteArrRep = Isomorphism (FinVecArrRep     . asPackedVector)
                             (fromPackedVector . getFinVecArrRep)

(⊕) :: ∀ t s v w . ( SmoothScalar s, FiniteDimensional v, FiniteDimensional w
                   , Scalar v ~ s, Scalar w ~ s )
          => FinVecArrRep t v s -> FinVecArrRep t w s -> FinVecArrRep t (v,w) s
FinVecArrRep v ⊕ FinVecArrRep w
  | HMat.size v + HMat.size w == 0  = FinVecArrRep v
  | HMat.size v == 0                = FinVecArrRep $ HMat.vjoin [HMat.konst 0 nv, w]
  | HMat.size w == 0                = FinVecArrRep $ HMat.vjoin [v, HMat.konst 0 nw]
  | otherwise                       = FinVecArrRep $ HMat.vjoin [v,w]
 where Tagged nv = dimension :: Tagged v Int
       Tagged nw = dimension :: Tagged w Int

splitArrRep :: ∀ t s v w . ( SmoothScalar s, FiniteDimensional v, FiniteDimensional w
                   , Scalar v ~ s, Scalar w ~ s )
          => FinVecArrRep t (v,w) s -> (FinVecArrRep t v s, FinVecArrRep t w s)
splitArrRep (FinVecArrRep vw)
  | HMat.size vw == 0   = (FinVecArrRep vw, FinVecArrRep vw)
  | otherwise           = ( FinVecArrRep $ HMat.subVector 0 nv vw
                          , FinVecArrRep $ HMat.subVector nv nw vw )
 where Tagged nv = dimension :: Tagged v Int
       Tagged nw = dimension :: Tagged w Int
                  

instance (SmoothScalar s, FiniteDimensional r, Scalar r ~ s)
                 => HasBasis (FinVecArrRep t r s) where
  type Basis (FinVecArrRep t r s) = Basis r
  basisValue = (concreteArrRep$->$) . basisValue
  decompose = decompose . (concreteArrRep$<-$)
  decompose' = decompose' . (concreteArrRep$<-$)

instance (SmoothScalar s, FiniteDimensional r, Scalar r ~ s)
                 => FiniteDimensional (FinVecArrRep t r s) where
  dimension = d
   where d :: ∀ t r s . FiniteDimensional r => Tagged (FinVecArrRep t r s) Int
         d = Tagged n
          where Tagged n = dimension :: Tagged r Int
  indexBasis = d
   where d :: ∀ t r s . FiniteDimensional r => Tagged (FinVecArrRep t r s) (Int -> Basis r)
         d = Tagged n
          where Tagged n = indexBasis :: Tagged r (Int -> Basis r)
  basisIndex = d
   where d :: ∀ t r s . FiniteDimensional r => Tagged (FinVecArrRep t r s) (Basis r -> Int)
         d = Tagged n
          where Tagged n = basisIndex :: Tagged r (Basis r -> Int)
  asPackedVector = apv
   where apv :: ∀ t r s . (FiniteDimensional r, SmoothScalar s)
                     => FinVecArrRep t r s -> HMat.Vector s
         apv (FinVecArrRep v)
             | HMat.size v == 0  = HMat.konst 0 n
             | otherwise         = v
          where Tagged n = dimension :: Tagged r Int
  fromPackedVector = FinVecArrRep


instance (NaturallyEmbedded m r, FiniteDimensional r, s ~ Scalar r)
                 => NaturallyEmbedded m (FinVecArrRep t r s) where
  embed = (concreteArrRep$<-$) . embed
  coEmbed = coEmbed . (concreteArrRep$->$)
                     

