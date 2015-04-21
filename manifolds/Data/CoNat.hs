-- |
-- Module      : Data.CoNat
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

module Data.CoNat where

import Data.Tagged
import Data.Semigroup

import Data.MemoTrie
import Data.VectorSpace
import Data.AffineSpace
import Data.Basis
import Data.AdditiveGroup
    
import qualified Prelude as Hask hiding(foldl)
import qualified Control.Applicative as Hask
import qualified Control.Monad       as Hask
import qualified Data.Foldable       as Hask


import Control.Category.Constrained.Prelude hiding ((^))


import qualified Data.Vector as Arr
import qualified Numeric.LinearAlgebra.HMatrix as HMat


    
-- | Mainly intended to be used as a data kind.
--   Of course, we'd rather use "GHC.TypeLits" naturals, but they aren't mature enough yet.
data Nat = Z | S Nat deriving (Eq)

natToInt :: Nat -> Int
natToInt Z = 0; natToInt (S n) = 1 + natToInt n

fromNat :: Num a => Nat -> a
fromNat = fromIntegral . natToInt

class KnownNat (n :: Nat) where
  theNat :: Tagged n Nat
  theNatN :: Num n' => Tagged n n'
            
  cozero :: s Z -> Option (s n)
  cozeroT :: c Z x -> Option (c n x)
             
  cosucc :: (forall k . KnownNat k => s (S k)) -> Option (s n)
  fCosucc :: Hask.Alternative f => (forall k . KnownNat k => f (s (S k))) -> f (s n)
  cosuccT :: (forall k . KnownNat k => s (S k) x) -> Option (s n x)
  fCosuccT :: Hask.Alternative f => (forall k . KnownNat k => f (s (S k) x)) -> f (s n x)


instance KnownNat Z where
  theNat = Tagged Z
  theNatN = Tagged 0
  cozero  = pure; cosucc _  = Hask.empty; fCosucc _  = Hask.empty
  cozeroT = pure; cosuccT _ = Hask.empty; fCosuccT _ = Hask.empty
instance (KnownNat n) => KnownNat (S n) where
  theNat = fmap S theNat
  theNatN = fmap (+1) theNatN
  cozero _  = Hask.empty; cosucc v  = pure v; fCosucc v  = v
  cozeroT _ = Hask.empty; cosuccT v = pure v; fCosuccT v = v



newtype Range (n::Nat) = InRange { getInRange :: Int -- ^ MUST be between 0 and @n-1@.
                                 }

clipToRange :: forall n . KnownNat n => Int -> Option (Range n)
clipToRange = \k -> if k < n then Hask.pure $ InRange n
                             else Hask.empty
 where (Tagged n) = theNatN :: Tagged n Int
                       
instance KnownNat n => HasTrie (Range n) where
  data Range n :->: x = RangeTrie (FreeVect n x)
  trie = RangeTrie . \f -> fmap f ids
   where ids = fmap InRange indices
  untrie (RangeTrie (FreeVect arr)) = \(InRange i) -> arr Arr.! i
  enumerate (RangeTrie (FreeVect arr)) = Arr.ifoldr (\i x l -> (InRange i, x) : l) [] arr


newtype FreeVect (n::Nat) x = FreeVect
    { getFreeVect :: Arr.Vector x -- ^ MUST have length @n@.
    } deriving (Hask.Functor, Hask.Foldable)

instance (Num x, KnownNat n) => AffineSpace (FreeVect n x) where
  type Diff (FreeVect n x) = FreeVect n x
  (.-.) = perfectZipWith (-)
  (.+^) = perfectZipWith (+)
instance (Num x, KnownNat n) => AdditiveGroup (FreeVect n x) where
  zeroV = replicVector 0
  negateV = fmap negate
  (^+^) = perfectZipWith (+)
instance (Num x, KnownNat n) => VectorSpace (FreeVect n x) where
  type Scalar (FreeVect n x) = x
  (*^) = fmap . (*)
instance (Num x, AdditiveGroup x, KnownNat n) => InnerSpace (FreeVect n x) where
  FreeVect v<.>FreeVect w = Arr.sum $ Arr.zipWith (*) v w
instance (Num x, KnownNat n) => HasBasis (FreeVect n x) where
  type Basis (FreeVect n x) = Range n
  basisValue = \(InRange i) -> fmap (\k -> if i==k then 1 else 0) ids
   where ids = indices
  decompose (FreeVect arr) = Arr.ifoldr (\i x l -> (InRange i, x) : l) [] arr
  decompose' (FreeVect arr) (InRange i) = arr Arr.! i


freeVectDimension :: forall n x . KnownNat n => Tagged (FreeVect n x) Int
freeVectDimension = retag (theNatN :: Tagged n Int)

replicVector :: forall n x . KnownNat n => x -> FreeVect n x
replicVector = FreeVect . Arr.replicate n
 where (Tagged n) = theNatN :: Tagged n Int


freeVector :: forall n x . KnownNat n => [x] -> Option (FreeVect n x)
freeVector c
    | length c == n  = pure . FreeVect $ Arr.fromList c
    | otherwise      = Hask.empty
 where (Tagged n) = theNatN :: Tagged n Int

-- | Free vector containing the (0-based) indices of its fields as entries.
indices :: forall n n' . (KnownNat n, Num n') => FreeVect n n'
indices = FreeVect $ Arr.enumFromN 0 n
 where (Tagged n) = theNatN :: Tagged n Int


perfectZipWith :: forall n a b c . KnownNat n
        => (a->b->c) -> FreeVect n a -> FreeVect n b -> FreeVect n c
perfectZipWith f (FreeVect va) (FreeVect vb) = FreeVect $ Arr.zipWith f va vb
