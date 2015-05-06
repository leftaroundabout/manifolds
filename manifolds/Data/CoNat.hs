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

natTagLast :: forall n f n' . (KnownNat n, Num n') => Tagged (f n) n'
natTagLast = retag (theNatN :: Tagged n n')
natTagPænultimate :: forall n f n' x . (KnownNat n, Num n') => Tagged (f n x) n'
natTagPænultimate = retag (theNatN :: Tagged n n')
natTagAntepænultimate :: forall n f n' x y . (KnownNat n, Num n') => Tagged (f n x y) n'
natTagAntepænultimate = retag (theNatN :: Tagged n n')

natSelfSucc :: forall n . KnownNat n => Tagged (S n) Nat
natSelfSucc = Tagged $ S n
 where (Tagged n) = theNat :: Tagged n Nat
natSelfSuccN :: forall n a . (KnownNat n, Num a) => Tagged (S n) a
natSelfSuccN = Tagged $ n + 1
 where (Tagged n) = theNatN :: Tagged n a

class KnownNat (n :: Nat) where
  theNat :: Tagged n Nat
  theNatN :: Num n' => Tagged n n'
            
  cozero :: s Z -> Option (s n)
  cozeroT :: c Z x -> Option (c n x)
            
  cosucc :: (forall k . KnownNat k => s (S k)) -> Option (s n)
  fCosucc :: Hask.Alternative f => (forall k . KnownNat k => f (s (S k))) -> f (s n)
  cosuccT :: (forall k . KnownNat k => s (S k) x) -> Option (s n x)
  fCosuccT :: Hask.Alternative f => (forall k . KnownNat k => f (s (S k) x)) -> f (s n x)
  
  coNat :: (s Z->r) -> ( forall k . KnownNat k => s (S k) -> r ) -> s n -> r
  coNatT :: (c Z x->r) -> ( forall k . KnownNat k => c (S k) x -> r ) -> c n x -> r
  
  coInduce :: s Z -> (forall k . KnownNat k => s k -> s (S k)) -> s n
  coInduceT :: c Z x -> (forall k . KnownNat k => c k x -> c (S k) x) -> c n x


instance KnownNat Z where
  theNat = Tagged Z
  theNatN = Tagged 0
  cozero  = pure; cosucc _  = Hask.empty; fCosucc _  = Hask.empty
  cozeroT = pure; cosuccT _ = Hask.empty; fCosuccT _ = Hask.empty
  coNat f _ = f; coNatT f _ = f
  coInduce s _ = s
  coInduceT s _ = s
instance (KnownNat n) => KnownNat (S n) where
  theNat = natSelfSucc
  theNatN = natSelfSuccN
  cozero _  = Hask.empty; cosucc v  = pure v; fCosucc v  = v
  cozeroT _ = Hask.empty; cosuccT v = pure v; fCosuccT v = v
  coNat _ f = f; coNatT _ f = f
  coInduce s f = f $ coInduce s f
  coInduceT s f = f $ coInduceT s f


class (KnownNat k, KnownNat j) => (≤) (k::Nat) (j::Nat) where
  succToMatch :: (forall n . KnownNat n => s n -> s (S n)) -> s k -> s j
  succToMatchT :: (forall n . KnownNat n => c n x -> c (S n) x) -> c k x -> c j x

instance (KnownNat n) => Z ≤ n where
  succToMatch f s = coInduce s f
  succToMatchT f s = coInduceT s f
instance (k ≤ j) => (S k) ≤ (S j) where
  succToMatch = stm
   where stm :: ∀ k j s . (k≤j) => (forall n . KnownNat n => s n -> s (S n))
                                     -> s (S k) -> s (S j)
         stm f s = let (Tagged r) = succToMatchT ff
                                      (Tagged s :: Tagged k (s (S k)))
                                                :: Tagged j (s (S j))
                       ff :: ∀n. KnownNat n => Tagged n (s (S k)) -> Tagged (S n) (s (S j))
                       ff (Tagged q) = Tagged $ f q
                   in r



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

instance (KnownNat n) => Hask.Applicative (FreeVect n) where
  pure = replicVector
  (<*>) = perfectZipWith ($)

type x ^ n = FreeVect n x

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


replicVector :: forall n x . KnownNat n => x -> FreeVect n x
replicVector = FreeVect . Arr.replicate n
 where (Tagged n) = theNatN :: Tagged n Int


freeVector :: forall l n x . (KnownNat n, Hask.Foldable l) => l x -> Option (FreeVect n x)
freeVector c'
    | length c == n  = pure . FreeVect $ Arr.fromList c
    | otherwise      = Hask.empty
 where (Tagged n) = theNatN :: Tagged n Int
       c = Hask.toList c'

-- | Free vector containing the (0-based) indices of its fields as entries.
indices :: forall n n' . (KnownNat n, Num n') => FreeVect n n'
indices = FreeVect $ Arr.enumFromN 0 n
 where (Tagged n) = theNatN :: Tagged n Int


perfectZipWith :: forall n a b c . KnownNat n
        => (a->b->c) -> FreeVect n a -> FreeVect n b -> FreeVect n c
perfectZipWith f (FreeVect va) (FreeVect vb) = FreeVect $ Arr.zipWith f va vb



freeCons :: a -> FreeVect n a -> FreeVect (S n) a
freeCons x (FreeVect xs) = FreeVect $ Arr.cons x xs

freeSnoc :: FreeVect n a -> a -> FreeVect (S n) a
freeSnoc (FreeVect xs) x = FreeVect $ Arr.snoc xs x


