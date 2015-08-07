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
{-# LANGUAGE PolyKinds                  #-}

module Data.CoNat where

import Data.Tagged
import Data.Semigroup

import Data.MemoTrie
import Data.VectorSpace
import Data.AffineSpace
import Data.Basis
import Data.AdditiveGroup
import qualified Data.List as List
    
import qualified Prelude as Hask hiding(foldl)
import qualified Control.Applicative as Hask
import qualified Control.Monad       as Hask
import qualified Data.Foldable       as Hask
import qualified Data.Traversable    as Hask


import Control.Category.Constrained.Prelude hiding ((^), Foldable(..), Traversable(..))
import Data.Traversable.Constrained


import qualified Data.Vector as Arr
import qualified Numeric.LinearAlgebra.HMatrix as HMat

import Unsafe.Coerce

    
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
  
  ftorCoInduce :: f (s Z) -> (forall k . KnownNat k => f (s k) -> f (s (S k))) -> f (s n)
  ftorCoInduceT :: f (c Z x) -> (forall k . KnownNat k => f (c k x) -> f (c (S k) x))
                         -> f (c n x)

  tryToMatch :: KnownNat k => (∀ j . KnownNat j => b j -> b (S j)) -> b k -> Option (b n)


instance KnownNat Z where
  theNat = Tagged Z
  theNatN = Tagged 0
  cozero  = pure; cosucc _  = Hask.empty; fCosucc _  = Hask.empty
  cozeroT = pure; cosuccT _ = Hask.empty; fCosuccT _ = Hask.empty
  coNat f _ = f; coNatT f _ = f
  coInduce s _ = s
  coInduceT s _ = s
  ftorCoInduce s _ = s
  ftorCoInduceT s _ = s
  tryToMatch = ttmZ
   where ttmZ :: ∀ b k . KnownNat k
                    => (∀ j . KnownNat j => b j -> b (S j)) -> b k -> Option (b Z)
         ttmZ sc nf = case k of
                        Z -> return $ unsafeCoerce nf
                        S _ -> Hask.empty
          where (Tagged k) = theNat :: Tagged k Nat
instance (KnownNat n) => KnownNat (S n) where
  theNat = natSelfSucc
  theNatN = natSelfSuccN
  cozero _  = Hask.empty; cosucc v  = pure v; fCosucc v  = v
  cozeroT _ = Hask.empty; cosuccT v = pure v; fCosuccT v = v
  coNat _ f = f; coNatT _ f = f
  coInduce s f = f $ coInduce s f
  coInduceT s f = f $ coInduceT s f
  ftorCoInduce s f = f $ ftorCoInduce s f
  ftorCoInduceT s f = f $ ftorCoInduceT s f
  tryToMatch = ttmS
   where ttmS :: ∀ b k n . (KnownNat k, KnownNat n)
                    => (∀ j . KnownNat j => b j -> b (S j)) -> b k -> Option (b (S n))
         ttmS sc nf | k == sn    = return $ unsafeCoerce nf
                    | k <= sn    = tryToMatch sc $ sc nf
                    | otherwise  = Hask.empty
          where (Tagged k) = theNatN :: Tagged k Int
                (Tagged sn) = theNatN :: Tagged (S n) Int
                       


newtype NatTagAtPænultimate t x n
           = NatTagAtPænultimate { getNatTagAtPænultimate :: t n x }
mapNatTagAtPænultimate :: (s n x -> t m y)
    -> NatTagAtPænultimate s x n -> NatTagAtPænultimate t y m
mapNatTagAtPænultimate f (NatTagAtPænultimate x) = NatTagAtPænultimate $ f x

newtype NatTagAtAntepænultimate t x y n
           = NatTagAtAntepænultimate { getNatTagAtAntepænultimate :: t n x y }
mapNatTagAtAntepænultimate :: (s n w x -> t m y z)
    -> NatTagAtAntepænultimate s w x n -> NatTagAtAntepænultimate t y z m
mapNatTagAtAntepænultimate f (NatTagAtAntepænultimate x) = NatTagAtAntepænultimate $ f x

newtype NatTagAtPreantepænultimate t x y z n
           = NatTagAtPreantepænultimate { getNatTagAtPreantepænultimate :: t n x y z }
mapNatTagAtPreantepænultimate :: (s n u v w -> t m x y z)
    -> NatTagAtPreantepænultimate s u v w n -> NatTagAtPreantepænultimate t x y z m
mapNatTagAtPreantepænultimate f (NatTagAtPreantepænultimate x) = NatTagAtPreantepænultimate $ f x

newtype NatTagAtFtorUltimate f t n
           = NatTagAtFtorUltimate { getNatTagAtFtorUltimate :: f (t n) }
mapNatTagAtFtorUltimate :: (f (s n) -> f (t m))
    -> NatTagAtFtorUltimate f s n -> NatTagAtFtorUltimate f t m
mapNatTagAtFtorUltimate f (NatTagAtFtorUltimate x) = NatTagAtFtorUltimate $ f x

newtype NatTagAtFtorPænultimate f t x n
           = NatTagAtFtorPænultimate { getNatTagAtFtorPænultimate :: f (t n x) }
mapNatTagAtFtorPænultimate :: (f (s n x) -> f (t m y))
    -> NatTagAtFtorPænultimate f s x n -> NatTagAtFtorPænultimate f t y m
mapNatTagAtFtorPænultimate f (NatTagAtFtorPænultimate x) = NatTagAtFtorPænultimate $ f x

newtype NatTagAtFtorAntepænultimate f t x y n
           = NatTagAtFtorAntepænultimate { getNatTagAtFtorAntepænultimate :: f (t n x y) }
mapNatTagAtFtorAntepænultimate :: (f (s n w x) -> f (t m y z))
    -> NatTagAtFtorAntepænultimate f s w x n -> NatTagAtFtorAntepænultimate f t y z m
mapNatTagAtFtorAntepænultimate f (NatTagAtFtorAntepænultimate x) = NatTagAtFtorAntepænultimate $ f x


tryToMatchT :: (KnownNat k, KnownNat j)
                   => (∀ n . KnownNat n => c n x -> c (S n) x) -> c k x -> Option (c j x)
tryToMatchT f = fmap getNatTagAtPænultimate
       . tryToMatch (mapNatTagAtPænultimate f) . NatTagAtPænultimate
tryToMatchTT ::(KnownNat k, KnownNat j) => (∀ n . KnownNat n => d n x y -> d (S n) x y) -> d k x y -> Option (d j x y)
tryToMatchTT f = fmap getNatTagAtAntepænultimate
       . tryToMatch (mapNatTagAtAntepænultimate f) . NatTagAtAntepænultimate
tryToMatchTTT :: (KnownNat k, KnownNat j) => (∀ n . KnownNat n => e n x y z -> e (S n) x y z)
                    -> e k x y z -> Option (e j x y z)
tryToMatchTTT f = fmap getNatTagAtPreantepænultimate
       . tryToMatch (mapNatTagAtPreantepænultimate f) . NatTagAtPreantepænultimate

ftorTryToMatch :: (KnownNat k, KnownNat j) =>
           (∀ n . KnownNat n => f (b n) -> f (b (S n))) -> f (b k) -> Option (f (b j))
ftorTryToMatch f = fmap getNatTagAtFtorUltimate
       . tryToMatch (mapNatTagAtFtorUltimate f) . NatTagAtFtorUltimate
ftorTryToMatchT :: (KnownNat k, KnownNat j) => (∀ n . KnownNat n => f (c n x) -> f (c (S n) x)) -> f (c k x) -> Option (f (c j x))
ftorTryToMatchT f = fmap getNatTagAtFtorPænultimate
       . tryToMatch (mapNatTagAtFtorPænultimate f) . NatTagAtFtorPænultimate
ftorTryToMatchTT :: (KnownNat k, KnownNat j) => (∀ n . KnownNat n => f (d n x y) -> f (d (S n) x y)) -> f (d k x y) -> Option (f (d j x y))
ftorTryToMatchTT f = fmap getNatTagAtFtorAntepænultimate
       . tryToMatch (mapNatTagAtFtorAntepænultimate f) . NatTagAtFtorAntepænultimate






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
instance (KnownNat n) => Traversable (FreeVect n) (FreeVect n) (->) (->) where
  traverse f (FreeVect v) = fmap FreeVect . runAsHaskFunctor
                              $ Hask.traverse (AsHaskFunctor . f) v
instance (KnownNat n, Show x) => Show (FreeVect n x) where
  show (FreeVect v) = "(freeTuple $->$ ("
            ++ List.intercalate "," [show x | x<-Arr.toList v] ++ "))"

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
    | List.length c == n  = pure . FreeVect $ Arr.fromList c
    | otherwise           = Hask.empty
 where (Tagged n) = theNatN :: Tagged n Int
       c = Hask.toList c'

-- | Free vector containing the (0-based) indices of its fields as entries.
indices :: forall n n' . (KnownNat n, Num n') => FreeVect n n'
indices = FreeVect $ Arr.enumFromN 0 n
 where (Tagged n) = theNatN :: Tagged n Int


perfectZipWith :: forall n a b c . KnownNat n
        => (a->b->c) -> FreeVect n a -> FreeVect n b -> FreeVect n c
perfectZipWith f (FreeVect va) (FreeVect vb) = FreeVect $ Arr.zipWith f va vb

freeSortBy :: forall n a . KnownNat n
        => (a->a->Ordering) -> a^n -> a^n
freeSortBy cmp (FreeVect xs) = FreeVect $ Arr.fromList (List.sortBy cmp $ Arr.toList xs)

freeRotate :: ∀ n a . KnownNat n => Int -> a^n -> a^n
freeRotate j' = \(FreeVect v) -> FreeVect $ Arr.unsafeBackpermute v rot
 where (Tagged n) = theNatN :: Tagged n Int
       rot = Arr.enumFromN j (n-j) Arr.++ Arr.enumFromN 0 j
       j = j'`mod`n



freeCons :: a -> FreeVect n a -> FreeVect (S n) a
freeCons x (FreeVect xs) = FreeVect $ Arr.cons x xs

freeSnoc :: FreeVect n a -> a -> FreeVect (S n) a
freeSnoc (FreeVect xs) x = FreeVect $ Arr.snoc xs x




newtype AsHaskFunctor f x = AsHaskFunctor { runAsHaskFunctor :: f x }

instance (Functor f (->) (->)) => Hask.Functor (AsHaskFunctor f) where
  fmap f (AsHaskFunctor c) = AsHaskFunctor $ fmap f c
instance (Monoidal f (->) (->)) => Hask.Applicative (AsHaskFunctor f) where
  pure x = fmap (const x) . AsHaskFunctor $ pureUnit ()
  AsHaskFunctor fs <*> AsHaskFunctor xs = AsHaskFunctor . fmap (uncurry ($)) $ fzip (fs, xs)
