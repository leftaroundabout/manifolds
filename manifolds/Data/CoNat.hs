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


import Control.Category.Constrained.Prelude hiding ((^))
import Data.Traversable.Constrained


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
  
  ftorCoInduce :: f (s Z) -> (forall k . KnownNat k => f (s k) -> f (s (S k))) -> f (s n)
  ftorCoInduceT :: f (c Z x) -> (forall k . KnownNat k => f (c k x) -> f (c (S k) x))
                         -> f (c n x)


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


class (KnownNat k, KnownNat j) => (≤) (k::Nat) (j::Nat) where
  succToMatch :: (∀ n . KnownNat n => b n -> b (S n)) -> b k -> b j

succToMatchT :: (k≤j) => (∀ n . KnownNat n => c n x -> c (S n) x) -> c k x -> c j x
succToMatchT f = getNatTagAtPænultimate
       . succToMatch (mapNatTagAtPænultimate f) . NatTagAtPænultimate
succToMatchTT :: (k≤j) => (∀ n . KnownNat n => d n x y -> d (S n) x y) -> d k x y -> d j x y
succToMatchTT f = getNatTagAtAntepænultimate
       . succToMatch (mapNatTagAtAntepænultimate f) . NatTagAtAntepænultimate
succToMatchTTT :: (k≤j) => (∀ n . KnownNat n => e n x y z -> e (S n) x y z)
                    -> e k x y z -> e j x y z
succToMatchTTT f = getNatTagAtPreantepænultimate
       . succToMatch (mapNatTagAtPreantepænultimate f) . NatTagAtPreantepænultimate

ftorSuccToMatch :: (k≤j) =>
           (∀ n . KnownNat n => f (b n) -> f (b (S n))) -> f (b k) -> f (b j)
ftorSuccToMatch f = getNatTagAtFtorUltimate
       . succToMatch (mapNatTagAtFtorUltimate f) . NatTagAtFtorUltimate
ftorSuccToMatchT :: (k≤j) => (∀ n . KnownNat n => f (c n x) -> f (c (S n) x)) -> f (c k x) -> f (c j x)
ftorSuccToMatchT f = getNatTagAtFtorPænultimate
       . succToMatch (mapNatTagAtFtorPænultimate f) . NatTagAtFtorPænultimate
ftorSuccToMatchTT :: (k≤j) => (∀ n . KnownNat n => f (d n x y) -> f (d (S n) x y)) -> f (d k x y) -> f (d j x y)
ftorSuccToMatchTT f = getNatTagAtFtorAntepænultimate
       . succToMatch (mapNatTagAtFtorAntepænultimate f) . NatTagAtFtorAntepænultimate


newtype Cosucc'd s n = Cosucc'd { getSucc'd :: s (S n) }
cosucc'dSucc :: ∀ s n . KnownNat n => (s (S n) -> s (S (S n)))
                        -> Cosucc'd s n -> Cosucc'd s (S n)
cosucc'dSucc f (Cosucc'd x) = Cosucc'd $ f x

newtype FtorCosucc'd f s n = FtorCosucc'd { getFtorSucc'd :: f (s (S n)) }
ftorCosucc'dSucc :: ∀ f s n . KnownNat n => (f (s (S n)) -> f(s (S (S n))))
                        -> FtorCosucc'd f s n -> FtorCosucc'd f s (S n)
ftorCosucc'dSucc f (FtorCosucc'd x) = FtorCosucc'd $ f x

instance (KnownNat n) => Z ≤ n where
  succToMatch f s = coInduce s f
instance (k ≤ j) => (S k) ≤ (S j) where
  succToMatch f s = let (Cosucc'd r) = succToMatch (cosucc'dSucc f) (Cosucc'd s) in r


class (i ≤ j, j ≤ k, i ≤ k) => WeakOrdTriple i j k where
  succToMatchLtd :: (∀ n . (KnownNat n, S n≤k) => b n -> b (S n)) -> Tagged k (b i -> b j)

succToMatchTLtd :: (WeakOrdTriple i j k) => 
           (∀ n . (KnownNat n, S n≤k) => c n x -> c (S n) x) -> Tagged k (c i x -> c j x)
succToMatchTLtd f = fmap ((getNatTagAtPænultimate .) . (. NatTagAtPænultimate))
                            $ succToMatchLtd (mapNatTagAtPænultimate f)
succToMatchTTLtd :: (WeakOrdTriple i j k) => 
           (∀ n . (KnownNat n, S n≤k) => d n x y -> d (S n) x y) -> Tagged k (d i x y -> d j x y)
succToMatchTTLtd f = fmap ((getNatTagAtAntepænultimate .) . (. NatTagAtAntepænultimate))
                            $ succToMatchLtd (mapNatTagAtAntepænultimate f)
succToMatchTTTLtd :: (WeakOrdTriple i j k) => 
           (∀ n . (KnownNat n, S n≤k) => e n x y z -> e (S n) x y z) -> Tagged k (e i x y z -> e j x y z)
succToMatchTTTLtd f = fmap ((getNatTagAtPreantepænultimate .) . (. NatTagAtPreantepænultimate))
                            $ succToMatchLtd (mapNatTagAtPreantepænultimate f)

ftorSuccToMatchLtd :: (WeakOrdTriple i j k) => 
           (∀ n . (KnownNat n, S n≤k) => f (b n) -> f (b (S n))) -> Tagged k (f (b i) -> f (b j))
ftorSuccToMatchLtd f = fmap ((getNatTagAtFtorUltimate .) . (. NatTagAtFtorUltimate))
                            $ succToMatchLtd (mapNatTagAtFtorUltimate f)
ftorSuccToMatchTLtd :: (WeakOrdTriple i j k) => 
           (∀ n . (KnownNat n, S n≤k) => f (c n x) -> f (c (S n) x)) -> Tagged k (f (c i x) -> f (c j x))
ftorSuccToMatchTLtd f = fmap ((getNatTagAtFtorPænultimate .) . (. NatTagAtFtorPænultimate))
                            $ succToMatchLtd (mapNatTagAtFtorPænultimate f)
ftorSuccToMatchTTLtd :: (WeakOrdTriple i j k) => 
           (∀ n . (KnownNat n, S n≤k) => f (d n x y) -> f (d (S n) x y)) -> Tagged k (f (d i x y) -> f (d j x y))
ftorSuccToMatchTTLtd f = fmap ((getNatTagAtFtorAntepænultimate .) . (. NatTagAtFtorAntepænultimate))
                            $ succToMatchLtd (mapNatTagAtFtorAntepænultimate f)

instance (KnownNat n) => WeakOrdTriple Z Z n where
  succToMatchLtd _ = Tagged id

instance (WeakOrdTriple Z j k, S j ≤ k) => WeakOrdTriple Z (S j) k where
  succToMatchLtd = stml
   where stml :: ∀ j k b . (WeakOrdTriple Z j k, S j ≤ k) => 
                    (∀ n . (KnownNat n, S n≤k) => b n -> b (S n)) -> Tagged k (b Z -> b (S j))
         stml f = Tagged $ f . f'
          where (Tagged f') = succToMatchLtd f :: Tagged k (b Z -> b j)

instance (WeakOrdTriple i j k)
                 => WeakOrdTriple (S i) (S j) (S k) where
  succToMatchLtd = stml
   where stml :: ∀ i j k b . (WeakOrdTriple i j k) => 
                      (∀ n . (KnownNat n, S n≤S k) => b n -> b (S n))
                          -> Tagged (S k) (b (S i) -> b (S j))
         stml f = Tagged $
                   \s -> let (Tagged ff) = succToMatchLtd ltdCsdf
                                             :: Tagged k (Cosucc'd b i -> Cosucc'd b j)
                             (Cosucc'd r) = ff (Cosucc'd s)
                         in r
          where ltdCsdf :: ∀ n . (KnownNat n, S n ≤ k) => Cosucc'd b n -> Cosucc'd b (S n)
                ltdCsdf = cosucc'dSucc f







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

freeSortBy :: forall n a . KnownNat n
        => (a->a->Ordering) -> a^n -> a^n
freeSortBy cmp (FreeVect xs) = FreeVect $ Arr.fromList (List.sortBy cmp $ Arr.toList xs)


freeCons :: a -> FreeVect n a -> FreeVect (S n) a
freeCons x (FreeVect xs) = FreeVect $ Arr.cons x xs

freeSnoc :: FreeVect n a -> a -> FreeVect (S n) a
freeSnoc (FreeVect xs) x = FreeVect $ Arr.snoc xs x




newtype AsHaskFunctor f x = AsHaskFunctor { runAsHaskFunctor :: f x }

instance (Functor f (->) (->)) => Hask.Functor (AsHaskFunctor f) where
  fmap f (AsHaskFunctor c) = AsHaskFunctor $ fmap f c
instance (Monoidal f (->) (->)) => Hask.Applicative (AsHaskFunctor f) where
  pure = runAsHaskFunctor . pure
  AsHaskFunctor fs <*> AsHaskFunctor xs = AsHaskFunctor . fmap (uncurry ($)) $ fzip (fs, xs)
