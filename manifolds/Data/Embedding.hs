-- |
-- Module      : Data.Embedding
-- Copyright   : (c) Justus Sagemüller 2015
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsag $ hvl.no
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

module Data.Embedding where

import qualified Prelude as Hask hiding(foldl)
import qualified Control.Applicative as Hask
import qualified Control.Monad       as Hask
import qualified Data.Foldable       as Hask


import Control.Category.Constrained.Prelude hiding ((^))
import Control.Arrow.Constrained




data Isomorphism c a b = Isomorphism { forwardIso :: c a b
                                     , backwardIso :: c b a }

infixr 0 $->$, $<-$
($->$) :: (Function c, Object c a, Object c b) => Isomorphism c a b -> a -> b
Isomorphism f _ $->$ x = f $ x

($<-$) :: (Function c, Object c b, Object c a) => Isomorphism c a b -> b -> a
Isomorphism _ p $<-$ y = p $ y

fromInversePair :: c a b -> c b a -> Isomorphism c a b
fromInversePair = Isomorphism

perfectInvert :: Isomorphism c a b -> Isomorphism c b a
perfectInvert (Isomorphism f b) = Isomorphism b f

instance (Category c) => Category (Isomorphism c) where
  type Object (Isomorphism c) a = Object c a
  id = Isomorphism id id
  Isomorphism e p . Isomorphism f q = Isomorphism (e.f) (q.p)

instance (Cartesian c) => Cartesian (Isomorphism c) where
  type UnitObject (Isomorphism c) = UnitObject c
  type PairObjects (Isomorphism c) a b = PairObjects c a b
  swap = Isomorphism swap swap
  attachUnit = Isomorphism attachUnit detachUnit
  detachUnit = Isomorphism detachUnit attachUnit
  regroup = Isomorphism regroup regroup'
  regroup' = Isomorphism regroup' regroup

instance (CoCartesian c) => CoCartesian (Isomorphism c) where
  type ZeroObject (Isomorphism c) = ZeroObject c
  type SumObjects (Isomorphism c) a b = SumObjects c a b
  coSwap = Isomorphism coSwap coSwap
  attachZero = Isomorphism attachZero detachZero
  detachZero = Isomorphism detachZero attachZero
  coRegroup = Isomorphism coRegroup coRegroup'
  coRegroup' = Isomorphism coRegroup' coRegroup
  maybeAsSum = Isomorphism maybeAsSum maybeFromSum
  maybeFromSum = Isomorphism maybeFromSum maybeAsSum
  boolAsSum = Isomorphism boolAsSum boolFromSum
  boolFromSum = Isomorphism boolFromSum boolAsSum

instance (Morphism c) => Morphism (Isomorphism c) where
  Isomorphism e p *** Isomorphism f q = Isomorphism (e***f) (p***q)
  
instance (MorphChoice c) => MorphChoice (Isomorphism c) where
  Isomorphism e p +++ Isomorphism f q = Isomorphism (e+++f) (p+++q)

instance (Category c) => EnhancedCat c (Isomorphism c) where 
  arr = forwardIso

instance (Category c) => EnhancedCat (Embedding c) (Isomorphism c) where 
  arr (Isomorphism f b) = Embedding f b


    
-- | A pair of matching functions. The projection must be a left (but not necessarily right)
--   inverse of the embedding,
--   i.e. the cardinality of @a@ will have to be less or equal than the cardinality
--   of @b@.
data Embedding c a b = Embedding { embedding :: c a b
                                 , projection :: c b a
                                 }

fromEmbedProject :: c a b -- ^ Injective embedding
                 -> c b a -- ^ Surjective projection. Must be left inverse of embedding.
                 -> Embedding c a b
fromEmbedProject = Embedding


infixr 0 $->, >-$
($->) :: (Function c, Object c a, Object c b) => Embedding c a b -> a -> b
Embedding f _ $-> x = f $ x

(>-$) :: (Function c, Object c b, Object c a) => Embedding c a b -> b -> a
Embedding _ p >-$ y = p $ y


instance (Category c) => Category (Embedding c) where
  type Object (Embedding c) a = Object c a
  id = Embedding id id
  Embedding e p . Embedding f q = Embedding (e.f) (q.p)

instance (Cartesian c) => Cartesian (Embedding c) where
  type UnitObject (Embedding c) = UnitObject c
  type PairObjects (Embedding c) a b = PairObjects c a b
  swap = Embedding swap swap
  attachUnit = Embedding attachUnit detachUnit
  detachUnit = Embedding detachUnit attachUnit
  regroup = Embedding regroup regroup'
  regroup' = Embedding regroup' regroup

instance (CoCartesian c) => CoCartesian (Embedding c) where
  type ZeroObject (Embedding c) = ZeroObject c
  type SumObjects (Embedding c) a b = SumObjects c a b
  coSwap = Embedding coSwap coSwap
  attachZero = Embedding attachZero detachZero
  detachZero = Embedding detachZero attachZero
  coRegroup = Embedding coRegroup coRegroup'
  coRegroup' = Embedding coRegroup' coRegroup
  maybeAsSum = Embedding maybeAsSum maybeFromSum
  maybeFromSum = Embedding maybeFromSum maybeAsSum
  boolAsSum = Embedding boolAsSum boolFromSum
  boolFromSum = Embedding boolFromSum boolAsSum

instance (Morphism c) => Morphism (Embedding c) where
  Embedding e p *** Embedding f q = Embedding (e***f) (p***q)
  
instance (MorphChoice c) => MorphChoice (Embedding c) where
  Embedding e p +++ Embedding f q = Embedding (e+++f) (p+++q)

instance (Category c) => EnhancedCat c (Embedding c) where 
  arr = embedding


        




