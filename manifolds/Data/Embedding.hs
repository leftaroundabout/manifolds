-- |
-- Module      : Data.Embedding
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

module Data.Embedding where

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
import Control.Arrow.Constrained


import qualified Data.Vector as Arr
import qualified Numeric.LinearAlgebra.HMatrix as HMat


    
infixr 0 $->, >-$

-- | A pair of matching functions. The projection must be a left (but not necessarily right)
--   inverse of the embedding
--   i.e. the cardinality of @a@ will have to be less or equal than the cardinality
--   of @b@.
data Embedding c a b = Embedding { ($->) :: c a b -- ^ Embedding into the containing space
                                 , (>-$) :: c b a -- ^ Projection into the embedded space
                                 }


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

instance (Morphism c) => Morphism (Embedding c) where
  Embedding e p *** Embedding f q = Embedding (e***f) (p***q)
  


