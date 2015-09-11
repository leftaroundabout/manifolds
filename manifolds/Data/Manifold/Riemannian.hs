-- |
-- Module      : Data.Manifold.Riemannian
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
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE ParallelListComp           #-}
{-# LANGUAGE UnicodeSyntax              #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE PatternGuards              #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE LiberalTypeSynonyms        #-}
{-# LANGUAGE CPP                        #-}
{-# LANGUAGE DataKinds                  #-}


module Data.Manifold.Riemannian  where


import Data.List hiding (filter, all, elem, sum)
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Vector as Arr
import Data.List.NonEmpty (NonEmpty(..))
import Data.List.FastNub
import qualified Data.List.NonEmpty as NE
import Data.Semigroup
import Data.Ord (comparing)
import Control.DeepSeq

import Data.VectorSpace
import Data.LinearMap
import Data.LinearMap.HerMetric
import Data.LinearMap.Category
import Data.AffineSpace
import Data.Basis
import Data.Complex hiding (magnitude)
import Data.Void
import Data.Tagged
import Data.Proxy

import Data.Manifold.Types
import Data.Manifold.Types.Primitive ((^))
import Data.Manifold.PseudoAffine
    
import Data.Embedding
import Data.CoNat

import qualified Prelude as Hask hiding(foldl, sum, sequence)
import qualified Control.Applicative as Hask
import qualified Control.Monad       as Hask hiding(forM_, sequence)
import Data.Functor.Identity
import Control.Monad.Trans.State
import Control.Monad.Trans.Writer
import Control.Monad.Trans.Class
import qualified Data.Foldable       as Hask
import Data.Foldable (all, elem, toList, sum)
import qualified Data.Traversable as Hask
import Data.Traversable (forM)

import qualified Numeric.LinearAlgebra.HMatrix as HMat

import Control.Category.Constrained.Prelude hiding
     ((^), all, elem, sum, forM, Foldable(..), Traversable)
import Control.Arrow.Constrained
import Control.Monad.Constrained hiding (forM)
import Data.Foldable.Constrained

import GHC.Generics (Generic)


class PseudoAffine x => Geodesic x where
  geodesicBetween :: s ~ Scalar (Needle x)
      => x -> x -> Option (Differentiable s s x)

#define deriveAffineGD(x)                 \
instance Geodesic x where {              \
  geodesicBetween a b = return $          \
      alg (\t -> point a ^+^ t * point s)    \
   where s = b - a;                         \
 }

deriveAffineGD(ℝ)
