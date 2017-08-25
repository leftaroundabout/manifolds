-- |
-- Module      : Data.Manifold.Types.Stiefel
-- Copyright   : (c) Justus Sagemüller 2015
-- License     : GPL v3
-- 
-- Maintainer  : (@) sagemueller $ geo.uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 
-- Stiefel manifolds are a generalisation of the concept of the 'UnitSphere'
-- in real vector spaces.
-- The /n/-th Stiefel manifold is the space of all possible configurations of
-- /n/ orthonormal vectors. In the case /n/ = 1, simply a single normalised vector,
-- i.e. a vector on the unit sphere.
-- 
-- Alternatively, the stiefel manifolds can be defined as quotient spaces under
-- scalings, and we prefer that definition since it doesn't require a notion of
-- unit length (which is only defined in inner-product spaces).

{-# LANGUAGE StandaloneDeriving, FlexibleContexts, UndecidableInstances #-}



module Data.Manifold.Types.Stiefel where


import Data.Maybe
import qualified Data.Vector as Arr

import Data.VectorSpace
import Data.AffineSpace
import Math.LinearMap.Category

import Data.Manifold.Types.Primitive ((^), empty, embed, coEmbed)
import Data.Manifold.PseudoAffine
    
import qualified Prelude as Hask hiding(foldl, sum, sequence)
import qualified Control.Applicative as Hask
import qualified Control.Monad       as Hask hiding(forM_, sequence)

import Control.Category.Constrained.Prelude hiding
     ((^), all, elem, sum, forM, Foldable(..), Traversable)
import Control.Arrow.Constrained
import Control.Monad.Constrained hiding (forM)
import Data.Foldable.Constrained


newtype Stiefel1 v = Stiefel1 { getStiefel1N :: DualVector v }
deriving instance (Show (DualVector v)) => Show (Stiefel1 v)
