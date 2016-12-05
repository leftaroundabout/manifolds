-- |
-- Module      : Data.Function.Affine
-- Copyright   : (c) Justus Sagemüller 2015
-- License     : GPL v3
-- 
-- Maintainer  : (@) sagemueller $ geo.uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 

{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE UndecidableInstances     #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE FunctionalDependencies   #-}
{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE LiberalTypeSynonyms      #-}
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE RankNTypes               #-}
{-# LANGUAGE TupleSections            #-}
{-# LANGUAGE ConstraintKinds          #-}
{-# LANGUAGE PatternGuards            #-}
{-# LANGUAGE PatternSynonyms          #-}
{-# LANGUAGE ViewPatterns             #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE UnicodeSyntax            #-}
{-# LANGUAGE MultiWayIf               #-}
{-# LANGUAGE ScopedTypeVariables      #-}
{-# LANGUAGE RecordWildCards          #-}
{-# LANGUAGE CPP                      #-}


module Data.Function.Affine (
              Affine
            , linearAffine
            , toOffsetSlope, toOffset'Slope 
            ) where
    


import Data.Semigroup

import Data.MemoTrie
import Data.VectorSpace
import Data.AffineSpace
import Data.Tagged
import Data.Manifold.Types.Primitive
import Data.Manifold.PseudoAffine
import Data.Manifold.Atlas

import qualified Prelude
import qualified Control.Applicative as Hask

import Control.Category.Constrained.Prelude hiding ((^))
import Control.Category.Constrained.Reified
import Control.Arrow.Constrained
import Control.Monad.Constrained
import Data.Foldable.Constrained

import Math.LinearMap.Category



data Affine s d c where
    Affine :: (ChartIndex d :->: (c, LinearMap s (Needle d) (Needle c)))
               -> Affine s d c

instance Category (Affine s) where
  type Object (Affine s) x = ( Atlas x, LinearSpace (Needle x)
                             , Scalar (Needle x) ~ s, HasTrie (ChartIndex x) )
  id = Affine . trie $ chartReferencePoint >>> id &&& const id
  Affine f . Affine g = Affine . trie
      $ \ixa -> case untrie g ixa of
           (b, ða'b) -> case untrie f $ lookupAtlas b of
            (c, ðb'c) -> (c, ðb'c . ða'b)

instance ∀ s . Num' s => Cartesian (Affine s) where
  type UnitObject (Affine s) = ZeroDim s
  swap = Affine . trie $ chartReferencePoint >>> swap &&& const swap
  attachUnit = Affine . trie $ chartReferencePoint >>> \a -> ((a,Origin), attachUnit)
  detachUnit = Affine . trie $ chartReferencePoint
                 >>> \(a,Origin::ZeroDim s) -> (a, detachUnit)
  regroup = Affine . trie $ chartReferencePoint >>> regroup &&& const regroup
  regroup' = Affine . trie $ chartReferencePoint >>> regroup' &&& const regroup'

instance EnhancedCat (->) (Affine s) where
  arr (Affine f) x = fx₀ .+~^ (ðx'f $ v)
   where chIx = lookupAtlas x
         Option (Just v) = x .-~. chartReferencePoint chIx
         (fx₀, ðx'f) = untrie f $ x
  
  
linearAffine :: {- (MetricScalar s, WithField s LinearManifold α, WithField s LinearManifold β)
             => -} (α+>β) -> Affine s α β
linearAffine = undefined

toOffsetSlope :: WithField s LinearManifold d
                      => Affine s d c -> (c, Needle d +> Needle c)
toOffsetSlope f = toOffset'Slope f zeroV

toOffset'Slope :: {- ( MetricScalar s, WithField s AffineManifold d
                                   , WithField s AffineManifold c )
                      => -} Affine s d c -> d -> (c, Needle d +> Needle c)
toOffset'Slope = undefined

