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
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE UnicodeSyntax            #-}
{-# LANGUAGE MultiWayIf               #-}
{-# LANGUAGE ScopedTypeVariables      #-}
{-# LANGUAGE RecordWildCards          #-}
{-# LANGUAGE CPP                      #-}


module Data.Function.Affine (
              Affine(..)
            ) where
    


import Data.List
import Data.Maybe
import Data.Semigroup

import Data.VectorSpace
import Data.LinearMap
import Data.LinearMap.HerMetric
import Data.MemoTrie (HasTrie(..))
import Data.AffineSpace
import Data.Basis
import Data.Void
import Data.Tagged
import Data.Manifold.Types.Primitive
import Data.Manifold.PseudoAffine

import Data.CoNat
import Data.VectorSpace.FiniteDimensional

import qualified Prelude
import qualified Control.Applicative as Hask

import Control.Category.Constrained.Prelude hiding ((^))
import Control.Arrow.Constrained
import Control.Monad.Constrained
import Data.Foldable.Constrained




data Affine s d c
   = Affine { affineCoOffset :: d
            , affineOffset :: c
            , affineSlope :: Needle d :-* Needle c
            }

instance (RealDimension s) => EnhancedCat (->) (Affine s) where
  arr (Affine co ao sl) x = ao .+~^ lapply sl (x.-.co)


instance (MetricScalar s) => Category (Affine s) where
  type Object (Affine s) o = WithField s LinearManifold o
  id = Affine zeroV zeroV idL
  Affine cof aof slf . Affine cog aog slg
      = Affine cog (aof .+~^ lapply slf (aog.-.cof)) (slf*.*slg)

linearAffine :: ( AdditiveGroup d, AdditiveGroup c
                , HasBasis (Needle d), HasTrie (Basis (Needle d)) )
       => (Needle d -> Needle c) -> Affine s d c
linearAffine = Affine zeroV zeroV . linear

instance (MetricScalar s) => Cartesian (Affine s) where
  type UnitObject (Affine s) = ZeroDim s
  swap = linearAffine swap
  attachUnit = linearAffine (, Origin)
  detachUnit = linearAffine fst
  regroup = linearAffine regroup
  regroup' = linearAffine regroup'

{-


instance (MetricScalar s) => Morphism (Differentiable s) where
  Differentiable f *** Differentiable g = Differentiable h
   where h (x,y) = ((fx, gy), lPar, devfg)
          where (fx, f', devf) = f x
                (gy, g', devg) = g y
                devfg δs = transformMetric lfst δx 
                           ^+^ transformMetric lsnd δy
                  where δx = devf $ transformMetric lcofst δs
                        δy = devg $ transformMetric lcosnd δs
                lPar = linear $ lapply f'***lapply g'
         lfst = linear fst; lsnd = linear snd
         lcofst = linear (,zeroV); lcosnd = linear (zeroV,)


instance (MetricScalar s) => PreArrow (Differentiable s) where
  terminal = Differentiable $ \_ -> (Origin, zeroV, const zeroV)
  fst = Differentiable $ \(x,_) -> (x, lfst, const zeroV)
   where lfst = linear fst
  snd = Differentiable $ \(_,y) -> (y, lsnd, const zeroV)
   where lsnd = linear snd
  Differentiable f &&& Differentiable g = Differentiable h
   where h x = ((fx, gx), lFanout, devfg)
          where (fx, f', devf) = f x
                (gx, g', devg) = g x
                devfg δs = (devf $ transformMetric lcofst δs)
                           ^+^ (devg $ transformMetric lcosnd δs)
                lFanout = linear $ lapply f'&&&lapply g'
         lcofst = linear (,zeroV); lcosnd = linear (zeroV,)


instance (MetricScalar s) => WellPointed (Differentiable s) where
  unit = Tagged Origin
  globalElement x = Differentiable $ \Origin -> (x, zeroV, const zeroV)
  const x = Differentiable $ \_ -> (x, zeroV, const zeroV)



type DfblFuncValue s = GenericAgent (Differentiable s)

instance (MetricScalar s) => HasAgent (Differentiable s) where
  alg = genericAlg
  ($~) = genericAgentMap
instance (MetricScalar s) => CartesianAgent (Differentiable s) where
  alg1to2 = genericAlg1to2
  alg2to1 = genericAlg2to1
  alg2to2 = genericAlg2to2
instance (MetricScalar s)
      => PointAgent (DfblFuncValue s) (Differentiable s) a x where
  point = genericPoint
-}





