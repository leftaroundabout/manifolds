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

instance (MetricScalar s) => Morphism (Affine s) where
  Affine cof aof slf *** Affine cog aog slg
      = Affine (cof,cog) (aof,aog) (linear $ lapply slf *** lapply slg)

instance (MetricScalar s) => PreArrow (Affine s) where
  terminal = linearAffine $ const Origin
  fst = linearAffine fst
  snd = linearAffine snd
  Affine cof aof slf &&& Affine cog aog slg
      = Affine zeroV (aof.-^lapply slf cof, aog.-^lapply slg cog)
                 (linear $ lapply slf &&& lapply slg)

instance (MetricScalar s) => WellPointed (Affine s) where
  unit = Tagged Origin
  globalElement x = Affine zeroV x zeroV
  const x = Affine zeroV x zeroV



type AffinFuncValue s = GenericAgent (Affine s)

instance (MetricScalar s) => HasAgent (Affine s) where
  alg = genericAlg
  ($~) = genericAgentMap
instance (MetricScalar s) => CartesianAgent (Affine s) where
  alg1to2 = genericAlg1to2
  alg2to1 = genericAlg2to1
  alg2to2 = genericAlg2to2
instance (MetricScalar s)
      => PointAgent (AffinFuncValue s) (Affine s) a x where
  point = genericPoint



instance (WithField s LinearManifold v, WithField s LinearManifold a)
    => AdditiveGroup (AffinFuncValue s a v) where
  zeroV = GenericAgent $ Affine zeroV zeroV zeroV
  GenericAgent (Affine cof aof slf) ^+^ GenericAgent (Affine cog aog slg)
       = GenericAgent $ Affine (cof^+^cog) (aof^+^aog) (slf^+^slg)
  negateV (GenericAgent (Affine co ao sl))
      = GenericAgent $ Affine (negateV co) (negateV ao) (negateV sl)



