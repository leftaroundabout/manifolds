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

import Data.Constraint.Trivial
import Control.Category.Constrained.Prelude hiding ((^))
import Control.Category.Constrained.Reified
import Control.Arrow.Constrained
import Control.Monad.Constrained
import Data.Foldable.Constrained




data Affine s d c where
   SubtractFrom :: α -> Affine s α (Needle α)
   AddTo :: α -> Affine s (Needle α) α
   ScaleWith :: (LinearManifold α, LinearManifold β) => (α:-*β) -> Affine s α β
   ReAffine :: ReWellPointed (Affine s) α β -> Affine s α β

toOffset'Slope :: (LinearManifold d, AffineManifold c)
                      => Affine s d c -> (c, d:-*Needle c)
toOffset'Slope (SubtractFrom c) = (negateV c, idL)
toOffset'Slope (AddTo c) = (c, idL)
toOffset'Slope (ScaleWith q) = (zeroV, q)

instance (RealDimension s) => EnhancedCat (->) (Affine s) where
--  arr (Affine co ao sl) x = ao .+~^ lapply sl (x.-.co)

instance (RealDimension s, AffineManifold d, AffineManifold c)
                  => AffineSpace (Affine s d c) where
  type Diff (Affine s d c) = Affine s d (Diff c)
--   Affine cof aof slf .-. Affine cog aog slg = Affine cog ((aof.-.aog)^+^aoΔ) (slf^-^slg)
--    where aoΔ = lapply slf (cof.-.cog)
--   Affine cof aof slf .+^ Affine coΔ aoΔ slΔ = Affine cof (aof.+^aoΔ') (slf^+^slΔ)
--    where aoΔ' = aoΔ ^-^ lapply slΔ (coΔ.-.cof)

instance (RealDimension s, AffineManifold d, LinearManifold c)
                  => AdditiveGroup (Affine s d c) where
--   zeroV = const zeroV
--   Affine cof aof slf ^+^ Affine cog aog slg = Affine (cof^+^cog) (aof^+^aog) (slf^+^slg)

instance (MetricScalar s) => Category (Affine s) where
  type Object (Affine s) o = WithField s AffineManifold o
  
--   id = ReAffine id
--   
--   Affine cof aof slf . Affine cog aog slg
--       = Affine cog (aof .+~^ lapply slf (aog.-.cof)) (slf*.*slg)
--   ReAffine f . ReAffine g = ReAffine $ f . g
--   fa@(Affine cof aof slf) . ReAffine fwp = case fwp of
--      Const k -> const $ aof .+^ lapply slf (k.-.cof)
--      ReWellPointed ga -> fa . ga
--      ReWellPointedArr' fpa -> case fpa of
--         Terminal -> fa . const Origin
--         g :&&& h ->
--             let g' = ReAffine $ ReWellPointedArr' g
--                 h' = ReAffine $ ReWellPointedArr' h
--             in case ( Affine (fst cof) aof (linear $ \a -> lapply slf (a,zeroV)) . g'
--                     , Affine (snd cof) aof (linear $ \a -> lapply slf (zeroV,a)) . h' ) of
--                  _ -> undefined
        

-- linearAffine :: ( AdditiveGroup d, AdditiveGroup c
--                 , HasBasis (Needle d), HasTrie (Basis (Needle d)) )
--        => (Needle d -> Needle c) -> Affine s d c
-- linearAffine = Affine zeroV zeroV . linear

instance (MetricScalar s) => Cartesian (Affine s) where
  type UnitObject (Affine s) = ZeroDim s
--   swap = ReAffine swap
--   attachUnit = ReAffine attachUnit
--   detachUnit = ReAffine detachUnit
--   regroup = ReAffine regroup
--   regroup' = ReAffine regroup'

instance (MetricScalar s) => Morphism (Affine s) where
--   Affine cof aof slf *** Affine cog aog slg
--       = Affine (cof,cog) (aof,aog) (linear $ lapply slf *** lapply slg)

instance (MetricScalar s) => PreArrow (Affine s) where
--   terminal = ReAffine terminal
--   fst = ReAffine fst
--   snd = ReAffine snd
--   Affine cof aof slf &&& Affine cog aog slg
--       = Affine coh (aof.-^lapply slf rco, aog.+^lapply slg rco)
--                  (linear $ lapply slf &&& lapply slg)
--    where rco = (cog.-.cof)^/2
--          coh = cof .+^ rco

instance (MetricScalar s) => WellPointed (Affine s) where
--   unit = Tagged Origin
--   globalElement x = Affine zeroV x zeroV
--   const = ReAffine . const



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
--   point = genericPoint



instance (WithField s LinearManifold v, WithField s LinearManifold a)
    => AdditiveGroup (AffinFuncValue s a v) where
--   zeroV = GenericAgent $ Affine zeroV zeroV zeroV
--   GenericAgent (Affine cof aof slf) ^+^ GenericAgent (Affine cog aog slg)
--        = GenericAgent $ Affine (cof^+^cog) (aof^+^aog) (slf^+^slg)
--   negateV (GenericAgent (Affine co ao sl))
--       = GenericAgent $ Affine (negateV co) (negateV ao) (negateV sl)



