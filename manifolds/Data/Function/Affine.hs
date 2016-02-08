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
   Subtract :: α -> Affine s α (Needle α)
   AddTo :: α -> Affine s (Needle α) α
   ScaleWith :: (LinearManifold α, LinearManifold β) => (α:-*β) -> Affine s α β
   ReAffine :: ReWellPointed (Affine s) α β -> Affine s α β


-- | Basically evaluates an affine function as a generic differentiable one,
--   yielding at a given reference point the result and Jacobian. Unlike with
--   'Data.Function.Differentiable.Differentiable', the induced 1st-order Taylor
--   series is equal to the function!
toOffset'Slope :: ( MetricScalar s, WithField s AffineManifold d
                                   , WithField s AffineManifold c )
                      => Affine s d c -> d -> (c, Needle d :-* Needle c)
toOffset'Slope (Subtract c) ref = (ref.-.c, idL)
toOffset'Slope (AddTo c) ref = (c.+^ref, idL)
toOffset'Slope (ScaleWith q) ref = (lapply q ref, q)
toOffset'Slope (ReAffine r) ref = case r of
   ReWellPointed f               -> toOffset'Slope f ref
   ReWellPointedArr' a -> case a of
      RePreArrow f               -> toOffset'Slope (arr f) ref
      RePreArrowMorph m -> case m of
         ReMorphism f            -> toOffset'Slope (arr f) ref
         ReMorphismCart c -> case c of
            ReCartesian f        -> toOffset'Slope (arr f) ref
            ReCartesianCat k -> case k of
               Id                -> (ref, linear id)
               f :>>> g -> case toOffset'Slope (arr f) ref of
                  (cf,sf) -> case toOffset'Slope (arr g) cf of
                     (cg,sg)     -> (cg, sg*.*sf)
            Swap                 -> (swap ref, linear swap)
            AttachUnit           -> ((ref,Origin), linear (,Origin))
            DetachUnit           -> (fst ref, linear fst)
            Regroup              -> (regroup ref, linear regroup)
            Regroup'             -> (regroup' ref, linear regroup')
         f :*** g     -> case ( toOffset'Slope (arr f) (fst ref)
                              , toOffset'Slope (arr g) (snd ref) ) of
            ((cf, sf), (cg, sg)) -> ((cf,cg), linear $ lapply sf *** lapply sg)
      Terminal                   -> (Origin, zeroV)
      Fst                        -> (fst ref, linear fst)
      Snd                        -> (snd ref, linear snd)
      f :&&& g     -> case ( toOffset'Slope (arr f) ref
                           , toOffset'Slope (arr g) ref ) of
            ((cf, sf), (cg, sg)) -> ((cf,cg), linear $ lapply sf &&& lapply sg)
   Const c                       -> (c, zeroV)
            
   

instance (MetricScalar s) => EnhancedCat (->) (Affine s) where
  arr f = fst . toOffset'Slope f

instance (MetricScalar s) => EnhancedCat (Affine s) (ReCategory (ReCartesian (ReMorphism (RePreArrow (ReWellPointed (Affine s)))))) where
  arr = arr . ReCartesianCat
instance (MetricScalar s) => EnhancedCat (Affine s) (ReCartesian (ReMorphism (RePreArrow (ReWellPointed (Affine s))))) where
  arr = arr . ReMorphismCart
instance (MetricScalar s) => EnhancedCat (Affine s) (ReMorphism (RePreArrow (ReWellPointed (Affine s)))) where
  arr = arr . RePreArrowMorph
instance (MetricScalar s) => EnhancedCat (Affine s) (RePreArrow (ReWellPointed (Affine s))) where
  arr = arr . ReWellPointedArr'
instance (MetricScalar s) => EnhancedCat (Affine s) (ReWellPointed (Affine s)) where
  arr = ReAffine

instance (MetricScalar s, WithField s AffineManifold d, WithField s AffineManifold c)
                  => AffineSpace (Affine s d c) where
  type Diff (Affine s d c) = Affine s d (Diff c)
  
  AddTo c .-. ReAffine Id' = const c
  AddTo c .-. AddTo c' = const $ c.-.c'
  AddTo c .-. Subtract c' = const $ c^+^c'
  Subtract c .-. AddTo c' = const . negateV $ c'^+^c
  Subtract c .-. Subtract c' = const $ c'.-.c
  AddTo c .-. ScaleWith q = AddTo c . ScaleWith (idL^-^q)
  Subtract c .-. ScaleWith q = ScaleWith (idL^-^q) . Subtract c
  ScaleWith q .-. AddTo c = AddTo (negateV c) . ScaleWith (q^-^idL)
  ScaleWith q .-. Subtract c = AddTo c . ScaleWith (q^-^idL)
  ScaleWith q .-. ScaleWith r = ScaleWith $ q^-^r
  ScaleWith q .-. f = let (c, r) = toOffset'Slope f zeroV
                      in AddTo (negateV c) . ScaleWith (q^-^r)
  f .-. ScaleWith q = let (c, r) = toOffset'Slope f zeroV
                      in AddTo c . ScaleWith (r^-^q)
  AddTo c .-. ReAffine (Const c') = AddTo (c.-.c')
  Subtract c .-. ReAffine (Const c') = AddTo c' . Subtract c
  ReAffine (Const c) .-. ReAffine (Const c') = const (c.-.c')
  AddTo c .-. f = let (c', q) = toOffset'Slope f zeroV
                  in AddTo (c.-.c') . ScaleWith (idL.-.q)
  f .-. AddTo c = let (c', q) = toOffset'Slope f zeroV
                  in AddTo (c'.-.c) . ScaleWith (q.-.idL)
  Subtract c .-. f = let (d, q) = toOffset'Slope f c
                     in AddTo (negateV d) . ScaleWith (idL^-^q) . Subtract c
      -- f x = q·x + v
      -- s x = x − c − (q·x + v) = x − c − q·x − v
      -- d = q·c + v
      -- -d + (1−q)·(x−c) = − q·c − v + x − c − (q·x − q·c) 
      --                  = -q·x − v + x − c
  f .-. Subtract c = let (d, q) = toOffset'Slope f c
                     in AddTo d . ScaleWith (q^-^idL) . Subtract c
  
  AddTo c .+^ AddTo c' = AddTo (c.+^c') . ScaleWith (linear (^*2))

instance (MetricScalar s, WithField s AffineManifold d, WithField s LinearManifold c)
                  => AdditiveGroup (Affine s d c) where
  zeroV = const zeroV
  negateV (AddTo c) = AddTo $ negateV c
  AddTo c ^+^ AddTo c' = AddTo $ c^+^c'
  

instance (MetricScalar s) => Category (Affine s) where
  type Object (Affine s) o = WithField s AffineManifold o
  
  id = ReAffine id
  
  ReAffine f . ReAffine g = ReAffine $ f . g
--   Affine cof aof slf . Affine cog aog slg
--       = Affine cog (aof .+~^ lapply slf (aog.-.cof)) (slf*.*slg)
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
  swap = ReAffine swap
  attachUnit = ReAffine attachUnit
  detachUnit = ReAffine detachUnit
  regroup = ReAffine regroup
  regroup' = ReAffine regroup'

instance (MetricScalar s) => Morphism (Affine s) where
  AddTo c *** AddTo c' = AddTo (c,c')
--   Affine cof aof slf *** Affine cog aog slg
--       = Affine (cof,cog) (aof,aog) (linear $ lapply slf *** lapply slg)

instance (MetricScalar s) => PreArrow (Affine s) where
  terminal = ReAffine terminal
  fst = ReAffine fst
  snd = ReAffine snd
  ReAffine f &&& ReAffine g = ReAffine $ f &&& g
        
--   Affine cof aof slf &&& Affine cog aog slg
--       = Affine coh (aof.-^lapply slf rco, aog.+^lapply slg rco)
--                  (linear $ lapply slf &&& lapply slg)
--    where rco = (cog.-.cof)^/2
--          coh = cof .+^ rco

instance (MetricScalar s) => WellPointed (Affine s) where
  unit = Tagged Origin
  globalElement x = AddTo x . ScaleWith (linear undefined)
  const = ReAffine . const



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
  zeroV = GenericAgent zeroV
  GenericAgent f ^+^ GenericAgent g = GenericAgent $ f ^+^ g
  negateV (GenericAgent f) = GenericAgent $ negateV f



