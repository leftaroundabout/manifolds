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
   Subtract :: AffineManifold α => Affine s (α,α) (Needle α)
   AddTo :: Affine s (α, Needle α) α
   ScaleWith :: (LinearManifold α, LinearManifold β) => (α:-*β) -> Affine s α β
   ReAffine :: ReWellPointed (Affine s) α β -> Affine s α β

reAffine :: ReWellPointed (Affine s) α β -> Affine s α β
reAffine (ReWellPointed f) = f
reAffine f = ReAffine f

pattern Specific f = ReWellPointed f
pattern Id = ReAffine WellPointedId
infixr 1 :>>>, :<<<
pattern f :>>> g <- ReAffine (WellPointedCompo (reAffine -> f) (reAffine -> g))
pattern g :<<< f <- ReAffine (WellPointedCompo (reAffine -> f) (reAffine -> g))
pattern Swap = ReAffine WellPointedSwap
pattern AttachUnit = ReAffine WellPointedAttachUnit
pattern DetachUnit = ReAffine WellPointedDetachUnit
pattern Regroup = ReAffine WellPointedRegroup
pattern Regroup' = ReAffine WellPointedRegroup_
pattern Terminal = ReAffine WellPointedTerminal
pattern Fst = ReAffine WellPointedFst
pattern Snd = ReAffine WellPointedSnd
infixr 3 :***, :&&&
pattern f :*** g <- ReAffine (WellPointedPar (reAffine -> f) (reAffine -> g))
pattern f :&&& g <- ReAffine (WellPointedFanout (reAffine -> f) (reAffine -> g))
pattern Const c = ReAffine (WellPointedConst c)


toOffsetSlope :: (MetricScalar s, WithField s LinearManifold d
                                 , WithField s AffineManifold c )
                      => Affine s d c -> (c, Needle d :-* Needle c)
toOffsetSlope f = toOffset'Slope f zeroV

-- | Basically evaluates an affine function as a generic differentiable one,
--   yielding at a given reference point the result and Jacobian. Unlike with
--   'Data.Function.Differentiable.Differentiable', the induced 1st-order Taylor
--   series is equal to the function!
toOffset'Slope :: ( MetricScalar s, WithField s AffineManifold d
                                   , WithField s AffineManifold c )
                      => Affine s d c -> d -> (c, Needle d :-* Needle c)
toOffset'Slope Subtract (a,b) = (a.-.b, linear $ uncurry(^-^))
toOffset'Slope AddTo (p,v) = (p.+^v, linear $ uncurry(^+^))
toOffset'Slope (ScaleWith q) ref = (lapply q ref, q)
toOffset'Slope Id ref = (ref, linear id)
toOffset'Slope (f :>>> g) ref = case toOffset'Slope f ref of
                  (cf,sf) -> case toOffset'Slope g cf of
                     (cg,sg)     -> (cg, sg*.*sf)
toOffset'Slope Swap ref = (swap ref, linear swap)
toOffset'Slope AttachUnit ref = ((ref,Origin), linear (,Origin))
toOffset'Slope DetachUnit ref = (fst ref, linear fst)
toOffset'Slope Regroup ref = (regroup ref, linear regroup)
toOffset'Slope Regroup' ref = (regroup' ref, linear regroup')
toOffset'Slope (f:***g) ref = case ( toOffset'Slope f (fst ref)
                                 , toOffset'Slope g (snd ref) ) of
                  ((cf, sf), (cg, sg)) -> ((cf,cg), linear $ lapply sf *** lapply sg)
toOffset'Slope Terminal ref = (Origin, zeroV)
toOffset'Slope Fst ref = (fst ref, linear fst)
toOffset'Slope Snd ref = (snd ref, linear snd)
toOffset'Slope (f:&&&g) ref = case ( toOffset'Slope (arr f) ref
                                  , toOffset'Slope (arr g) ref ) of
                  ((cf, sf), (cg, sg)) -> ((cf,cg), linear $ lapply sf &&& lapply sg)
toOffset'Slope (Const c) ref = (c, zeroV)
            
coOffsetForm :: ( MetricScalar s, WithField s AffineManifold d
                                , WithField s AffineManifold c )
                      => Affine s d c -> Affine s d c
coOffsetForm (ScaleWith q) = id&&&const zeroV >>> Subtract >>> ScaleWith q
coOffsetForm ((coOffsetForm -> Id:&&&Const cof :>>> Subtract :>>> f) :>>> g)
                    = id&&&const cof >>> Subtract >>> (f >>> g)
coOffsetForm ( (coOffsetForm -> Id:&&&Const cof :>>> Subtract :>>> f)
          :*** (coOffsetForm -> Id:&&&Const cog :>>> Subtract :>>> g) )
     = id&&&const(cof,cog) >>> Subtract >>> (f***g)
coOffsetForm (Id:&&&Const cof :>>> Subtract)
           = (Id&&&Const cof >>> ReAffine (ReWellPointed Subtract`WellPointedCompo`WellPointedId))
coOffsetForm f = f

pattern PreSubtract c f <- (coOffsetForm -> Id:&&&Const c :>>> Subtract :>>> f)

preSubtract :: ( MetricScalar s, WithField s AffineManifold d
                               , WithField s AffineManifold c )
               => c -> Affine s (Diff c) d -> Affine s c d
-- The specialised clauses may not actually be useful here.
preSubtract _ (Const d) = const d
preSubtract _ Terminal = Terminal
preSubtract c (f:>>>g) = preSubtract c f >>> g
-- preSubtract (c,d) (f:***g) = preSubtract c f *** preSubtract d g
preSubtract c (f:&&&g) = preSubtract c f &&& preSubtract c g
preSubtract c f = id&&&const c >>> Subtract >>> f
   
pattern PostAdd c f <- f:&&&Const c :>>> AddTo

instance (MetricScalar s) => EnhancedCat (->) (Affine s) where
  arr f = fst . toOffset'Slope f

instance (MetricScalar s) => EnhancedCat (Affine s) (ReWellPointed (Affine s)) where
  arr (Specific c) = c
  arr c = ReAffine c

instance (MetricScalar s, WithField s AffineManifold d, WithField s AffineManifold c)
                  => AffineSpace (Affine s d c) where
  type Diff (Affine s d c) = Affine s d (Diff c)
  
  ScaleWith q .-. ScaleWith r = ScaleWith $ q^-^r
  (PostAdd c (ScaleWith q)) .-. g = let (d, r) = toOffsetSlope g
                                    in ScaleWith (q^-^r) &&& const (c.-.d) >>> AddTo
  f .-. (PostAdd d (ScaleWith r)) = let (c, q) = toOffsetSlope f
                                    in ScaleWith (q^-^r) &&& const (c.-.d) >>> AddTo
  
  Id .-. Id = const zeroV
  Fst .-. Fst = const zeroV
  Snd .-. Snd = const zeroV
  Swap .-. Swap = const zeroV
  AttachUnit .-. AttachUnit = const zeroV
  DetachUnit .-. DetachUnit = const zeroV
  Terminal .-. _ = Terminal
  _ .-. Terminal = Terminal
  Subtract .-. Subtract = const zeroV
  AddTo .-. AddTo = const zeroV
  
  Const c .-. Const d = Const $ c.-.d
  
  (f:***g) .-. (h:***i) = f.-.h *** g.-.i
  (f:***g) .-. Const (c,d) = f.-.const c *** g.-.const d
  -- Const (c,d) .-. (f:***g) = const c.-.f *** const d.-.g
  (f:&&&g) .-. (h:&&&i) = f.-.h &&& g.-.i
  (f:&&&_) .-. AttachUnit = f.-.id >>> AttachUnit
  (f:&&&g) .-. Const (c,d) = f.-.const c &&& g.-.const d
  -- Const (c,d) .-. (f:&&&g) = const c.-.f &&& const d.-.g

  ScaleWith q .-. f = let (c, r) = toOffset'Slope f zeroV
                      in ScaleWith (q^-^r)&&&const(negateV c) >>> AddTo
  f .-. ScaleWith q = let (c, r) = toOffset'Slope f zeroV
                      in ScaleWith (r^-^q)&&&const c >>> AddTo
  
  PreSubtract b f .-. g = let (c, q) = toOffsetSlope f
                              (d, r) = toOffset'Slope g b
                          in preSubtract b $ ScaleWith (q^-^r)
      {- f x = q·x + c    -}                 &&& const (c.-.d) >>> AddTo
      -- g x = r·x + w
      -- d = r·b + w
      -- (q−r)·(x−b) = q·x − q⋅b − r⋅x + r⋅b
      -- s x = f (x−b) − g x
      --     = q⋅(x−b) + c − r⋅x − w
      --     = q⋅x − q⋅b + c − r⋅x − w
      --     = (q−r)·(x−b) + c − r⋅b − w
      --     = (q−r)·(x−b) + c − d
  
  -- According to GHC, this clause overlaps with the above. Hm...
  f .-. PreSubtract b g = let (c, q) = toOffset'Slope f b
                              (d, r) = toOffsetSlope g
                          in preSubtract b $ ScaleWith (q^-^r)
      {- f x = q·x + v    -}                 &&& const (c.-.d) >>> AddTo
      -- g x = r·x + d
      -- c = q·b + v
      -- (q−r)·(x−b) = q·x − q⋅b − r⋅x + r⋅b
      -- s x = f x − g (x−b)
      --     = q⋅x + v − r⋅(x−b) − d
      --     = q⋅x + v − r⋅x + r⋅b − d
      --     = (q−r)·(x−b) + q⋅b + v − d
      --     = (q−r)·(x−b) + c − d
  
  
  ScaleWith q .+^ ScaleWith r = ScaleWith $ q^+^r
  (PostAdd c (ScaleWith q)) .+^ g = let (d, r) = toOffsetSlope g
                                    in ScaleWith (q^+^r) &&& const (c.+^d) >>> AddTo
  f .+^ (PostAdd d (ScaleWith r)) = let (c, q) = toOffsetSlope f
                                    in const (c.+^d)&&&ScaleWith (q^+^r) >>> AddTo
  (f:***g) .+^ (h:***i) = f.+^h *** g.+^i
  (f:&&&g) .+^ (h:&&&i) = f.+^h &&& g.+^i
  
  Const c .+^ Const c' = const (c.+^c')

  Terminal .+^ _ = Terminal
  Const c .+^ Terminal = Const c
  Const c .+^ f = const c&&&f >>> AddTo
  
  Fst .+^ Fst = Fst >>> ScaleWith (linear (^*2))
  Snd .+^ Snd = Snd >>> ScaleWith (linear (^*2))
  
  f .+^ Id = let (c,q) = toOffset'Slope f zeroV
             in const c&&&ScaleWith (q^+^idL) >>> AddTo
  f .+^ AttachUnit = let (c,q) = toOffset'Slope f zeroV
                     in const c&&&ScaleWith (q^+^linear(,Origin)) >>> AddTo
  f .+^ DetachUnit = let (c,q) = toOffset'Slope f zeroV
                     in const c&&&ScaleWith (q^+^linear fst) >>> AddTo
  f .+^ Swap = let (c,q) = toOffset'Slope f zeroV
               in const c&&&ScaleWith (q^+^linear swap) >>> AddTo



instance (MetricScalar s, WithField s AffineManifold d, WithField s LinearManifold c)
                  => AdditiveGroup (Affine s d c) where
  zeroV = const zeroV
  negateV (Const c) = const $ negateV c
  (^+^) = (.+^)
  (^-^) = (.-.)
  

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
  Const c *** Const c' = const (c,c')
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



