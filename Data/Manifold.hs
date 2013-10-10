-- |
-- Module      : Data.Manifold
-- Copyright   : (c) Justus Sagemüller 2013
-- License     : GPL v3
-- 
-- Maintainer  : (@) sagemuej $ smail.uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 


{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE UndecidableInstances     #-}
-- {-# LANGUAGE OverlappingInstances     #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE RankNTypes               #-}
{-# LANGUAGE TupleSections            #-}
{-# LANGUAGE ConstraintKinds          #-}
{-# LANGUAGE PatternGuards            #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE ScopedTypeVariables      #-}


module Data.Manifold where

import Data.List
import qualified Data.Map as Map
import Data.Maybe
import Data.Function hiding ((.), id)

import qualified Data.Vector as V
import Data.Vector(fromList, toList, (!), singleton)
import qualified Data.Vector.Algorithms.Insertion as VAIns

import Data.VectorSpace
import Data.Basis

import Prelude hiding((.), id)

import Control.Category
import Control.Arrow
import Control.Monad
import Control.Monad.Trans.Maybe
import Control.Comonad

import Debug.Trace

import Util.LtdShow



-- | Continuous mapping.
data domain :--> codomain where
  Continuous_id :: x:-->x
  Continuous :: ( Manifold d, Manifold c
                , v ~ TangentSpace d, u ~ TangentSpace c
                , δ ~ Scalar v, ε ~ Scalar u, δ ~ ε) =>
        { runContinuous :: Chart d -> v -> (Chart c, u, ε->δ) }
           -> d :--> c
           
          

infixr 0 --$


-- | Function application, like '($)', but for continuous functions.
--   
--   From another point of view, this is one side of the forgetful functor from
--   the category of topological spaces to the category of sets.
(--$) :: (d:-->c) -> d -> c

Continuous_id --$ x = x
Continuous f --$ x = y
 where (tch, v, _) = f sch u
       tchIn = case tch of Chart tchIn _ _ -> tchIn
       schOut = case sch of Chart _ schOut _ -> schOut
       y = tchIn --$ v
       sch = head $ localAtlas x
       u = fromJust (schOut x) --$ x





instance Category (:-->) where

  id = Continuous_id
  
  Continuous_id . f = f
  f . Continuous_id = f
  Continuous f . Continuous g = Continuous h
   where h srcChart u = (tgtChart, w, q.p)
          where (interChart, v, p) = g srcChart u
                (tgtChart, w, q) = f interChart v
             
          


type EuclidSpace v = (HasBasis v, EqFloating(Scalar v), Eq v)
type EqFloating f = (Eq f, Ord f, Floating f)


-- | A chart is a homeomorphism from a connected, open subset /Q/ ⊂ /M/ of
-- an /n/-manifold /M/ to either the open unit disk /Dⁿ/ ⊂ /V/ ≃ ℝ/ⁿ/, or
-- the half-disk /Hⁿ/ = {/x/ ∊ /Dⁿ/: x₀≥0}. In e.g. the former case, 'chartInMap'
-- is thus defined ∀ /v/ ∊ /V/ : |/v/| < 1, while 'chartOutMap p' will yield @Just x@
-- with /x/ ∊ /Dⁿ/ provided /p/ is in /Q/, and @Nothing@ otherwise.
-- Obviously, @fromJust . 'chartOutMap' . 'chartInMap'@ should be equivalent to @id@
-- on /Dⁿ/, and @'chartInMap' . fromJust . 'chartOutMap'@ to @id@ on /Q/.
data Chart :: * -> * where
  Chart :: (Manifold m, v ~ TangentSpace m) =>
        { chartInMap :: v :--> m
        , chartOutMap :: m -> Maybe (m:-->v)
        , chartKind :: ChartKind      } -> Chart m
data ChartKind = LandlockedChart  -- ^ A /M/ ⇆ /Dⁿ/ chart, for ordinary manifolds
               | RimChart         -- ^ A /M/ ⇆ /Hⁿ/ chart, for manifolds with a rim

isInUpperHemi :: EuclidSpace v => v -> Bool
isInUpperHemi v = (snd . head) (decompose v) >= 0

rimGuard :: EuclidSpace v => ChartKind -> v -> Maybe v
rimGuard LandlockedChart v = Just v
rimGuard RimChart v
 | isInUpperHemi v = Just v
 | otherwise       = Nothing

chartEnv :: Manifold m => Chart m
               -> (TangentSpace m->TangentSpace m)
               -> m -> Maybe m
chartEnv (Chart inMap outMap chKind) f x = do
    vGet <- outMap x
    let v = vGet --$ x
    v' <- rimGuard chKind v
    return $ inMap --$ v'

  

 

type Atlas m = [Chart m]

class (EuclidSpace(TangentSpace m)) => Manifold m where
  type TangentSpace m :: *
  type TangentSpace m = m   -- For vector spaces.
  
  localAtlas :: m -> Atlas m


vectorSpaceAtlas :: (Manifold v, v ~ TangentSpace v) => v -> Atlas v
vectorSpaceAtlas v = [Chart { chartInMap  = id
                            , chartOutMap = const $ Just id
                            , chartKind   = LandlockedChart } ]


  
--   transferSimplex :: Chart m                  -> Chart m
--                   -> Simplex (TangentSpace m) -> Maybe(Simplex(TangentSpace m))
  
--   triangulation :: m -> Triangulation m
--   triangulation = autoTriangulation
  


-- | At the moment, complex etc. manifolds are not supported (because 'EuclidSpace' requires its scalar to be 'Ord' right now).
instance Manifold Float where
  localAtlas = vectorSpaceAtlas
instance Manifold Double where
  localAtlas = vectorSpaceAtlas

instance (EuclidSpace v1, EuclidSpace v2, Scalar v1~Scalar v2) => Manifold (v1, v2) where
  localAtlas = vectorSpaceAtlas




data S2 = S2 { ϑParamS2 :: Double -- [0, π[
             , φParamS2 :: Double -- [0, 2π[
             }
 

-- instance Manifold S2 where
--   type TangentSpace S2 = (Double, Double)
--   localAtlas (S2 ϑ φ)
--    | ϑ<pi-2     = [ Chart (\(x,y)
--                              -> S2(2 * sqrt(x^2+y^2)) (atan2 y x) )
--                           (\(S2 ϑ' φ')
--                              -> let r=ϑ'/2
--                                 in guard (r<1) >> Just (r * cos φ', r * sin φ') )
--                           LandlockedChart ]
--    | ϑ>2        = [ Chart (\(x,y)
--                              -> S2(pi - 2*sqrt(x^2+y^2)) (atan2 y x) )
--                           (\(S2 ϑ' φ')
--                              -> let r=(pi-ϑ')/2
--                                 in guard (r<1) >> Just (r * cos φ', r * sin φ') )
--                           LandlockedChart ]
--    | otherwise  = localAtlas(S2 0 φ) ++ localAtlas(S2 (2*pi) φ)
-- 





type Endomorphism a = a->a

