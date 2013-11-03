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
import Data.Maybe
import Data.Semigroup
import Data.Function hiding ((.), id)

import Data.VectorSpace
import Data.Basis

import Prelude hiding((.), id)

import Control.Category
import Control.Arrow
import Control.Monad
import Control.Comonad




-- | Continuous mapping.
data domain :--> codomain where
  Continuous_id :: x:-->x
  Continuous :: ( Manifold d, Manifold c
                , v ~ TangentSpace d, u ~ TangentSpace c
                , δ ~ Scalar v, ε ~ Scalar u, δ ~ ε) =>
        { runContinuous :: Chart d -> v -> (Chart c, u, ε->Option δ) }
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


continuous_id' ::  Manifold m => m :--> m
continuous_id' = Continuous id'
 where id' chart v = (chart, v, return)


type HasLocalDistance m d = (Manifold m, d ~ Scalar (TangentSpace m))
type EqvMetricSpaces a b = Scalar (TangentSpace a) ~ Scalar (TangentSpace b)

const__ :: (Manifold d, Manifold c, Scalar(TangentSpace d)~Scalar(TangentSpace c))
    => c -> d:-->c
const__ x = Continuous f
 where f _ _ = (tgtChart, w, const mzero)
       tgtChart = head $ localAtlas x
       tchOut = case tgtChart of Chart _ tchOut _ -> tchOut
       w = fromJust (tchOut x) --$ x


flatContinuous :: (FlatManifold v, FlatManifold w, δ~Scalar v, ε~Scalar w, δ~ε)
    => (v -> (w, ε -> Option δ)) -> (v:-->w)
flatContinuous f = Continuous cnt
 where cnt cct v = case cct of Chart inMap _ _ -> let
                                       (v', preEps) = runFlatContinuous inMap v
                                       (w, postEps) = f v'
                                    in (idChart, w, preEps>=>postEps)

runFlatContinuous :: (FlatManifold v, FlatManifold w, δ~Scalar v, ε~Scalar w, δ~ε)
    => (v:-->w) -> v -> (w, ε -> Option δ)
runFlatContinuous Continuous_id v = (v, return)
runFlatContinuous (Continuous cnf) v = (w, preEps>=>postEps)
 where (cc', v', preEps) = cnf idChart v
       (w, postEps) = case cc' of Chart inMap _ _ -> runFlatContinuous inMap v'


instance Category (:-->) where

  id = Continuous_id
  
  Continuous_id . f = f
  f . Continuous_id = f
  Continuous f . Continuous g = Continuous h
   where h srcChart u = (tgtChart, w, q>=>p)
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
  Chart :: (Manifold m, v ~ TangentSpace m, FlatManifold v) =>
        { chartInMap :: v :--> m
        , chartOutMap :: m -> Maybe (m:-->v)
        , chartKind :: ChartKind      } -> Chart m
data ChartKind = LandlockedChart  -- ^ A /M/ ⇆ /Dⁿ/ chart, for ordinary manifolds
               | RimChart         -- ^ A /M/ ⇆ /Hⁿ/ chart, for manifolds with a rim


type FlatManifold v = (Manifold v, v~TangentSpace v)

-- | 'idChart' is a special case, partly for efficiency reasons. This is interesting for
-- continuous mapping betwees vector spaces. In this case the chart maps not between
-- the space an open disk therein, but just is an \"alias\" for the whole space.
idChart :: FlatManifold v => Chart v
idChart = Chart { chartInMap  = id
                , chartOutMap = const $ Just id
                , chartKind   = LandlockedChart } 



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
  type TangentSpace m = m   -- For \"flat\", i.e. vector space manifolds.
  
  localAtlas :: m -> Atlas m


vectorSpaceAtlas :: FlatManifold v => v -> Atlas v
vectorSpaceAtlas _ = [idChart]


  

-- | At the moment, complex etc. manifolds are not supported (because 'EuclidSpace' requires its scalar to be 'Ord' right now).
instance Manifold Float where
  localAtlas = vectorSpaceAtlas
instance Manifold Double where
  localAtlas = vectorSpaceAtlas

type Representsℝ r = (EqFloating r, FlatManifold r, r~Scalar r)

continuousFlatFunction :: (FlatManifold d, FlatManifold c,  ε~Scalar c, δ~Scalar d, δ~ε) 
                          => (d -> (c, ε->Option δ)) -> d:-->c
continuousFlatFunction f = Continuous f'
 where f' (Chart Continuous_id _ _) x = (idChart, y, eps2Delta)
        where (y, eps2Delta) = f x

type CntnRealFunction = Representsℝ r => r :--> r

sin__, cos__ :: CntnRealFunction
sin__ = continuousFlatFunction sin'
 where sin' x = (sin x, eps2Delta)
        where eps2Delta ε
               | ε>2        = mzero
               | otherwise  = return $ ε / (dsinx + sqrt ε)
              dsinx = abs $ cos x
cos__ = continuousFlatFunction cos'
 where cos' x = (cos x, eps2Delta)
        where eps2Delta ε
               | ε>2        = mzero
               | otherwise  = return $ ε / (dcosx + sqrt ε)
              dcosx = abs $ sin x

exp__ :: CntnRealFunction
exp__ = continuousFlatFunction exp'
 where exp' x = (expx, eps2Delta)
        where expx = exp x
              eps2Delta ε = return . log $ (expx + ε)/expx
-- exp x + ε = exp (x + δ) = exp x * exp δ
-- δ = ln ( (exp x + ε)/exp x )


cntnFuncsCombine :: forall d v c c' c'' ε . 
         ( Manifold d, v ~ TangentSpace d
                     , FlatManifold c, FlatManifold c', FlatManifold c''
                     , ε ~ Scalar c  , ε ~ Scalar c'  , ε ~ Scalar c''   )
       => (c'->c''->(c, ε->(ε,ε))) -> (d:-->c') -> (d:-->c'') -> d:-->c
cntnFuncsCombine cmb Continuous_id g = cntnFuncsCombine cmb continuous_id' g
cntnFuncsCombine cmb f Continuous_id = cntnFuncsCombine cmb f continuous_id'
cntnFuncsCombine cmb (Continuous f) (Continuous g) = Continuous h
 where h ζd u = case (ζc', ζc'') of 
                 (Chart c'In _ _, Chart c''In _ _)
                   -> let (y', c'Eps) = runFlatContinuous c'In fu 
                          (y'', c''Eps) = runFlatContinuous c''In gu 
                          (y, epsSplit) = cmb y' y'' 
                          fullEps ε = fmap getMin $ (fmap Min $ fEps =<< c'Eps ε') 
                                                  <>(fmap Min $ gEps =<< c''Eps ε'')
                            where (ε', ε'') = epsSplit ε
                      in  (idChart, y, fullEps)
        where (ζc', fu, fEps) = f ζd u
              (ζc'',gu, gEps) = g ζd u


newtype CntnFuncValue d c = CntnFuncValue { runCntnFuncValue :: d :--> c }

continuous :: (CntnFuncValue d d -> CntnFuncValue d c) -> d:-->c
continuous f = case f $ CntnFuncValue id of CntnFuncValue q -> q


cntnFnValsApply :: (c':-->c) -> CntnFuncValue d c' -> CntnFuncValue d c 
cntnFnValsApply f (CntnFuncValue x) = CntnFuncValue $ f.x

cntnFnValsFunc :: ( Manifold d, FlatManifold c, FlatManifold c'
                  , ε~Scalar c, ε~Scalar c' )
             => (c' -> (c, ε->Option ε)) -> CntnFuncValue d c' -> CntnFuncValue d c
cntnFnValsFunc = cntnFnValsApply . continuousFlatFunction

cntnFnValsCombine :: forall d v c c' c'' ε . 
         ( Manifold d, v ~ TangentSpace d
                     , FlatManifold c, FlatManifold c', FlatManifold c''
                     , ε ~ Scalar c  , ε ~ Scalar c'  , ε ~ Scalar c''   )
       => (c'->c''->(c, ε->(ε,ε))) 
         -> CntnFuncValue d c' -> CntnFuncValue d c'' -> CntnFuncValue d c
cntnFnValsCombine cmb (CntnFuncValue f) (CntnFuncValue g) 
    = CntnFuncValue $ cntnFuncsCombine cmb f g

instance (Representsℝ r, Manifold d, EqvMetricSpaces r d) => Num (CntnFuncValue d r) where
  fromInteger = CntnFuncValue . const__ . fromInteger
  
  (+) = cntnFnValsCombine $ \a b -> (a+b, \ε -> (ε/2, ε/2))
  (-) = cntnFnValsCombine $ \a b -> (a-b, \ε -> (ε/2, ε/2))
  
  (*) = cntnFnValsCombine $ \a b -> (a*b, 
                             \ε -> (ε / (2 * sqrt(2*b^2+ε)), ε / (2 * sqrt(2*a^2+ε))))
  --  |δa| < ε / 2·sqrt(2·b² + ε) ∧ |δb| < ε / 2·sqrt(2·a² + ε)
  --  ⇒  | (a+δa) · (b+δb) - a·b | = | a·δb + b·δa + δa·δb | 
  --   ≤ | a·δb | + | b·δa | + | δa·δb |
  --   ≤ | a·ε/2·sqrt(2·a² + ε) | + | b·ε/2·sqrt(2·b² + ε) | + | ε² / 4·sqrt(2·b² + ε)·sqrt(2·a² + ε) |
  --   ≤ | a·ε/2·sqrt(2·a²) | + | b·ε/2·sqrt(2·b²) | + | ε² / 4·sqrt(ε)·sqrt(ε) |
  --   ≤ | ε/sqrt(8) | + | ε/sqrt(8) | + | ε / 4 |
  --   ≈ .96·ε < ε

  negate = cntnFnValsFunc $ \x -> (negate x, return)
  abs = cntnFnValsFunc $ \x -> (abs x, return)
  signum = cntnFnValsFunc $ \x -> (signum x, \ε -> if ε>2 then mzero else return $ abs x)

instance (EuclidSpace v1, EuclidSpace v2, Scalar v1~Scalar v2) => Manifold (v1, v2) where
  localAtlas = vectorSpaceAtlas



data GraphWindowSpec = GraphWindowSpec {
    lBound, rBound, bBound, tBound :: Double
  , xResolution, yResolution :: Int
  }

finiteGraphContinℝtoℝ :: (Double:-->Double) -> GraphWindowSpec -> [(Double, Double)]
finiteGraphContinℝtoℝ Continuous_id (GraphWindowSpec{..})
       = [(x, x) | x<-[lBound, rBound] ]
finiteGraphContinℝtoℝ fc (GraphWindowSpec{..}) 
       = refine [(x, f x, δyG) | x<-[lBound, rBound] ] [(rBound, fst $ f rBound)]
   where refine [(x₁, (y₁, eps₁), ε₁),  (x₂, (y₂, eps₂), ε₂)] = id
         f = runFlatContinuous fc
         δyG = (tBound - bBound) / fromIntegral yResolution




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

