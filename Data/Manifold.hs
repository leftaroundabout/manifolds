-- |
-- Module      : Data.Manifold
-- Copyright   : (c) Justus Sagemüller 2013
-- License     : GPL v3
-- 
-- Maintainer  : (@) sagemuej $ smail.uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 


{-#LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE UndecidableInstances     #-}
-- {-# LANGUAGE OverlappingInstances     #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE RankNTypes               #-}
{-# LANGUAGE TupleSections            #-}
{-# LANGUAGE ConstraintKinds          #-}
{-# LANGUAGE PatternGuards            #-}
{-# LANGUAGE LambdaCase               #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE ScopedTypeVariables      #-}
{-# LANGUAGE RecordWildCards          #-}


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
                , δ ~ Scalar v, ε ~ Scalar u) =>
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

const__ :: (Manifold c, Manifold d)
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

sin__, cos__, atan__ ,  exp__ , sinh__, cosh__, tanh__, asinh__ :: CntnRealFunction
sin__ = continuousFlatFunction sin'
 where sin' x = (sinx, eps2Delta)
        where eps2Delta ε
               | ε > 1 + abs sinx  = mzero
               | otherwise         = return $ ε / (dsinx + sqrt ε)
              dsinx = abs $ cos x
              sinx = sin x
cos__ = continuousFlatFunction cos'
 where cos' x = (cosx, eps2Delta)
        where eps2Delta ε
               | ε > 1 + abs cosx  = mzero
               | otherwise         = return $ ε / (dcosx + sqrt ε)
              dcosx = abs $ sin x
              cosx = cos x
atan__ = continuousFlatFunction atan'
 where atan' x = (atanx, eps2Delta)
        where eps2Delta ε
               | ε >= pi/2 + abs atanx  = mzero
               | otherwise              = return . abs $ tan (atanx + ε * signum x) - x
              atanx = atan x

exp__ = continuousFlatFunction exp'
 where exp' x = (expx, eps2Delta)
        where expx = exp x
              eps2Delta ε = return . log $ (expx + ε)/expx
-- exp x + ε = exp (x + δ) = exp x * exp δ
-- δ = ln ( (exp x + ε)/exp x )

sinh__ = continuousFlatFunction sinh'
 where sinh' x = (sinhx, eps2Delta)
        where eps2Delta ε = return $ asinh (abs sinhx + ε) - abs x
              sinhx = sinh x
cosh__ = continuousFlatFunction cosh'
 where cosh' x = (coshx, eps2Delta)
        where eps2Delta ε = return $ acosh (coshx + ε) - abs x
              coshx = cosh x
tanh__ = continuousFlatFunction tanh'
 where tanh' x = (tanhx, eps2Delta)
        where eps2Delta ε
               | ε >= 1 + abs tanhx  = mzero
               | otherwise           = return . abs $ atanh (tanhx - ε * signum x) - x
              tanhx = tanh x
asinh__ = continuousFlatFunction asinh'
 where asinh' x = (asinhx, eps2Delta)
        where eps2Delta ε = return . abs $ sinh (asinhx - ε * signum x) - x
              asinhx = asinh x
       

cntnFuncsCombine :: forall d v c c' c'' ε ε' ε''. 
         ( Manifold d, v ~ TangentSpace d
                     , FlatManifold c, FlatManifold c', FlatManifold c''
                     , ε ~ Scalar c  , ε' ~ Scalar c' , ε'' ~ Scalar c'', ε~ε', ε~ε''  )
       => (c'->c''->(c, ε->(ε',ε''))) -> (d:-->c') -> (d:-->c'') -> d:-->c
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


data CntnFuncValue d c = CntnFuncValue { runCntnFuncValue :: d :--> c }
                       | CntnFuncConst c

continuous :: (Manifold d, Manifold c)
              => (CntnFuncValue d d -> CntnFuncValue d c) -> d:-->c
continuous f = case f $ CntnFuncValue id of 
                          CntnFuncValue q -> q
                          CntnFuncConst c -> const__ c

constCntnFuncValue :: c -> CntnFuncValue d c
constCntnFuncValue = CntnFuncConst

cntnFnValsApply :: (c':-->c) -> CntnFuncValue d c' -> CntnFuncValue d c 
cntnFnValsApply f (CntnFuncValue x) = CntnFuncValue $ f.x
cntnFnValsApply f (CntnFuncConst x) = CntnFuncConst $ f--$x

cntnFnValsFunc :: ( Manifold d, FlatManifold c, FlatManifold c'
                  , ε~Scalar c, ε~Scalar c' )
             => (c' -> (c, ε->Option ε)) -> CntnFuncValue d c' -> CntnFuncValue d c
cntnFnValsFunc = cntnFnValsApply . continuousFlatFunction

cntnFnValsCombine :: forall d v c c' c'' ε ε' ε''. 
         ( Manifold d, v ~ TangentSpace d
                     , FlatManifold c, FlatManifold c', FlatManifold c''
                     , ε ~ Scalar c  , ε' ~ Scalar c'  , ε'' ~ Scalar c'', ε~ε', ε~ε''  )
       => (  c' -> c'' -> (c, ε -> (ε',(ε',ε''),ε''))  )
         -> CntnFuncValue d c' -> CntnFuncValue d c'' -> CntnFuncValue d c
cntnFnValsCombine cmb (CntnFuncValue f) (CntnFuncValue g) 
    = CntnFuncValue $ cntnFuncsCombine (second (>>> \(_,splε,_)->splε) .: cmb) f g
cntnFnValsCombine cmb (CntnFuncConst p) (CntnFuncConst q) 
    = CntnFuncConst . fst $ cmb p q
cntnFnValsCombine cmb f (CntnFuncConst q) 
    = cntnFnValsFunc (\c' -> second (>>> \(ε',_,_)->return ε') $ cmb c' q) f
cntnFnValsCombine cmb (CntnFuncConst p) g
    = cntnFnValsFunc (second (>>> \(_,_,ε'')->return ε'') . cmb p) g

instance (Representsℝ r, Manifold d, EqvMetricSpaces r d) => Num (CntnFuncValue d r) where
  fromInteger = constCntnFuncValue . fromInteger
  
  (+) = cntnFnValsCombine $ \a b -> (a+b, \ε -> (ε, (ε/2,ε/2), ε))
  (-) = cntnFnValsCombine $ \a b -> (a-b, \ε -> (ε, (ε/2,ε/2), ε))
  
  (*) = cntnFnValsCombine $ \a b -> (a*b, 
                             \ε -> ( ε/b
                                   , (ε / (2 * sqrt(2*b^2+ε)), ε / (2 * sqrt(2*a^2+ε)))
                                   , ε/a ))
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

instance (Representsℝ r, Manifold d, EqvMetricSpaces r d) => Fractional (CntnFuncValue d r) where
  fromRational = constCntnFuncValue . fromRational
  recip = cntnFnValsFunc $ \x -> let x¹ = recip x
                                 in (x¹, \ε -> return $ abs x - recip(ε + abs x¹))
  -- Readily derived from the worst-case of ε = 1 / (|x| – δ) – 1/|x|.

instance (Representsℝ r, Manifold d, EqvMetricSpaces r d) => Floating (CntnFuncValue d r) where
  pi = constCntnFuncValue pi
  
  exp = cntnFnValsApply exp__
  sin = cntnFnValsApply sin__
  cos = cntnFnValsApply cos__
  atan = cntnFnValsApply atan__
  sinh = cntnFnValsApply sinh__
  cosh = cntnFnValsApply cosh__
  tanh = cntnFnValsApply tanh__
  asinh = cntnFnValsApply asinh__
  
  log = cntnFnValsApply $ continuousFlatFunction ln'
   where ln' x = (lnx, eps2Delta)
          where lnx = log x
                eps2Delta ε = return $ x - exp (lnx - ε)
  asin = cntnFnValsApply $ continuousFlatFunction asin'
   where asin' x = (asinx, eps2Delta)
          where asinx = asin x
                eps2Delta ε = return $ 
                    if ε > pi/2 - abs asinx
                     then 1 - abs x
                     else sin (abs asinx + ε) - abs x
  acos = cntnFnValsApply $ continuousFlatFunction acos'
   where acos' x = (acosx, eps2Delta)
          where acosx = acos x
                eps2Delta ε = return $ 
                    if ε > pi/2 - abs (acosx - pi/2)
                     then 1 - abs x
                     else cos (abs acosx + ε) - abs x
  acosh = cntnFnValsApply $ continuousFlatFunction acosh'
   where acosh' x = (acoshx, eps2Delta)
          where acoshx = acosh x
                eps2Delta ε = return $ 
                    if ε > acoshx
                     then x - 1
                     else x - cosh (acoshx - ε)
  atanh = cntnFnValsApply $ continuousFlatFunction atanh'
   where atanh' x = (atanhx, eps2Delta)
          where atanhx = atanh x
                eps2Delta ε = return $ tanh (abs atanhx + ε) - abs x

instance (EuclidSpace v1, EuclidSpace v2, Scalar v1~Scalar v2) => Manifold (v1, v2) where
  localAtlas = vectorSpaceAtlas



data GraphWindowSpec = GraphWindowSpec {
    lBound, rBound, bBound, tBound :: Double
  , xResolution, yResolution :: Int
  }

finiteGraphContinℝtoℝ :: GraphWindowSpec -> (Double:-->Double) -> [(Double, Double)]
finiteGraphContinℝtoℝ (GraphWindowSpec{..}) Continuous_id 
       = [(x, x) | x<-[lBound, rBound] ]
finiteGraphContinℝtoℝ (GraphWindowSpec{..}) fc
       = connect [(x, f x, δyG) | x<-[lBound, rBound] ] [(rBound, fst $ f rBound)]
   where connect [(x₁, (y₁, eps₁), ε₁),  (x₂, (y₂, eps₂), ε₂)]
                = case (getOption $ eps₁ ε₁, getOption $ eps₂ ε₂) of
                   (Nothing, Nothing)                  -> done
                   (Just δ₁, Nothing) | δ₁>δxS         -> done
                                      | otherwise      -> refine
                   (Nothing, Just δ₂) | δ₂>δxS         -> done
                                      | otherwise      -> refine
                   (Just δ₁, Just δ₂) | δ₁>δxS, δ₂>δxS -> done
                                      | otherwise      -> refine
             where δxS = x₂-x₁
                   m = x₁ + δxS/2
                   fm@(ym, _) = f m
                   done = ((x₁, y₁) :)
                   refine = connect [(x₁, (y₁, eps₁), ε₁), (m, fm, ε')]
                          . connect [(m, fm, ε'), (x₂, (y₂, eps₂), ε₂)]
                   ε' = (if δxS < δxG then max (min (abs $ ym - y₁) (abs $ ym - y₂)) else id)
                          $ max ε₁ ε₂
         f = runFlatContinuous fc
         δxG = (rBound - lBound) / fromIntegral xResolution
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


(.:) :: (c->d) -> (a->b->c) -> a->b->d 
(.:) = (.) . (.)

