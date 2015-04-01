-- |
-- Module      : Data.Manifold
-- Copyright   : (c) Justus Sagemüller 2013
-- License     : GPL v3
-- 
-- Maintainer  : (@) sagemueller $ geo.uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 
-- This is something of a first attempt at formalising manifolds and continuous
-- mappings thereon. They /work/
-- (check out <http://hackage.haskell.org/package/dynamic-plot-0.1.0.0> for a use case),
-- but aren't very efficient. The interface might well change considerably in the future.


{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE UndecidableInstances     #-}
-- {-# LANGUAGE OverlappingInstances     #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE FunctionalDependencies   #-}
{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE RankNTypes               #-}
{-# LANGUAGE TupleSections            #-}
{-# LANGUAGE ConstraintKinds          #-}
{-# LANGUAGE PatternGuards            #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE ScopedTypeVariables      #-}
{-# LANGUAGE RecordWildCards          #-}


module Data.Manifold (module Data.Manifold, module Data.Manifold.Types.Primitive) where

import Data.List
import Data.Maybe
import Data.Semigroup
import Data.Function (on)

import Data.VectorSpace
import Data.AffineSpace
import Data.Basis
import Data.Complex hiding (magnitude)
import Data.Void
import Data.Manifold.Types.Primitive

import qualified Prelude

import Control.Category.Constrained.Prelude hiding ((^))
import Control.Arrow.Constrained
import Control.Monad.Constrained
import Data.Foldable.Constrained



-- | Continuous mapping.
data domain :--> codomain where
  Continuous :: ( Manifold d, Manifold c
                , v ~ TangentSpace d, u ~ TangentSpace c
                , δ ~ Metric v, ε ~ Metric u   ) =>
        { runContinuous :: Chart d -> v -> (Chart c, u, ε->Option δ) }
           -> d :--> c
   






continuous_id' ::  Manifold m => m :--> m
continuous_id' = Continuous id'
 where id' chart v = (chart, v, return)


const__ :: (Manifold c, Manifold d)
    => c -> d:-->c
const__ x = Continuous f
 where f _ _ = (tgtChart, w, const mzero)
       tgtChart = head $ localAtlas x
       w = case tgtChart of 
            IdChart          -> x
            Chart _ tchOut _ -> fromJust (tchOut x) $ x


flatContinuous :: ( FlatManifold v, FlatManifold w, δ~Metric v, ε~Metric w )
    => (v -> (w, ε -> Option δ)) -> (v:-->w)
flatContinuous f = Continuous cnt
 where cnt IdChart v = let (w, postEps) = f v 
                       in (IdChart, w, postEps)
       cnt (Chart inMap _ _) v = let (v', preEps) = runFlatContinuous inMap v
                                     (w, postEps) = f v'
                                 in (IdChart, w, preEps>=>postEps)

runFlatContinuous :: ( FlatManifold v, FlatManifold w, δ~Metric v, ε~Metric w )
    => (v:-->w) -> v -> (w, ε -> Option δ)
runFlatContinuous (Continuous cnf) v = (w, preEps>=>postEps)
 where (cc', v', preEps) = cnf IdChart v
       (w, postEps) = case cc' of 
           IdChart         -> (v', return)
           Chart inMap _ _ -> runFlatContinuous inMap v'


instance Category (:-->) where
  type Object (:-->) t = Manifold t

  id = Continuous $ \c v -> (c, v, just)
  
  Continuous f . Continuous g = Continuous h
   where h srcChart u = (tgtChart, w, q>=>p)
          where (interChart, v, p) = g srcChart u
                (tgtChart, w, q) = f interChart v
             
instance EnhancedCat (->) (:-->) where
  Continuous f `arr` x = y
   where (tch, v, _) = f sch u
         y = case tch of Chart tchIn _ _ -> tchIn $ v
                         IdChart         -> v
         u = case sch of Chart _ schOut _ -> fromJust (schOut x) $ x
                         IdChart          -> x
         sch = head $ localAtlas x


instance Cartesian (:-->) where
  type PairObjects (:-->) a b = ( FlatManifold a, FlatManifold b, Manifold(a,b) )
  swap = Continuous $ \c t -> case c of
           IdChart         -> let (v,w) = t in (IdChart, (w,v), return)
           Chart inMap _ _ -> let ((v,w), epsP) = runFlatContinuous inMap t 
                              in  (IdChart, (w,v), epsP)
  attachUnit = Continuous $ \c v -> case c of
           IdChart         -> (IdChart, (v,()), return)
           Chart inMap _ _ -> let (v', epsP) = runFlatContinuous inMap v
                              in  (IdChart, (v',()), epsP)
  detachUnit = Continuous $ \c t -> case c of
           IdChart         -> let (v,()) = t in (IdChart, v, return)
           Chart inMap _ _ -> let ((v,()), epsP) = runFlatContinuous inMap t
                              in  (IdChart, v, epsP)
  regroup = Continuous $ \c t -> case c of
           IdChart         -> let (u,(v,w)) = t in (IdChart, ((u,v),w), return)
           Chart inMap _ _ -> let ((u,(v,w)), epsP) = runFlatContinuous inMap t
                              in  (IdChart, ((u,v),w), epsP)
  regroup' = Continuous $ \c t -> case c of
           IdChart         -> let ((u,v),w) = t in (IdChart, (u,(v,w)), return)
           Chart inMap _ _ -> let (((u,v),w), epsP) = runFlatContinuous inMap t
                              in  (IdChart, (u,(v,w)), epsP)

instance Morphism (:-->) where
  first (Continuous f) = Continuous $ \c t -> case c of
           IdChart -> let (v,w) = t
                          (IdChart, v', epsP) = f IdChart v
                      in  (IdChart, (v',w), (/ sqrt 2) >>> 
                                            \ε -> fmap getMin $ (fmap Min $ epsP ε)
                                                              <>(just $ Min ε)      )
  second (Continuous g) = Continuous $ \c t -> case c of
           IdChart -> let (v,w) = t
                          (IdChart, w', epsP) = g IdChart w
                      in  (IdChart, (v,w'), (/ sqrt 2) >>> 
                                            \ε -> fmap getMin $ (just $ Min ε)
                                                              <>(fmap Min $ epsP ε) )
  Continuous f *** Continuous g = Continuous $ \c t -> case c of
           IdChart -> let (v,w) = t
                          (IdChart, v', epsPv) = f IdChart v
                          (IdChart, w', epsPw) = g IdChart w
                      in  (IdChart, (v',w'), (/ sqrt 2) >>> 
                                            \ε -> fmap getMin $ (fmap Min $ epsPv ε)
                                                              <>(fmap Min $ epsPw ε) )

instance PreArrow (:-->) where
  terminal = const__ ()
  Continuous f &&& Continuous g = Continuous $ \c v -> case c of
           IdChart -> let (IdChart, v', epsPv) = f IdChart v
                          (IdChart, w', epsPw) = g IdChart v
                      in  (IdChart, (v',w'), (/ sqrt 2) >>> 
                                            \ε -> fmap getMin $ (fmap Min $ epsPv ε)
                                                              <>(fmap Min $ epsPw ε) )
  fst = Continuous $ \c t -> case c of
           IdChart -> let (v,_) = t
                      in  (IdChart, v, return)
  snd = Continuous $ \c t -> case c of
           IdChart -> let (_,v) = t
                      in  (IdChart, v, return)
  





-- | A chart is a homeomorphism from a connected, open subset /Q/ ⊂ /M/ of
-- an /n/-manifold /M/ to either the open unit disk /Dⁿ/ ⊂ /V/ ≃ ℝ/ⁿ/, or
-- the half-disk /Hⁿ/ = {/x/ ∊ /Dⁿ/: x₀≥0}. In e.g. the former case, 'chartInMap'
-- is thus defined ∀ /v/ ∊ /V/ : |/v/| < 1, while 'chartOutMap p' will yield @Just x@
-- with /x/ ∊ /Dⁿ/ provided /p/ is in /Q/, and @Nothing@ otherwise.
-- Obviously, @fromJust . 'chartOutMap' . 'chartInMap'@ should be equivalent to @id@
-- on /Dⁿ/, and @'chartInMap' . fromJust . 'chartOutMap'@ to @id@ on /Q/.
data Chart :: * -> * where
  IdChart :: (FlatManifold v) => Chart v
  Chart :: (Manifold m, v ~ TangentSpace m, FlatManifold v) =>
        { chartInMap :: v :--> m
        , chartOutMap :: m -> Maybe (m:-->v)
        , chartKind :: ChartKind      } -> Chart m
data ChartKind = LandlockedChart  -- ^ A /M/ ⇆ /Dⁿ/ chart, for ordinary manifolds
               | RimChart         -- ^ A /M/ ⇆ /Hⁿ/ chart, for manifolds with a rim


type FlatManifold v = (MetricSpace v, Manifold v, v~TangentSpace v)




isInUpperHemi :: EuclidSpace v => v -> Bool
isInUpperHemi v = (snd . head) (decompose v) >= 0

-- rimGuard :: EuclidSpace v => ChartKind -> v -> Maybe v
-- rimGuard LandlockedChart v = Just v
-- rimGuard RimChart v
--  | isInUpperHemi v = Just v
--  | otherwise       = Nothing
-- 
-- chartEnv :: Manifold m => Chart m
--                -> (TangentSpace m->TangentSpace m)
--                -> m -> Maybe m
-- chartEnv IdChart f x = Just $ f x
-- chartEnv (Chart inMap outMap chKind) f x = do
--     vGet <- outMap x
--     let v = vGet $ x
--     v' <- rimGuard chKind v
--     Just $ inMap $ v'
-- 
  

 

type Atlas m = [Chart m]

class (MetricSpace(TangentSpace m), Metric(TangentSpace m) ~ ℝ) => Manifold m where
  type TangentSpace m :: *
  type TangentSpace m = m   -- For \"flat\", i.e. vector space manifolds.
  
  localAtlas :: m -> Atlas m


vectorSpaceAtlas :: FlatManifold v => v -> Atlas v
vectorSpaceAtlas _ = [IdChart]


  
instance Manifold () where
  type TangentSpace () = ()
  localAtlas = vectorSpaceAtlas

instance Manifold Double where
  localAtlas = vectorSpaceAtlas
  
instance ( FlatManifold v₁, FlatManifold v₂, Scalar v₁~Scalar v₂
         , MetricSpace (Scalar v₁), Metric (Scalar v₁)~ℝ
         , VectorSpace (v₁,v₂), Scalar (v₁,v₂) ~ Scalar v₁
         ) => Manifold (v₁,v₂) where
  localAtlas = vectorSpaceAtlas








type Representsℝ r = (EqFloating r, FlatManifold r, r~Scalar r, r~Metric r)

continuousFlatFunction :: ( FlatManifold d, FlatManifold c,  ε~Metric c, δ~Metric d ) 
                          => (d -> (c, ε->Option δ)) -> d:-->c
continuousFlatFunction f = Continuous f'
 where f' IdChart x = (IdChart, y, eps2Delta)
        where (y, eps2Delta) = f x
       f' (Chart inMap _ _) v = (IdChart, y, postEps>=>preEps)
        where (v', preEps) = runFlatContinuous inMap v
              (y, postEps) = f v'

type CntnRealFunction = Representsℝ r => r :--> r

sin__, cos__, atan__ ,  exp__ , sinh__, cosh__, tanh__, asinh__ :: CntnRealFunction
sin__ = continuousFlatFunction sin'
 where sin' x = (sinx, eps2Delta)
        where eps2Delta ε
               | ε > 1 + abs sinx  = nothing
               | otherwise         = just $ ε / (dsinx + sqrt ε)
              dsinx = abs $ cos x
              sinx = sin x
cos__ = continuousFlatFunction cos'
 where cos' x = (cosx, eps2Delta)
        where eps2Delta ε
               | ε > 1 + abs cosx  = nothing
               | otherwise         = just $ ε / (dcosx + sqrt ε)
              dcosx = abs $ sin x
              cosx = cos x
atan__ = continuousFlatFunction atan'
 where atan' x = (atanx, eps2Delta)
        where eps2Delta ε
               | ε >= pi/2 + abs atanx  = nothing
               | otherwise              = just $ abs x - tan (abs atanx - ε)
              atanx = atan x

exp__ = continuousFlatFunction exp'
 where exp' x = (expx, eps2Delta)
        where expx = exp x
              eps2Delta ε 
                | x>0, expx*2 == expx  = just 0   -- "Infinity" in floating-point
                | otherwise            = just $ log (expx + ε) - x
-- exp x + ε = exp (x + δ) = exp x * exp δ
-- δ = ln ( (exp x + ε)/exp x )

sinh__ = continuousFlatFunction sinh'
 where sinh' x = (sinhx, eps2Delta)
        where eps2Delta ε = just $ asinh (abs sinhx + ε) - abs x
              sinhx = sinh x
cosh__ = continuousFlatFunction cosh'
 where cosh' x = (coshx, eps2Delta)
        where eps2Delta ε = just $ acosh (coshx + ε) - abs x
              coshx = cosh x
tanh__ = continuousFlatFunction tanh'
 where tanh' x = (tanhx, eps2Delta)
        where eps2Delta ε
               | ε >= 1 + abs tanhx  = nothing
               | otherwise           = just $ abs x - atanh (abs tanhx - ε)
              tanhx = tanh x
asinh__ = continuousFlatFunction asinh'
 where asinh' x = (asinhx, eps2Delta)
        where eps2Delta ε = just $ abs x - sinh (abs asinhx - ε)
              asinhx = asinh x
       

cntnFuncsCombine :: forall d v c c' c'' ε ε' ε''. 
         (       FlatManifold c, FlatManifold c', FlatManifold c''
                     , ε ~ Metric c  , ε' ~ Metric c' , ε'' ~ Metric c'', ε~ε', ε~ε''  )
       => (c'->c''->(c, ε->(ε',ε''))) -> (d:-->c') -> (d:-->c'') -> d:-->c
cntnFuncsCombine cmb (Continuous f) (Continuous g) = Continuous h
 where h ζd u = case (ζc', ζc'') of 
                 (IdChart, IdChart) 
                   -> let (y, epsSplit) = cmb fu gu
                          fullEps ε = fmap getMin $ (fmap Min $ fEps ε') 
                                                  <>(fmap Min $ gEps ε'')
                           where (ε', ε'') = epsSplit ε
                      in  (IdChart, y, fullEps)
                 (IdChart, Chart c''In _ _)
                   -> let (y'', c''Eps) = runFlatContinuous c''In gu
                          (y, epsSplit) = cmb fu y''
                          fullEps ε = fmap getMin $ (fmap Min $ fEps ε')
                                                  <>(fmap Min $ gEps =<< c''Eps ε'')
                           where (ε', ε'') = epsSplit ε
                      in  (IdChart, y, fullEps)
                 (Chart c'In _ _, IdChart)
                   -> let (y', c'Eps) = runFlatContinuous c'In fu 
                          (y, epsSplit) = cmb y' gu
                          fullEps ε = fmap getMin $ (fmap Min $ fEps =<< c'Eps ε') 
                                                  <>(fmap Min $ gEps ε'')
                            where (ε', ε'') = epsSplit ε
                      in  (IdChart, y, fullEps)
                 (Chart c'In _ _, Chart c''In _ _)
                   -> let (y', c'Eps) = runFlatContinuous c'In fu 
                          (y'', c''Eps) = runFlatContinuous c''In gu 
                          (y, epsSplit) = cmb y' y'' 
                          fullEps ε = fmap getMin $ (fmap Min $ fEps =<< c'Eps ε') 
                                                  <>(fmap Min $ gEps =<< c''Eps ε'')
                            where (ε', ε'') = epsSplit ε
                      in  (IdChart, y, fullEps)
        where (ζc', fu, fEps) = f ζd u
              (ζc'',gu, gEps) = g ζd u


data CntnFuncValue d c = CntnFuncValue { runCntnFuncValue :: d :--> c }
                       | CntnFuncConst c

instance HasAgent (:-->) where
  type AgentVal (:-->) d c = CntnFuncValue d c
  alg f = case f $ CntnFuncValue id of 
                          CntnFuncValue q -> q
                          CntnFuncConst c -> const__ c
  f $~ CntnFuncValue g = CntnFuncValue $ f . g
  f $~ CntnFuncConst c = CntnFuncConst $ f $ c

instance PointAgent CntnFuncValue (:-->) d c where
  point = CntnFuncConst

instance CartesianAgent (:-->) where
  alg1to2 f = case f $ CntnFuncValue id of
       (CntnFuncConst c₁, CntnFuncConst c₂) -> const__ (c₁, c₂)
       (CntnFuncConst c₁, CntnFuncValue f₂)
            -> Continuous $ \IdChart x -> let (fx, epsP) = runFlatContinuous f₂ x
                                          in (IdChart, (c₁, fx), epsP) 
       (CntnFuncValue f₁, CntnFuncConst c₂)
            -> Continuous $ \IdChart x -> let (fx, epsP) = runFlatContinuous f₁ x
                                          in (IdChart, (fx, c₂), epsP) 
       (CntnFuncValue f₁, CntnFuncValue f₂) -> f₁ &&& f₂ 
  alg2to1 f = case f (CntnFuncValue fst) (CntnFuncValue snd) of
               CntnFuncConst c -> const__ c
               CntnFuncValue f -> f
  alg2to2 f = case f (CntnFuncValue fst) (CntnFuncValue snd) of
       (CntnFuncConst c₁, CntnFuncConst c₂) -> const__ (c₁, c₂)
       (CntnFuncConst c₁, CntnFuncValue f₂)
            -> Continuous $ \IdChart x -> let (fx, epsP) = runFlatContinuous f₂ x
                                          in (IdChart, (c₁, fx), epsP) 
       (CntnFuncValue f₁, CntnFuncConst c₂)
            -> Continuous $ \IdChart x -> let (fx, epsP) = runFlatContinuous f₁ x
                                          in (IdChart, (fx, c₂), epsP) 
       (CntnFuncValue f₁, CntnFuncValue f₂) -> f₁ &&& f₂ 



cntnFnValsFunc :: ( FlatManifold c, FlatManifold c', Manifold d
                  , ε~Metric c, ε~Metric c'                     )
             => (c' -> (c, ε->Option ε)) -> CntnFuncValue d c' -> CntnFuncValue d c
cntnFnValsFunc = ($~) . continuousFlatFunction

cntnFnValsCombine :: forall d c c' c'' ε ε' ε''. 
         (             FlatManifold c, FlatManifold c', FlatManifold c'', Manifold d
                     , ε ~ Metric c  , ε' ~ Metric c'  , ε'' ~ Metric c'', ε~ε', ε~ε''  )
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

instance (Representsℝ r, Manifold d) => Num (CntnFuncValue d r) where
  fromInteger = point . fromInteger
  
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
  signum = cntnFnValsFunc $ \x -> (signum x, \ε -> if ε>2 then nothing else just $ abs x)

instance (Representsℝ r, Manifold d) => Fractional (CntnFuncValue d r) where
  fromRational = point . fromRational
  recip = cntnFnValsFunc $ \x -> let x¹ = recip x
                                 in (x¹, \ε -> just $ abs x - recip(ε + abs x¹))
  -- Readily derived from the worst-case of ε = 1 / (|x| – δ) – 1/|x|.

instance (Representsℝ r, Manifold d) => Floating (CntnFuncValue d r) where
  pi = point pi
  
  exp x = exp__$~ x
  sin x = sin__$~ x
  cos x = cos__$~ x
  atan x = atan__$~ x
  sinh x = sinh__$~ x
  cosh x = cosh__$~ x
  tanh x = tanh__$~ x
  asinh x = asinh__$~ x
  
  log x = continuousFlatFunction ln' $~ x
   where ln' x = (lnx, eps2Delta)
          where lnx = log x
                eps2Delta ε = just $ x - exp (lnx - ε)
  asin x = continuousFlatFunction asin' $~ x
   where asin' x = (asinx, eps2Delta)
          where asinx = asin x
                eps2Delta ε = just $ 
                    if ε > pi/2 - abs asinx
                     then 1 - abs x
                     else sin (abs asinx + ε) - abs x
  acos x = continuousFlatFunction acos' $~ x
   where acos' x = (acosx, eps2Delta)
          where acosx = acos x
                eps2Delta ε = just $ 
                    if ε > pi/2 - abs (acosx - pi/2)
                     then 1 - abs x
                     else cos (abs acosx + ε) - abs x
  acosh x = continuousFlatFunction acosh' $~ x
   where acosh' x = (acoshx, eps2Delta)
          where acoshx = acosh x
                eps2Delta ε = just $ 
                    if ε > acoshx
                     then x - 1
                     else x - cosh (acoshx - ε)
  atanh x = continuousFlatFunction atanh' $~ x
   where atanh' x = (atanhx, eps2Delta)
          where atanhx = atanh x
                eps2Delta ε = just $ tanh (abs atanhx + ε) - abs x


instance (FlatManifold v, Manifold d) => AdditiveGroup (CntnFuncValue d v) where
  zeroV = point zeroV
  (^+^) = cntnFnValsCombine $ \a b -> (a^+^b, \ε -> (ε, (ε/2,ε/2), ε))
  negateV = cntnFnValsFunc $ \x -> (negateV x, return)

instance ( FlatManifold v, MetricSpace v, Metric v~ℝ, FlatManifold (Scalar v)
         , MetricSpace (Scalar v), Metric (Scalar v) ~ ℝ, Manifold d ) 
               => VectorSpace (CntnFuncValue d v) where
  type Scalar (CntnFuncValue d v) = CntnFuncValue d (Scalar v)
  (*^) = cntnFnValsCombine 
           $ \λ v -> ( λ*^v
                     , \ε -> let l = metric v
                                 λ' = metric λ
                             in ( ε/l
                                , ( ε / (2 * sqrt(2 * l^2 + ε))
                                  , ε / (2 * sqrt(2 * λ'^2 + ε)))
                                , ε / λ' ))
         
  











finiteGraphContinℝtoℝ :: GraphWindowSpec -> (Double:-->Double) -> [(Double, Double)]
finiteGraphContinℝtoℝ (GraphWindowSpec{..}) fc
       = connect [(x, f x, δyG) | x<-[lBound, rBound] ] [(rBound, fst (f rBound))]
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


finiteGraphContinℝtoℝ² :: GraphWindowSpec -> (Double:-->(Double, Double)) -> [[(Double, Double)]]
finiteGraphContinℝtoℝ² (GraphWindowSpec{..}) fc
       = map (\(tl, tu) -> reCoarsen $ connect (tl, f tl) (tu, f tu) [fst (f tu)]) segments
  where connect n₁@(t₁, (p₁, eps₁)) n₂@(t₂, (p₂, eps₂)) 
           | and . catMaybes $ map (getOption . fmap( > t₂ - t₁ ) . ($reso)) [eps₁, eps₂]  
                                                     = (p₁ : )
           | m <- (id &&& f) $ midBetween [t₁, t₂]   = connect n₁ m . connect m n₂

        segments = do
                 (start, dir) <- [ (Just 0                                 , -1)
                                 , (go (\_ -> not . inRange) reasonable 1 0, 1 ) ]
                 foldMap (`explore`dir) start
         where explore t₀ dir
                 | Just ti <- go (\_ -> inRange) reasonable dir t₀
                 , Just tb <- exitWindow (-dir) ti
                 , Just te <- exitWindow   dir  ti
                              = (if dir > 0 then (tb, te) else (te, tb)) : explore te dir
                 | otherwise  = []
                where exitWindow = go (\t p -> not $ reasonable t && inRange p) (const True)
               go isDone hasHope dir t
                 | not $ hasHope t  = Nothing
                 | isDone t p       = Just t
                 | Just s <- getOption(epsP $ mobility p)
                                    = go isDone hasHope dir $ t + dir * s
                 | otherwise        = Nothing
                where (p, epsP) = f t

        f = runFlatContinuous fc
        inRange (x, y) = x > lBound && x < rBound && y > bBound && y < tBound
        reasonable = (< 1e+250) . abs
        mobility = \p -> sqrt $ max (distanceSq p cp₁) (distanceSq p cp₂) 
         where cp₁ = ( midBetween[lBound, rBound, rBound], midBetween[bBound, tBound, tBound] )
               cp₂ = ( midBetween[lBound, lBound, rBound], midBetween[bBound, bBound, tBound] )
        resoSq = reso ^ 2
        reso = min ( (rBound - lBound) / fromIntegral xResolution )
                   ( (tBound - bBound) / fromIntegral yResolution ) * 2
        firstJust = head . catMaybes

        reCoarsen (p₁ : p₂ : ps)
          | distanceSq p₁ p₂ > resoSq  = p₁ : reCoarsen (p₂ : ps)
          | otherwise                  = reCoarsen (p₁ : ps)
        reCoarsen ps = ps


               
                      
        
midBetween :: (VectorSpace v, Fractional(Scalar v)) => [v] -> v
midBetween vs = sumV vs ^/ (fromIntegral $ length vs)





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







(.:) :: (c->d) -> (a->b->c) -> a->b->d 
(.:) = (.) . (.)


just = Option . Just
nothing = Option Nothing





class (RealFloat (Metric v), InnerSpace v) => MetricSpace v where
  type Metric v :: *
  type Metric v = ℝ
  metric :: v -> Metric v
  metric = sqrt . metricSq
  metricSq :: v -> Metric v
  metricSq = (^2) . metric
  (|*^) :: Metric v -> v -> v
  μ |*^ v = metricToScalar v μ *^ v 
  metricToScalar :: v -> Metric v -> Scalar v
  

instance MetricSpace () where
  metric = const 0
  metricToScalar = const id
instance MetricSpace ℝ where
  metric = id
  metricToScalar = const id
instance ( RealFloat r, MetricSpace r, Scalar (Complex r)~Metric r ) 
             => MetricSpace (Complex r) where
  type Metric (Complex r) = Metric r
  metricSq (a :+ b) = metricSq a + metricSq b
  metricToScalar = const id
instance ( MetricSpace v, MetricSpace (Scalar v)
         , MetricSpace w, Scalar v~Scalar w
         , Metric v~Metric (Scalar v), Metric w~Metric v
         , Metric(Scalar w)~Metric v, RealFloat (Metric v)
         ) => MetricSpace (v,w) where
  type Metric (v,w) = Metric v
  metricSq (v,w) = metric (magnitudeSq v) + metric (magnitudeSq w)
  metricToScalar (v,_) = metricToScalar v








