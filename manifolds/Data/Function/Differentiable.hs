-- |
-- Module      : Data.Function.Differentiable
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


module Data.Function.Differentiable (
            -- * Everywhere differentiable functions
              Differentiable
            -- * Almost-everywhere diff'able functions
            , PWDiffable
            -- * Region-wise defined diff'able functions
            , RWDiffable
            -- ** Operators for piecewise definition
            -- $definitionRegionOps
            , (?->), (?>), (?<), (?|:), backupRegions
            -- * Regions within a manifold
            , Region
            , smoothIndicator
            -- * Evaluation of differentiable functions
            , discretisePathIn
            , discretisePathSegs
            , continuityRanges
            , regionOfContinuityAround
            , analyseLocalBehaviour
            ) where
    


import Data.List
import qualified Data.Vector.Generic as Arr
import qualified Data.Vector
import Data.Maybe
import Data.Semigroup
import Data.Function (on)
import Data.Fixed

import Data.VectorSpace
import Data.LinearMap
import Data.LinearMap.HerMetric
import Data.MemoTrie (HasTrie(..))
import Data.AffineSpace
import Data.Basis
import Data.Complex hiding (magnitude)
import Data.Void
import Data.Tagged
import Data.Manifold.Types.Primitive
import Data.Manifold.PseudoAffine

import Data.CoNat
import Data.VectorSpace.FiniteDimensional

import qualified Numeric.LinearAlgebra.HMatrix as HMat

import qualified Prelude
import qualified Control.Applicative as Hask

import Control.Category.Constrained.Prelude hiding ((^))
import Control.Arrow.Constrained
import Control.Monad.Constrained
import Data.Foldable.Constrained






discretisePathIn :: WithField ℝ Manifold y
      => Int                        -- ^ Limit the number of steps taken in either direction. Note this will not cap the resolution but /length/ of the discretised path.
      -> ℝInterval                  -- ^ Parameter interval of interest.
      -> (RieMetric ℝ, RieMetric y) -- ^ Inaccuracy allowance /ε/.
      -> (Differentiable ℝ ℝ y)     -- ^ Path specification.
      -> [(ℝ,y)]                    -- ^ Trail of points along the path, such that a linear interpolation deviates nowhere by more as /ε/.
discretisePathIn nLim (xl, xr) (mx,my) (Differentiable f)
         = reverse (tail . take nLim $ traceFwd xl xm (-1))
          ++ take nLim (traceFwd xr xm 1)
 where traceFwd xlim x₀ dir
         | signum (x₀-xlim) == signum dir = [(xlim, fxlim)]
         | otherwise                      = (x₀, fx₀) : traceFwd xlim (x₀+xstep) dir
        where (fx₀, jf, δx²) = f x₀
              εx = my fx₀ `extendMetric` lapply jf (metricAsLength $ mx x₀)
              χ = metric (δx² εx) 1
              xstep = dir * min (abs x₀+1) (recip χ)
              (fxlim, _, _) = f xlim
       xm = (xr + xl) / 2
                      
type ℝInterval = (ℝ,ℝ)

continuityRanges :: WithField ℝ Manifold y
      => Int                        -- ^ Max number of exploration steps per region
      -> RieMetric ℝ                -- ^ Needed resolution of boundaries
      -> ℝ                          -- ^ Starting value of exploration (center)
      -> RWDiffable ℝ ℝ y           -- ^ Function to investigate
      -> ([ℝInterval], [ℝInterval]) -- ^ Subintervals on which the function is guaranteed continuous.
continuityRanges nLim δbf xc (RWDiffable f)
  | (GlobalRegion, _) <- f xc
                 = ([], [(-huge,huge)])
  | otherwise    = glueMid (go xc (-1)) (go xc 1)
 where go x₀ dir
         | yq₀ <= abs (lapply jq₀ 1 * step₀)
                      = go (x₀ + step₀/2) dir
         | RealSubray PositiveHalfSphere xl' <- rangeHere, dir > 0
                      = if definedHere then [(x₀, hugeℝVal)]
                                       else []
         | RealSubray NegativeHalfSphere xl' <- rangeHere, dir < 0
                      = if definedHere then [(-hugeℝVal, x₀)]
                                       else []
         | otherwise  = exit nLim dir x₀
        where (rangeHere, fq₀) = f x₀
              (PreRegion (Differentiable r₀)) = genericisePreRegion rangeHere
              (yq₀, jq₀, δyq₀) = r₀ x₀
              step₀ = dir/metric (δbf x₀) 1
              exit 0 _ xq
                | not definedHere  = []
                | xq < xc          = [(xq,x₀)]
                | otherwise        = [(x₀,xq)]
              exit nLim' dir' xq
                | yq₁<0 || as_devεδ δyq yq₁<abs stepp
                                      = exit (nLim'-1) (dir'/2) xq
                | yq₂<0
                , as_devεδ δyq (-yq₂)>=abs stepp
                , resoHere stepp<1    = (if definedHere
                                          then ((min x₀ xq₁, max x₀ xq₁):)
                                          else id) $ go xq₂ dir
                | otherwise           = exit (nLim'-1) dir xq₁
               where (yq, jq, δyq) = r₀ xq
                     xq₁ = xq + stepp
                     xq₂ = xq₁ + stepp
                     yq₁ = yq + f'x*stepp
                     yq₂ = yq₁ + f'x*stepp
                     f'x = lapply jq 1
                     stepp | f'x*dir < 0  = -0.9 * abs dir' * yq/f'x
                           | otherwise    = dir' * as_devεδ δyq yq -- TODO: memoise in `exit` recursion
                     resoHere = metricSq $ δbf xq
                     resoStep = dir/sqrt(resoHere 1)
              definedHere = case fq₀ of
                              Option (Just _) -> True
                              Option Nothing  -> False
       glueMid ((l,le):ls) ((re,r):rs) | le==re  = (ls, (l,r):rs)
       glueMid l r = (l,r)
       huge = exp $ fromIntegral nLim

discretisePathSegs :: WithField ℝ Manifold y
      => Int              -- ^ Maximum number of path segments and/or points per segment.
      -> ( RieMetric ℝ
         , RieMetric y )  -- ^ Inaccuracy allowance /δ/ for arguments
                          --   (mostly relevant for resolution of discontinuity boundaries –
                          --   consider it a “safety margin from singularities”),
                          --   and /ε/ for results in the target space.
      -> ℝ                -- ^ Starting value of exploration (center)
      -> RWDiffable ℝ ℝ y -- ^ Path specification. It is recommended that this
                          --   function be limited to a compact interval (e.g. with
                          --   '?>', '?<' and '?->'). For many functions the discretisation
                          --   will even work on an infinite interval: the point density
                          --   is exponentially decreased towards the infinities. But
                          --   this is still pretty bad for performance.
      -> ([[(ℝ,y)]], [[(ℝ,y)]]) -- ^ Discretised paths: continuous segments in either direction
discretisePathSegs nLim (mx,my) x₀ f@(RWDiffable ff)
                            = ( map discretise ivsL, map discretise ivsR )
 where (ivsL, ivsR) = continuityRanges nLim mx x₀ f
       discretise rng@(l,r) = discretisePathIn nLim rng (mx,my) fr
        where (_, Option (Just fr)) = ff $ (l+r)/2

              
analyseLocalBehaviour ::
    RWDiffable ℝ ℝ ℝ
 -> ℝ                      -- ^ /x/₀ value.
 -> Option ( (ℝ,ℝ)
           , ℝ->Option ℝ ) -- ^ /f/ /x/₀, derivative (i.e. Taylor-1-coefficient),
                           --   and reverse propagation of /O/ (/δ/²) bound.
analyseLocalBehaviour (RWDiffable f) x₀ = case f x₀ of
       (r, Option (Just (Differentiable fd)))
           | inRegion r x₀ -> return $
              let (fx, j, δf) = fd x₀
                  epsprop ε
                    | ε>0  = case metric (δf $ metricFromLength ε) 1 of
                               0  -> empty
                               δ' -> return $ recip δ'
                    | otherwise  = pure 0
              in ((fx, lapply j 1), epsprop)
       _ -> empty
 where inRegion GlobalRegion _ = True
       inRegion (PreRegion (Differentiable rf)) x
         | (yr,_,_) <- rf x   = yr>0

-- | Represent a 'Region' by a smooth function which is positive within the region,
--   and crosses zero at the boundary.
smoothIndicator :: LocallyScalable ℝ q => Region ℝ q -> Differentiable ℝ q ℝ
smoothIndicator (Region _ r₀) = let (PreRegion r) = genericisePreRegion r₀
                                in  r

regionOfContinuityAround :: RWDiffable ℝ q x -> q -> Region ℝ q
regionOfContinuityAround (RWDiffable f) q = Region q . fst . f $ q
              


hugeℝVal :: ℝ
hugeℝVal = 1e+100






type LinDevPropag d c = Metric c -> Metric d

unsafe_dev_ε_δ :: RealDimension a
                => String -> (a -> a) -> LinDevPropag a a
unsafe_dev_ε_δ errHint f d
            = let ε'² = metricSq d 1
              in if ε'²>0
                  then let δ = f . sqrt $ recip ε'²
                       in if δ > 0
                           then projector $ recip δ
                           else error $ "ε-δ propagator function for "
                                    ++errHint++", with ε="
                                    ++show(sqrt $ recip ε'²)
                                    ++ " gives non-positive δ="++show δ++"."
                  else zeroV
dev_ε_δ :: RealDimension a
         => (a -> a) -> Metric a -> Option (Metric a)
dev_ε_δ f d = let ε'² = metricSq d 1
              in if ε'²>0
                  then let δ = f . sqrt $ recip ε'²
                       in if δ > 0
                           then pure . projector $ recip δ
                           else empty
                  else pure zeroV

as_devεδ :: RealDimension a => LinDevPropag a a -> a -> a
as_devεδ ldp ε | ε>0
               , δ'² <- metricSq (ldp . projector $ recip ε) 1
               , δ'² > 0
                    = sqrt $ recip δ'²
               | otherwise  = 0

-- | The category of differentiable functions between manifolds over scalar @s@.
--   
--   As you might guess, these offer /automatic differentiation/ of sorts (basically,
--   simple forward AD), but that's in itself is not really the killer feature here.
--   More interestingly, we actually have the (à la Curry-Howard) /proof/
--   built in: the function /f/ has at /x/&#x2080; derivative /f'&#x2093;/&#x2080;,
--   if, for&#xb9; /&#x3b5;/>0, there exists /&#x3b4;/ such that
--   |/f/ /x/ &#x2212; (/f/ /x/&#x2080; + /x/&#x22c5;/f'&#x2093;/&#x2080;)| < /&#x3b5;/
--   for all |/x/ &#x2212; /x/&#x2080;| < /&#x3b4;/.
-- 
--   Observe that, though this looks quite similar to the standard definition
--   of differentiability, it is not equivalent thereto &#x2013; in fact it does
--   not prove any analytic properties at all. To make it equivalent, we need
--   a lower bound on /&#x3b4;/: simply /&#x3b4;/ gives us continuity, and for
--   continuous differentiability, /&#x3b4;/ must grow at least like &#x221a;/&#x3b5;/
--   for small /&#x3b5;/. Neither of these conditions are enforced by the type system,
--   but we do require them for any allowed values because these proofs are obviously
--   tremendously useful &#x2013; for instance, you can have a root-finding algorithm
--   and actually be sure you get /all/ solutions correctly, not just /some/ that are
--   (hopefully) the closest to some reference point you'd need to laborously define!
-- 
--   Unfortunately however, this also prevents doing any serious algebra etc. with the
--   category, because even something as simple as division necessary introduces singularities
--   where the derivatives must diverge.
--   Not to speak of many trigonometric e.g. trigonometric functions that
--   are undefined on whole regions. The 'PWDiffable' and 'RWDiffable' categories have explicit
--   handling for those issues built in; you may simply use these categories even when
--   you know the result will be smooth in your relevant domain (or must be, for e.g.
--   physics reasons).
--   
--   &#xb9;(The implementation does not deal with /&#x3b5;/ and /&#x3b4;/ as difference-bounding
--   reals, but rather as metric tensors that define a boundary by prohibiting the
--   overlap from exceeding one; this makes the concept actually work on general manifolds.)
newtype Differentiable s d c
   = Differentiable { runDifferentiable ::
                        d -> ( c   -- function value
                             , Needle d :-* Needle c -- Jacobian
                             , LinDevPropag d c -- Metric showing how far you can go
                                                -- from x₀ without deviating from the
                                                -- Taylor-1 approximation by more than
                                                -- some error margin
                             ) }
type (-->) = Differentiable ℝ


instance (MetricScalar s) => Category (Differentiable s) where
  type Object (Differentiable s) o = LocallyScalable s o
  id = Differentiable $ \x -> (x, idL, const zeroV)
  Differentiable f . Differentiable g = Differentiable $
     \x -> let (y, g', devg) = g x
               (z, f', devf) = f y
               devfg δz = let δy = transformMetric f' δz
                              εy = devf δz
                          in transformMetric g' εy ^+^ devg δy ^+^ devg εy
           in (z, f'*.*g', devfg)


instance (RealDimension s) => EnhancedCat (->) (Differentiable s) where
  arr (Differentiable f) x = let (y,_,_) = f x in y

instance (MetricScalar s) => Cartesian (Differentiable s) where
  type UnitObject (Differentiable s) = ZeroDim s
  swap = Differentiable $ \(x,y) -> ((y,x), lSwap, const zeroV)
   where lSwap = linear swap
  attachUnit = Differentiable $ \x -> ((x, Origin), lAttachUnit, const zeroV)
   where lAttachUnit = linear $ \x ->  (x, Origin)
  detachUnit = Differentiable $ \(x, Origin) -> (x, lDetachUnit, const zeroV)
   where lDetachUnit = linear $ \(x, Origin) ->  x
  regroup = Differentiable $ \(x,(y,z)) -> (((x,y),z), lRegroup, const zeroV)
   where lRegroup = linear regroup
  regroup' = Differentiable $ \((x,y),z) -> ((x,(y,z)), lRegroup, const zeroV)
   where lRegroup = linear regroup'


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



actuallyLinear :: ( WithField s LinearManifold x, WithField s LinearManifold y )
            => (x:-*y) -> Differentiable s x y
actuallyLinear f = Differentiable $ \x -> (lapply f x, f, const zeroV)

actuallyAffine :: ( WithField s LinearManifold x, WithField s AffineManifold y )
            => y -> (x:-*Diff y) -> Differentiable s x y
actuallyAffine y₀ f = Differentiable $ \x -> (y₀ .+^ lapply f x, f, const zeroV)


dfblFnValsFunc :: ( LocallyScalable s c, LocallyScalable s c', LocallyScalable s d
                  , v ~ Needle c, v' ~ Needle c'
                  , ε ~ HerMetric v, ε ~ HerMetric v' )
             => (c' -> (c, v':-*v, ε->ε)) -> DfblFuncValue s d c' -> DfblFuncValue s d c
dfblFnValsFunc f = (Differentiable f $~)

dfblFnValsCombine :: forall d c c' c'' v v' v'' ε ε' ε'' s. 
         ( LocallyScalable s c,  LocallyScalable s c',  LocallyScalable s c''
         ,  LocallyScalable s d
         , v ~ Needle c, v' ~ Needle c', v'' ~ Needle c''
         , ε ~ HerMetric v  , ε' ~ HerMetric v'  , ε'' ~ HerMetric v'', ε~ε', ε~ε''  )
       => (  c' -> c'' -> (c, (v',v''):-*v, ε -> (ε',ε''))  )
         -> DfblFuncValue s d c' -> DfblFuncValue s d c'' -> DfblFuncValue s d c
dfblFnValsCombine cmb (GenericAgent (Differentiable f))
                      (GenericAgent (Differentiable g)) 
    = GenericAgent . Differentiable $
        \d -> let (c', f', devf) = f d
                  (c'', g', devg) = g d
                  (c, h', devh) = cmb c' c''
                  h'l = h' *.* lcofst; h'r = h' *.* lcosnd
              in ( c
                 , h' *.* linear (lapply f' &&& lapply g')
                 , \εc -> let εc' = transformMetric h'l εc
                              εc'' = transformMetric h'r εc
                              (δc',δc'') = devh εc 
                          in devf εc' ^+^ devg εc''
                               ^+^ transformMetric f' δc'
                               ^+^ transformMetric g' δc''
                 )
 where lcofst = linear(,zeroV)
       lcosnd = linear(zeroV,) 





instance (WithField s LinearManifold v, LocallyScalable s a, Floating s)
    => AdditiveGroup (DfblFuncValue s a v) where
  zeroV = point zeroV
  (^+^) = dfblFnValsCombine $ \a b -> (a^+^b, lPlus, const zeroV)
      where lPlus = linear $ uncurry (^+^)
  negateV = dfblFnValsFunc $ \a -> (negateV a, lNegate, const zeroV)
      where lNegate = linear negateV
  
instance (RealDimension n, LocallyScalable n a)
            => Num (DfblFuncValue n a n) where
  fromInteger i = point $ fromInteger i
  (+) = dfblFnValsCombine $ \a b -> (a+b, lPlus, const zeroV)
      where lPlus = linear $ uncurry (+)
  (*) = dfblFnValsCombine $
          \a b -> ( a*b
                  , linear $ \(da,db) -> a*db + b*da
                  , \d -> let d¹₂ = sqrt d in (d¹₂,d¹₂)
                           -- ε δa δb = (a+δa)·(b+δb) - (a·b + (a·δa + b·δb)) 
                           --         = δa·δb
                           --   so choose δa = δb = √ε
                  )
  negate = dfblFnValsFunc $ \a -> (negate a, lNegate, const zeroV)
      where lNegate = linear negate
  abs = dfblFnValsFunc dfblAbs
   where dfblAbs a
          | a>0        = (a, idL, unsafe_dev_ε_δ("abs "++show a) $ \ε -> a + ε/2) 
          | a<0        = (-a, negateV idL, unsafe_dev_ε_δ("abs "++show a) $ \ε -> ε/2 - a)
          | otherwise  = (0, zeroV, (^/ sqrt 2))
  signum = dfblFnValsFunc dfblSgn
   where dfblSgn a
          | a>0        = (1, zeroV, unsafe_dev_ε_δ("signum "++show a) $ const a)
          | a<0        = (-1, zeroV, unsafe_dev_ε_δ("signum "++show a) $ \_ -> -a)
          | otherwise  = (0, zeroV, const $ projector 1)



-- VectorSpace instance is more problematic than you'd think: multiplication
-- requires the allowed-deviation backpropagators to be split as square
-- roots, but the square root of a nontrivial-vector-space metric requires
-- an eigenbasis transform, which we have not implemented yet.
-- 
-- instance (WithField s LinearManifold v, LocallyScalable s a, Floating s)
--       => VectorSpace (DfblFuncValue s a v) where
--   type Scalar (DfblFuncValue s a v) = DfblFuncValue s a (Scalar v)
--   (*^) = dfblFnValsCombine $ \μ v -> (μ*^v, lScl, \ε -> (ε ^* sqrt 2, ε ^* sqrt 2))
--       where lScl = linear $ uncurry (*^)


-- | Important special operator needed to compute intersection of 'Region's.
minDblfuncs :: (LocallyScalable s m, RealDimension s)
     => Differentiable s m s -> Differentiable s m s -> Differentiable s m s
minDblfuncs (Differentiable f) (Differentiable g) = Differentiable h
 where h x
         | fx < gx   = ( fx, jf
                       , \d -> devf d ^+^ devg d
                               ^+^ transformMetric δj
                                      (projector . recip $ recip(metric d 1) + gx - fx) )
         | fx > gx   = ( gx, jg
                       , \d -> devf d ^+^ devg d
                               ^+^ transformMetric δj
                                      (projector . recip $ recip(metric d 1) + fx - gx) )
         | otherwise = ( fx, (jf^+^jg)^/2
                      , \d -> devf d ^+^ devg d
                               ^+^ transformMetric δj d )
        where (fx, jf, devf) = f x
              (gx, jg, devg) = g x
              δj = jf ^-^ jg


postEndo :: ∀ c a b . (HasAgent c, Object c a, Object c b)
                        => c a a -> GenericAgent c b a -> GenericAgent c b a
postEndo = genericAgentMap


-- | A pathwise connected subset of a manifold @m@, whose tangent space has scalar @s@.
data Region s m = Region { regionRefPoint :: m
                         , regionRDef :: PreRegion s m }

-- | A 'PreRegion' needs to be associated with a certain reference point ('Region'
--   includes that point) to define a connected subset of a manifold.
data PreRegion s m where
  GlobalRegion :: PreRegion s m
  RealSubray :: RealDimension s => S⁰ -> s -> PreRegion s s
  PreRegion :: (Differentiable s m s) -- A function that is positive at reference point /p/,
                                      -- decreases and crosses zero at the region's
                                      -- boundaries. (If it goes positive again somewhere
                                      -- else, these areas shall /not/ be considered
                                      -- belonging to the (by definition connected) region.)
         -> PreRegion s m

genericisePreRegion :: (RealDimension s, LocallyScalable s m)
                          => PreRegion s m -> PreRegion s m
genericisePreRegion GlobalRegion = PreRegion $ const 1
genericisePreRegion (RealSubray PositiveHalfSphere xl) = preRegionToInfFrom' xl
genericisePreRegion (RealSubray NegativeHalfSphere xr) = preRegionFromMinInfTo' xr
genericisePreRegion r = r

-- | Set-intersection of regions would not be guaranteed to yield a connected result
--   or even have the reference point of one region contained in the other. This
--   combinator assumes (unchecked) that the references are in a connected
--   sub-intersection, which is used as the result.
unsafePreRegionIntersect :: (RealDimension s, LocallyScalable s a)
                  => PreRegion s a -> PreRegion s a -> PreRegion s a
unsafePreRegionIntersect GlobalRegion r = r
unsafePreRegionIntersect r GlobalRegion = r
unsafePreRegionIntersect (RealSubray PositiveHalfSphere xl) (RealSubray PositiveHalfSphere xl')
                 = RealSubray PositiveHalfSphere $ max xl xl'
unsafePreRegionIntersect (RealSubray NegativeHalfSphere xr) (RealSubray NegativeHalfSphere xr')
                 = RealSubray PositiveHalfSphere $ min xr xr'
unsafePreRegionIntersect (PreRegion ra) (PreRegion rb) = PreRegion $ minDblfuncs ra rb
unsafePreRegionIntersect ra rb
   = unsafePreRegionIntersect (genericisePreRegion ra) (genericisePreRegion rb)

-- | Cartesian product of two regions.
regionProd :: (RealDimension s, LocallyScalable s a, LocallyScalable s b)
                  => Region s a -> Region s b -> Region s (a,b)
regionProd (Region a₀ ra) (Region b₀ rb) = Region (a₀,b₀) (preRegionProd ra rb)

-- | Cartesian product of two pre-regions.
preRegionProd :: (RealDimension s, LocallyScalable s a, LocallyScalable s b)
                  => PreRegion s a -> PreRegion s b -> PreRegion s (a,b)
preRegionProd GlobalRegion GlobalRegion = GlobalRegion
preRegionProd GlobalRegion (PreRegion rb) = PreRegion $ rb . snd
preRegionProd (PreRegion ra) GlobalRegion = PreRegion $ ra . fst
preRegionProd (PreRegion ra) (PreRegion rb) = PreRegion $ minDblfuncs (ra.fst) (rb.snd)
preRegionProd ra rb = preRegionProd (genericisePreRegion ra) (genericisePreRegion rb)


positivePreRegion, negativePreRegion :: (RealDimension s) => PreRegion s s
positivePreRegion = RealSubray PositiveHalfSphere 0
negativePreRegion = RealSubray NegativeHalfSphere 0


positivePreRegion', negativePreRegion' :: (RealDimension s) => PreRegion s s
positivePreRegion' = PreRegion $ Differentiable prr
 where prr x = ( 1 - 1/xp1
               , (1/xp1²) *^ idL
               , unsafe_dev_ε_δ("positivePreRegion@"++show x) δ )
                 -- ε = (1 − 1/(1+x)) + (-δ · 1/(x+1)²) − (1 − 1/(1+x−δ))
                 --   = 1/(1+x−δ) − 1/(1+x) − δ · 1/(x+1)²
                 --
                 -- ε·(1+x−δ) = 1 − (1+x−δ)/(1+x) − δ·(1+x-δ)/(x+1)²
                 -- ε·(1+x) − ε·δ = 1 − 1/(1+x) − x/(1+x) + δ/(1+x)
                 --                               − δ/(x+1)² − δ⋅x/(x+1)² + δ²/(x+1)²
                 --               = 1 − (1+x)/(1+x) + ((x+1) − 1)⋅δ/(x+1)²
                 --                               − δ⋅x/(x+1)² + δ²/(x+1)²
                 --               = 1 − 1 + x⋅δ/(x+1)² − δ⋅x/(x+1)² + δ²/(x+1)²
                 --               = δ²/(x+1)²
                 --
                 -- ε·(x+1)⋅(x+1)² − ε·δ⋅(x+1)² = δ²
                 -- 0 = δ² + ε·(x+1)²·δ − ε·(x+1)³
                 --
                 -- δ = let μ = ε·(x+1)²/2          -- Exact form
                 --     in -μ + √(μ² + ε·(x+1)³)    -- (not overflow save)
                 --
                 -- Safe approximation for large x:
                 -- ε = 1/(1+x−δ) − 1/(1+x) − δ · 1/(x+1)²
                 --   ≤ 1/(1+x−δ) − 1/(1+x)
                 -- 
                 -- ε⋅(1+x−δ)⋅(1+x) ≤ 1+x − (1+x−δ) = δ
                 -- 
                 -- δ ≥ ε + ε⋅x − ε⋅δ + ε⋅x + ε⋅x² − ε⋅δ⋅x
                 --
                 -- δ⋅(1 + ε + ε⋅x) ≥ ε + ε⋅x + ε⋅x + ε⋅x² ≥ ε⋅x²
                 --
                 -- δ ≥ ε⋅x²/(1 + ε + ε⋅x)
                 --   = ε⋅x/(1/x + ε/x + ε)
        where δ ε | x<100      = let μ = ε*xp1²/2
                                 in sqrt(μ^2 + ε * xp1² * xp1) - μ
                  | otherwise  = ε * x / ((1+ε)/x + ε)
              xp1 = (x+1)
              xp1² = xp1 ^ 2
negativePreRegion' = PreRegion $ ppr . ngt
 where PreRegion ppr = positivePreRegion'
       ngt = actuallyLinear $ linear negate

preRegionToInfFrom, preRegionFromMinInfTo :: RealDimension s => s -> PreRegion s s
preRegionToInfFrom = RealSubray PositiveHalfSphere
preRegionFromMinInfTo = RealSubray NegativeHalfSphere

preRegionToInfFrom', preRegionFromMinInfTo' :: RealDimension s => s -> PreRegion s s
preRegionToInfFrom' xs = PreRegion $ ppr . trl
 where PreRegion ppr = positivePreRegion'
       trl = actuallyAffine (-xs) idL
preRegionFromMinInfTo' xe = PreRegion $ ppr . flp
 where PreRegion ppr = positivePreRegion'
       flp = actuallyAffine (-xe) (linear negate)

intervalPreRegion :: RealDimension s => (s,s) -> PreRegion s s
intervalPreRegion (lb,rb) = PreRegion $ Differentiable prr
 where m = lb + radius; radius = (rb - lb)/2
       prr x = ( 1 - ((x-m)/radius)^2
               , (2*(m-x)/radius^2) *^ idL
               , unsafe_dev_ε_δ("intervalPreRegion@"++show x) $ (*radius) . sqrt )




-- | Category of functions that almost everywhere have an open region in
--   which they are continuously differentiable, i.e. /PieceWiseDiff'able/.
newtype PWDiffable s d c
   = PWDiffable {
        getDfblDomain :: d -> (PreRegion s d, Differentiable s d c) }



instance (RealDimension s) => Category (PWDiffable s) where
  type Object (PWDiffable s) o = LocallyScalable s o
  id = PWDiffable $ \x -> (GlobalRegion, id)
  PWDiffable f . PWDiffable g = PWDiffable h
   where h x₀ = case g x₀ of
                 (GlobalRegion, gr)
                  -> let (y₀,_,_) = runDifferentiable gr x₀
                     in case f y₀ of
                         (GlobalRegion, fr) -> (GlobalRegion, fr . gr)
                         (PreRegion ry, fr)
                               -> ( PreRegion $ ry . gr, fr . gr )
                 (PreRegion rx, gr)
                  -> let (y₀,_,_) = runDifferentiable gr x₀
                     in case f y₀ of
                         (GlobalRegion, fr) -> (PreRegion rx, fr . gr)
                         (PreRegion ry, fr)
                               -> ( PreRegion $ minDblfuncs (ry . gr) rx
                                  , fr . gr )
          where (rx, gr) = g x₀

globalDiffable :: Differentiable s a b -> PWDiffable s a b
globalDiffable f = PWDiffable $ const (GlobalRegion, f)

instance (RealDimension s) => EnhancedCat (PWDiffable s) (Differentiable s) where
  arr = globalDiffable
instance (RealDimension s) => EnhancedCat (->) (PWDiffable s) where
  arr (PWDiffable g) x = let (_,Differentiable f) = g x
                             (y,_,_) = f x 
                         in y

                
instance (RealDimension s) => Cartesian (PWDiffable s) where
  type UnitObject (PWDiffable s) = ZeroDim s
  swap = globalDiffable swap
  attachUnit = globalDiffable attachUnit
  detachUnit = globalDiffable detachUnit
  regroup = globalDiffable regroup
  regroup' = globalDiffable regroup'
  
instance (RealDimension s) => Morphism (PWDiffable s) where
  PWDiffable f *** PWDiffable g = PWDiffable h
   where h (x,y) = (preRegionProd rfx rgy, dff *** dfg)
          where (rfx, dff) = f x
                (rgy, dfg) = g y

instance (RealDimension s) => PreArrow (PWDiffable s) where
  PWDiffable f &&& PWDiffable g = PWDiffable h
   where h x = (unsafePreRegionIntersect rfx rgx, dff &&& dfg)
          where (rfx, dff) = f x
                (rgx, dfg) = g x
  terminal = globalDiffable terminal
  fst = globalDiffable fst
  snd = globalDiffable snd


instance (RealDimension s) => WellPointed (PWDiffable s) where
  unit = Tagged Origin
  globalElement x = PWDiffable $ \Origin -> (GlobalRegion, globalElement x)
  const x = PWDiffable $ \_ -> (GlobalRegion, const x)


type PWDfblFuncValue s = GenericAgent (PWDiffable s)

instance RealDimension s => HasAgent (PWDiffable s) where
  alg = genericAlg
  ($~) = genericAgentMap
instance RealDimension s => CartesianAgent (PWDiffable s) where
  alg1to2 = genericAlg1to2
  alg2to1 = genericAlg2to1
  alg2to2 = genericAlg2to2
instance (RealDimension s)
      => PointAgent (PWDfblFuncValue s) (PWDiffable s) a x where
  point = genericPoint

gpwDfblFnValsFunc
     :: ( RealDimension s
        , LocallyScalable s c, LocallyScalable s c', LocallyScalable s d
        , v ~ Needle c, v' ~ Needle c'
        , ε ~ HerMetric v, ε ~ HerMetric v' )
             => (c' -> (c, v':-*v, ε->ε)) -> PWDfblFuncValue s d c' -> PWDfblFuncValue s d c
gpwDfblFnValsFunc f = (PWDiffable (\_ -> (GlobalRegion, Differentiable f)) $~)

gpwDfblFnValsCombine :: forall d c c' c'' v v' v'' ε ε' ε'' s. 
         ( LocallyScalable s c,  LocallyScalable s c',  LocallyScalable s c''
         , LocallyScalable s d, RealDimension s
         , v ~ Needle c, v' ~ Needle c', v'' ~ Needle c''
         , ε ~ HerMetric v  , ε' ~ HerMetric v'  , ε'' ~ HerMetric v'', ε~ε', ε~ε''  )
       => (  c' -> c'' -> (c, (v',v''):-*v, ε -> (ε',ε''))  )
         -> PWDfblFuncValue s d c' -> PWDfblFuncValue s d c'' -> PWDfblFuncValue s d c
gpwDfblFnValsCombine cmb (GenericAgent (PWDiffable fpcs))
                         (GenericAgent (PWDiffable gpcs)) 
    = GenericAgent . PWDiffable $
        \d₀ -> let (rc', Differentiable f) = fpcs d₀
                   (rc'',Differentiable g) = gpcs d₀
               in (unsafePreRegionIntersect rc' rc'',) . Differentiable $
                    \d -> let (c', f', devf) = f d
                              (c'',g', devg) = g d
                              (c, h', devh) = cmb c' c''
                              h'l = h' *.* lcofst; h'r = h' *.* lcosnd
                          in ( c
                             , h' *.* linear (lapply f' &&& lapply g')
                             , \εc -> let εc' = transformMetric h'l εc
                                          εc'' = transformMetric h'r εc
                                          (δc',δc'') = devh εc 
                                      in devf εc' ^+^ devg εc''
                                           ^+^ transformMetric f' δc'
                                           ^+^ transformMetric g' δc''
                             )
 where lcofst = linear(,zeroV)
       lcosnd = linear(zeroV,) 


instance (WithField s LinearManifold v, LocallyScalable s a, RealDimension s)
    => AdditiveGroup (PWDfblFuncValue s a v) where
  zeroV = point zeroV
  (^+^) = gpwDfblFnValsCombine $ \a b -> (a^+^b, lPlus, const zeroV)
      where lPlus = linear $ uncurry (^+^)
  negateV = gpwDfblFnValsFunc $ \a -> (negateV a, lNegate, const zeroV)
      where lNegate = linear negateV

instance (RealDimension n, LocallyScalable n a)
            => Num (PWDfblFuncValue n a n) where
  fromInteger i = point $ fromInteger i
  (+) = gpwDfblFnValsCombine $ \a b -> (a+b, lPlus, const zeroV)
      where lPlus = linear $ uncurry (+)
  (*) = gpwDfblFnValsCombine $
          \a b -> ( a*b
                  , linear $ \(da,db) -> a*db + b*da
                  , \d -> let d¹₂ = sqrt d in (d¹₂,d¹₂)
                  )
  negate = gpwDfblFnValsFunc $ \a -> (negate a, lNegate, const zeroV)
      where lNegate = linear negate
  abs = (PWDiffable absPW $~)
   where absPW a₀
          | a₀<0       = (negativePreRegion, desc)
          | otherwise  = (positivePreRegion, asc)
         desc = actuallyLinear $ linear negate
         asc = actuallyLinear idL
  signum = (PWDiffable sgnPW $~)
   where sgnPW a₀
          | a₀<0       = (negativePreRegion, const $ -1)
          | otherwise  = (positivePreRegion, const 1)

instance (RealDimension n, LocallyScalable n a)
            => Fractional (PWDfblFuncValue n a n) where
  fromRational i = point $ fromRational i
  recip = postEndo . PWDiffable $ \a₀ -> if a₀<0
                                          then (negativePreRegion, Differentiable negp)
                                          else (positivePreRegion, Differentiable posp)
   where negp x = (x'¹, (- x'¹^2) *^ idL, unsafe_dev_ε_δ("1/"++show x) δ)
          where δ ε = let mph = -ε*x^2/2
                          δ₀ = mph + sqrt (mph^2 - ε*x^3)
                 -- See `Fractional RWDfblFuncValue` instance for explanation.
                      in if δ₀>0 then δ₀ else -x
                x'¹ = recip x
         posp x = (x'¹, (- x'¹^2) *^ idL, unsafe_dev_ε_δ("1/"++show x) δ)
          where δ ε = let mph = -ε*x^2/2
                          δ₀ = sqrt (mph^2 + ε*x^3) - mph
                      in if δ₀>0 then δ₀ else x
                x'¹ = recip x






-- | Category of functions that, where defined, have an open region in
--   which they are continuously differentiable. Hence /RegionWiseDiff'able/.
--   Basically these are the partial version of `PWDiffable`.
-- 
--   Though the possibility of undefined regions is of course not too nice
--   (we don't need Java to demonstrate this with its everywhere-looming @null@ values...),
--   this category will propably be the &#x201c;workhorse&#x201d; for most serious
--   calculus applications, because it contains all the usual trig etc. functions
--   and of course everything algebraic you can do in the reals.
-- 
--   The easiest way to define ordinary functions in this category is hence
--   with its 'AgentVal'ues, which have instances of the standard classes 'Num'
--   through 'Floating'. For instance, the following defines the /binary entropy/
--   as a differentiable function on the interval @]0,1[@: (it will
--   actually /know/ where it's defined and where not! &#x2013; and I don't mean you
--   need to exhaustively 'isNaN'-check all results...)
-- 
-- @
-- hb :: RWDiffable &#x211d; &#x211d; &#x211d;
-- hb = alg (\\p -> - p * logBase 2 p - (1-p) * logBase 2 (1-p) )
-- @
newtype RWDiffable s d c
   = RWDiffable {
        tryDfblDomain :: d -> (PreRegion s d, Option (Differentiable s d c)) }

notDefinedHere :: Option (Differentiable s d c)
notDefinedHere = Option Nothing



instance (RealDimension s) => Category (RWDiffable s) where
  type Object (RWDiffable s) o = LocallyScalable s o
  id = RWDiffable $ \x -> (GlobalRegion, pure id)
  RWDiffable f . RWDiffable g = RWDiffable h
   where h x₀ = case g x₀ of
                 (GlobalRegion, Option (Just gr))
                  -> let (y₀,_,_) = runDifferentiable gr x₀
                     in case f y₀ of
                         (GlobalRegion, Option Nothing)
                               -> (GlobalRegion, notDefinedHere)
                         (GlobalRegion, Option (Just fr))
                               -> (GlobalRegion, pure (fr . gr))
                         (r, Option Nothing) | PreRegion ry <- genericisePreRegion r
                               -> ( PreRegion $ ry . gr, notDefinedHere )
                         (r, Option (Just fr)) | PreRegion ry <- genericisePreRegion r
                               -> ( PreRegion $ ry . gr, pure (fr . gr) )
                 (rg@(RealSubray dir xl), Option (Just gr))
                  -> let (y₀,_,_) = runDifferentiable gr x₀
                     in case f y₀ of
                         (GlobalRegion, Option Nothing)
                               -> (rg, notDefinedHere)
                         (GlobalRegion, Option (Just fr))
                               -> (rg, pure (fr . gr))
                         (rf, Option Nothing)
                           | PreRegion rx <- genericisePreRegion rg
                           , PreRegion ry <- genericisePreRegion rf
                               -> ( PreRegion $ minDblfuncs (ry . gr) rx
                                  , notDefinedHere )
                         (rf, Option (Just fr))
                           | PreRegion rx <- genericisePreRegion rg
                           , PreRegion ry <- genericisePreRegion rf
                               -> ( PreRegion $ minDblfuncs (ry . gr) rx
                                  , pure (fr . gr) )
                 (PreRegion rx, Option (Just gr))
                  -> let (y₀,_,_) = runDifferentiable gr x₀
                     in case f y₀ of
                         (GlobalRegion, Option Nothing)
                               -> (PreRegion rx, notDefinedHere)
                         (GlobalRegion, Option (Just fr))
                               -> (PreRegion rx, pure (fr . gr))
                         (r, Option Nothing) | PreRegion ry <- genericisePreRegion r
                               -> ( PreRegion $ minDblfuncs (ry . gr) rx
                                  , notDefinedHere )
                         (r, Option (Just fr)) | PreRegion ry <- genericisePreRegion r
                               -> ( PreRegion $ minDblfuncs (ry . gr) rx
                                  , pure (fr . gr) )
                 (r, Option Nothing)
                  -> (r, notDefinedHere)


globalDiffable' :: Differentiable s a b -> RWDiffable s a b
globalDiffable' f = RWDiffable $ const (GlobalRegion, pure f)

pwDiffable :: PWDiffable s a b -> RWDiffable s a b
pwDiffable (PWDiffable q) = RWDiffable $ \x₀ -> let (r₀,f₀) = q x₀ in (r₀, pure f₀)



instance (RealDimension s) => EnhancedCat (RWDiffable s) (Differentiable s) where
  arr = globalDiffable'
instance (RealDimension s) => EnhancedCat (RWDiffable s) (PWDiffable s) where
  arr = pwDiffable
                
instance (RealDimension s) => Cartesian (RWDiffable s) where
  type UnitObject (RWDiffable s) = ZeroDim s
  swap = globalDiffable' swap
  attachUnit = globalDiffable' attachUnit
  detachUnit = globalDiffable' detachUnit
  regroup = globalDiffable' regroup
  regroup' = globalDiffable' regroup'
  
instance (RealDimension s) => Morphism (RWDiffable s) where
  RWDiffable f *** RWDiffable g = RWDiffable h
   where h (x,y) = (preRegionProd rfx rgy, liftA2 (***) dff dfg)
          where (rfx, dff) = f x
                (rgy, dfg) = g y

instance (RealDimension s) => PreArrow (RWDiffable s) where
  RWDiffable f &&& RWDiffable g = RWDiffable h
   where h x = (unsafePreRegionIntersect rfx rgx, liftA2 (&&&) dff dfg)
          where (rfx, dff) = f x
                (rgx, dfg) = g x
  terminal = globalDiffable' terminal
  fst = globalDiffable' fst
  snd = globalDiffable' snd


instance (RealDimension s) => WellPointed (RWDiffable s) where
  unit = Tagged Origin
  globalElement x = RWDiffable $ \Origin -> (GlobalRegion, pure (globalElement x))
  const x = RWDiffable $ \_ -> (GlobalRegion, pure (const x))


data RWDfblFuncValue s d c where
  ConstRWDFV :: c -> RWDfblFuncValue s d c
  GenericRWDFV :: RWDiffable s d c -> RWDfblFuncValue s d c

genericiseRWDFV :: (RealDimension s, LocallyScalable s c, LocallyScalable s d)
                    => RWDfblFuncValue s d c -> RWDfblFuncValue s d c
genericiseRWDFV (ConstRWDFV c) = GenericRWDFV $ const c
genericiseRWDFV v = v

instance RealDimension s => HasAgent (RWDiffable s) where
  type AgentVal (RWDiffable s) d c = RWDfblFuncValue s d c
  alg fq = case fq (GenericRWDFV id) of
    GenericRWDFV f -> f
  ($~) = postCompRW
instance RealDimension s => CartesianAgent (RWDiffable s) where
  alg1to2 fgq = case fgq (GenericRWDFV id) of
    (GenericRWDFV f, GenericRWDFV g) -> f &&& g
  alg2to1 fq = case fq (GenericRWDFV fst) (GenericRWDFV snd) of
    GenericRWDFV f -> f
  alg2to2 fgq = case fgq (GenericRWDFV fst) (GenericRWDFV snd) of
    (GenericRWDFV f, GenericRWDFV g) -> f &&& g
instance (RealDimension s)
      => PointAgent (RWDfblFuncValue s) (RWDiffable s) a x where
  point = ConstRWDFV

grwDfblFnValsFunc
     :: ( RealDimension s
        , LocallyScalable s c, LocallyScalable s c', LocallyScalable s d
        , v ~ Needle c, v' ~ Needle c'
        , ε ~ HerMetric v, ε ~ HerMetric v' )
             => (c' -> (c, v':-*v, ε->ε)) -> RWDfblFuncValue s d c' -> RWDfblFuncValue s d c
grwDfblFnValsFunc f = (RWDiffable (\_ -> (GlobalRegion, pure (Differentiable f))) $~)

grwDfblFnValsCombine :: forall d c c' c'' v v' v'' ε ε' ε'' s. 
         ( LocallyScalable s c,  LocallyScalable s c',  LocallyScalable s c''
         , LocallyScalable s d, RealDimension s
         , v ~ Needle c, v' ~ Needle c', v'' ~ Needle c''
         , ε ~ HerMetric v  , ε' ~ HerMetric v'  , ε'' ~ HerMetric v'', ε~ε', ε~ε''  )
       => (  c' -> c'' -> (c, (v',v''):-*v, ε -> (ε',ε''))  )
         -> RWDfblFuncValue s d c' -> RWDfblFuncValue s d c'' -> RWDfblFuncValue s d c
grwDfblFnValsCombine cmb (GenericRWDFV (RWDiffable fpcs))
                         (GenericRWDFV (RWDiffable gpcs)) 
    = GenericRWDFV . RWDiffable $
        \d₀ -> let (rc', fmay) = fpcs d₀
                   (rc'',gmay) = gpcs d₀
               in (unsafePreRegionIntersect rc' rc'',) $
                    case (fmay,gmay) of
                      (Option(Just(Differentiable f)), Option(Just(Differentiable g))) ->
                        pure . Differentiable $ \d
                         -> let (c', f', devf) = f d
                                (c'',g', devg) = g d
                                (c, h', devh) = cmb c' c''
                                h'l = h' *.* lcofst; h'r = h' *.* lcosnd
                            in ( c
                               , h' *.* linear (lapply f' &&& lapply g')
                               , \εc -> let εc' = transformMetric h'l εc
                                            εc'' = transformMetric h'r εc
                                            (δc',δc'') = devh εc 
                                        in devf εc' ^+^ devg εc''
                                             ^+^ transformMetric f' δc'
                                             ^+^ transformMetric g' δc''
                               )
                      _ -> notDefinedHere
 where lcofst = linear(,zeroV)
       lcosnd = linear(zeroV,) 
grwDfblFnValsCombine cmb fv gv
        = grwDfblFnValsCombine cmb (genericiseRWDFV fv) (genericiseRWDFV gv)


postCompRW :: ( RealDimension s
              , LocallyScalable s a, LocallyScalable s b, LocallyScalable s c )
              => RWDiffable s b c -> RWDfblFuncValue s a b -> RWDfblFuncValue s a c
postCompRW (RWDiffable f) (ConstRWDFV x) = case f x of
     (_, Option (Just fd)) -> ConstRWDFV $ fd $ x
postCompRW f (GenericRWDFV g) = GenericRWDFV $ f . g


instance ( WithField s EuclidSpace v, AdditiveGroup v, v ~ Needle (Interior (Needle v))
         , LocallyScalable s a, RealDimension s)
    => AdditiveGroup (RWDfblFuncValue s a v) where
  zeroV = point zeroV
  ConstRWDFV c₁ ^+^ ConstRWDFV c₂ = ConstRWDFV (c₁^+^c₂)
  ConstRWDFV c₁ ^+^ GenericRWDFV g = GenericRWDFV $
                               globalDiffable' (actuallyAffine c₁ idL) . g
  GenericRWDFV f ^+^ ConstRWDFV c₂ = GenericRWDFV $
                                  globalDiffable' (actuallyAffine c₂ idL) . f
  v^+^w = grwDfblFnValsCombine (\a b -> (a^+^b, lPlus, const zeroV)) v w
      where lPlus = linear $ uncurry (^+^)
  negateV (ConstRWDFV c) = ConstRWDFV (negateV c)
  negateV v = grwDfblFnValsFunc (\a -> (negateV a, lNegate, const zeroV)) v
      where lNegate = linear negateV

instance (RealDimension n, LocallyScalable n a)
            => Num (RWDfblFuncValue n a n) where
  fromInteger i = point $ fromInteger i
  (+) = (^+^)
  ConstRWDFV c₁ * ConstRWDFV c₂ = ConstRWDFV (c₁*c₂)
  ConstRWDFV c₁ * GenericRWDFV g = GenericRWDFV $
                               globalDiffable' (actuallyLinear $ linear (c₁*)) . g
  GenericRWDFV f * ConstRWDFV c₂ = GenericRWDFV $
                                  globalDiffable' (actuallyLinear $ linear (*c₂)) . f
  v*w = grwDfblFnValsCombine (
          \a b -> ( a*b
                  , linear $ \(da,db) -> a*db + b*da
                  , \d -> let d¹₂ = sqrt d in (d¹₂,d¹₂)
                  )
         ) v w
  negate = negateV
  abs = (RWDiffable absPW $~)
   where absPW a₀
          | a₀<0       = (negativePreRegion, pure desc)
          | otherwise  = (positivePreRegion, pure asc)
         desc = actuallyLinear $ linear negate
         asc = actuallyLinear idL
  signum = (RWDiffable sgnPW $~)
   where sgnPW a₀
          | a₀<0       = (negativePreRegion, pure (const $ -1))
          | otherwise  = (positivePreRegion, pure (const 1))

instance (RealDimension n, LocallyScalable n a)
            => Fractional (RWDfblFuncValue n a n) where
  fromRational i = point $ fromRational i
  recip = postCompRW . RWDiffable $ \a₀ -> if a₀<0
                                    then (negativePreRegion, pure (Differentiable negp))
                                    else (positivePreRegion, pure (Differentiable posp))
   where negp x = (x'¹, (- x'¹^2) *^ idL, unsafe_dev_ε_δ("1/"++show x) δ)
                 -- ε = 1/x − δ/x² − 1/(x+δ)
                 -- ε·x + ε·δ = 1 + δ/x − δ/x − δ²/x² − 1
                 --           = -δ²/x²
                 -- 0 = δ² + ε·x²·δ + ε·x³
                 -- δ = let mph = -ε·x²/2 in mph + sqrt (mph² − ε·x³)
          where δ ε = let mph = -ε*x^2/2
                          δ₀ = mph + sqrt (mph^2 - ε*x^3)
                      in if δ₀ > 0
                           then δ₀
                           else - x -- numerical underflow of εx³ vs mph
                                    --  ≡ ε*x^3 / (2*mph) (Taylor-expansion of the root)
                x'¹ = recip x
         posp x = (x'¹, (- x'¹^2) *^ idL, unsafe_dev_ε_δ("1/"++show x) δ)
          where δ ε = let mph = ε*x^2/2
                          δ₀ = sqrt (mph^2 + ε*x^3) - mph
                      in if δ₀>0 then δ₀ else x
                x'¹ = recip x





instance (RealDimension n, LocallyScalable n a)
            => Floating (RWDfblFuncValue n a n) where
  pi = point pi
  
  exp = grwDfblFnValsFunc
    $ \x -> let ex = exp x
            in if ex==0  -- numeric underflow
                then ( 0, zeroV, unsafe_dev_ε_δ("exp "++show x) $ \ε -> log ε - x )
                else ( ex, ex *^ idL, unsafe_dev_ε_δ("exp "++show x) $ \ε -> acosh(ε/(2*ex) + 1) )
                 -- ε = e^(x+δ) − eˣ − eˣ·δ 
                 --   = eˣ·(e^δ − 1 − δ) 
                 --   ≤ eˣ · (e^δ − 1 + e^(-δ) − 1)
                 --   = eˣ · 2·(cosh(δ) − 1)
                 -- cosh(δ) ≥ ε/(2·eˣ) + 1
                 -- δ ≥ acosh(ε/(2·eˣ) + 1)
  log = postCompRW . RWDiffable $ \x -> if x>0
                                  then (positivePreRegion, pure (Differentiable lnPosR))
                                  else (negativePreRegion, notDefinedHere)
   where lnPosR x = ( log x, recip x *^ idL, unsafe_dev_ε_δ("log "++show x) $ \ε -> x * sqrt(1 - exp(-ε)) )
                 -- ε = ln x + (-δ)/x − ln(x−δ)
                 --   = ln (x / ((x−δ) · exp(δ/x)))
                 -- x/e^ε = (x−δ) · exp(δ/x)
                 -- let γ = δ/x ∈ [0,1[
                 -- exp(-ε) = (1−γ) · e^γ
                 --         ≥ (1−γ) · (1+γ)
                 --         = 1 − γ²
                 -- γ ≥ sqrt(1 − exp(-ε)) 
                 -- δ ≥ x · sqrt(1 − exp(-ε)) 
                    
  sqrt = postCompRW . RWDiffable $ \x -> if x>0
                                   then (positivePreRegion, pure (Differentiable sqrtPosR))
                                   else (negativePreRegion, notDefinedHere)
   where sqrtPosR x = ( sx, idL ^/ (2*sx), unsafe_dev_ε_δ("sqrt "++show x) $
                          \ε -> 2 * (s2 * sqrt sx^3 * sqrt ε + signum (ε*2-sx) * sx * ε) )
          where sx = sqrt x; s2 = sqrt 2
                 -- Exact inverse of O(δ²) remainder.
  
  sin = grwDfblFnValsFunc sinDfb
   where sinDfb x = ( sx, cx *^ idL, unsafe_dev_ε_δ("sin "++show x) δ )
          where sx = sin x; cx = cos x
                sx² = sx^2; cx² = cx^2
                sx' = abs sx; cx' = abs cx
                sx'³ = sx'*sx²; cx⁴ = cx²*cx²
                δ ε = (ε*(1.8 + ε^2/(cx' + (2+40*cx⁴)/ε)) + σ₃³*sx'³)**(1/3) - σ₃*sx'
                        + σ₂*sqrt ε/(σ₂+cx²)
                    -- Carefully fine-tuned to give everywhere a good and safe bound.
                    -- The third root makes it pretty slow too, but since tight
                    -- deviation bounds can dramatically reduce the number of evaluations
                    -- needed in the first place, this is probably worthwhile.
                σ₂ = 1.4; σ₃ = 1.75; σ₃³ = σ₃^3
                    -- Safety margins for overlap between quadratic and cubic model
                    -- (these aren't naturally compatible to be used both together)
                      
  cos = sin . (globalDiffable' (actuallyAffine (pi/2) idL) $~)
  
  sinh x = (exp x - exp (-x))/2
    {- = grwDfblFnValsFunc sinhDfb
   where sinhDfb x = ( sx, cx *^ idL, unsafe_dev_ε_δ δ )
          where sx = sinh x; cx = cosh x
                δ ε = undefined -}
                 -- ε = sinh x + δ · cosh x − sinh(x+δ)
                 --   = ½ · ( eˣ − e⁻ˣ + δ · (eˣ + e⁻ˣ) − exp(x+δ) + exp(-x−δ) )
                 --                  = ½·e⁻ˣ · ( e²ˣ − 1 + δ · (e²ˣ + 1) − e²ˣ·e^δ + e^-δ )
                 --   = ½ · ( eˣ − e⁻ˣ + δ · (eˣ + e⁻ˣ) − exp(x+δ) + exp(-x−δ) )
  cosh x = (exp x + exp (-x))/2
  
  tanh = grwDfblFnValsFunc tanhDfb
   where tanhDfb x = ( tnhx, idL ^/ (cosh x^2), unsafe_dev_ε_δ("tan "++show x) δ )
          where tnhx = tanh x
                c = (tnhx*2/pi)^2
                p = 1 + abs x/(2*pi)
                δ ε = p * (sqrt ε + ε * c)
                  -- copied from 'atan' definition. Empirically works safely, in fact
                  -- with quite a big margin. TODO: find a tighter definition.

  atan = grwDfblFnValsFunc atanDfb
   where atanDfb x = ( atnx, idL ^/ (1+x^2), unsafe_dev_ε_δ("atan "++show x) δ )
          where atnx = atan x
                c = (atnx*2/pi)^2
                p = 1 + abs x/(2*pi)
                δ ε = p * (sqrt ε + ε * c)
                 -- Semi-empirically obtained: with the epsEst helper,
                 -- it is observed that this function is (for xc≥0) a lower bound
                 -- to the arctangent. The growth of the p coefficient makes sense
                 -- and holds for arbitrarily large xc, because those move us linearly
                 -- away from the only place where the function is not virtually constant
                 -- (around 0).
   
  asin = postCompRW . RWDiffable $ \x -> if
                  | x < (-1)   -> (preRegionFromMinInfTo (-1), notDefinedHere)  
                  | x > 1      -> (preRegionToInfFrom 1, notDefinedHere)
                  | otherwise  -> (intervalPreRegion (-1,1), pure (Differentiable asinDefdR))
   where asinDefdR x = ( asinx, asin'x *^ idL, unsafe_dev_ε_δ("asin "++show x) δ )
          where asinx = asin x; asin'x = recip (sqrt $ 1 - x^2)
                c = 1 - x^2 
                δ ε = sqrt ε * c
                 -- Empirical, with epsEst upper bound.

  acos = postCompRW . RWDiffable $ \x -> if
                  | x < (-1)   -> (preRegionFromMinInfTo (-1), notDefinedHere)  
                  | x > 1      -> (preRegionToInfFrom 1, notDefinedHere)
                  | otherwise  -> (intervalPreRegion (-1,1), pure (Differentiable acosDefdR))
   where acosDefdR x = ( acosx, acos'x *^ idL, unsafe_dev_ε_δ("acos "++show x) δ )
          where acosx = acos x; acos'x = - recip (sqrt $ 1 - x^2)
                c = 1 - x^2
                δ ε = sqrt ε * c -- Like for asin – it's just a translation/reflection.

  asinh = grwDfblFnValsFunc asinhDfb
   where asinhDfb x = ( asinhx, idL ^/ sqrt(1+x^2), unsafe_dev_ε_δ("asinh "++show x) δ )
          where asinhx = asinh x
                δ ε = abs x * sqrt((1 - exp(-ε))*0.8 + ε^2/(3*abs x)) + sqrt(ε/(abs x+0.5))
                 -- Empirical, modified from log function (the area hyperbolic sine
                 -- resembles two logarithmic lobes), with epsEst-checked lower bound.
  
  acosh = postCompRW . RWDiffable $ \x -> if x>0
                                   then (positivePreRegion, pure (Differentiable acoshDfb))
                                   else (negativePreRegion, notDefinedHere)
   where acoshDfb x = ( acosh x, idL ^/ sqrt(x^2 - 2), unsafe_dev_ε_δ("acosh "++show x) δ )
          where δ ε = (2 - 1/sqrt x) * (s2 * sqrt sx^3 * sqrt(ε/s2) + signum (ε*s2-sx) * sx * ε/s2) 
                sx = sqrt(x-1)
                s2 = sqrt 2
                 -- Empirical, modified from sqrt function – the area hyperbolic cosine
                 -- strongly resembles \x -> sqrt(2 · (x-1)).
                    
  atanh = postCompRW . RWDiffable $ \x -> if
                  | x < (-1)   -> (preRegionFromMinInfTo (-1), notDefinedHere)  
                  | x > 1      -> (preRegionToInfFrom 1, notDefinedHere)
                  | otherwise  -> (intervalPreRegion (-1,1), pure (Differentiable atnhDefdR))
   where atnhDefdR x = ( atanh x, recip(1-x^2) *^ idL, unsafe_dev_ε_δ("atanh "++show x) $ \ε -> sqrt(tanh ε)*(1-abs x) )
                 -- Empirical, with epsEst upper bound.
  



-- $definitionRegionOps
-- Because the agents of 'RWDiffable' aren't really values in /Hask/, you can't use
-- the standard comparison operators on them, nor the built-in syntax of guards
-- or if-statements.
-- 
-- However, because this category allows functions to be undefined in some region,
-- such decisions can be faked quite well: '?->' restricts a function to
-- some region, by simply marking it undefined outside¹, and '?|:' replaces these
-- regions with values from another function.
-- 
-- Example: define a function that is compactly supported on the interval ]-1,1[,
-- i.e. exactly zero everywhere outside.
--
-- @
-- Graphics.Dynamic.Plot.R2> plotWindow [diffableFnPlot (\\x -> -1 '?<' x '?<' 1 '?->' exp(1/(x^2 - 1)) '?|:' 0)]
-- @
-- 
-- <<images/examples/Friedrichs-mollifier.png>>
-- 
-- ¹ Note that it may not be necessary to restrict explicitly: for instance if a
-- square root appears somewhere in an expression, then the expression is automatically
-- restricted so that the root has a positive argument!
  
infixl 4 ?->
-- | Require the LHS to be defined before considering the RHS as result.
--   This works analogously to the standard `Control.Applicative.Applicative` method
-- 
--   @
--   ('Control.Applicative.*>') :: Maybe a -> Maybe b -> Maybe b
--   Just _ 'Control.Applicative.*>' a = a
--   _      'Control.Applicative.*>' a = Nothing
--   @
(?->) :: (RealDimension n, LocallyScalable n a, LocallyScalable n b, LocallyScalable n c)
      => RWDfblFuncValue n c a -> RWDfblFuncValue n c b -> RWDfblFuncValue n c b
ConstRWDFV _ ?-> f = f
GenericRWDFV (RWDiffable r) ?-> ConstRWDFV c = GenericRWDFV (RWDiffable s)
 where s x₀ = case r x₀ of
                (rd, Option (Just q)) -> (rd, return $ const c)
                (rd, Option Nothing) -> (rd, empty)
GenericRWDFV (RWDiffable f) ?-> GenericRWDFV (RWDiffable g) = GenericRWDFV (RWDiffable h)
 where h x₀ = case f x₀ of
                (rf, Option (Just _)) | (rg, q) <- g x₀
                        -> (unsafePreRegionIntersect rf rg, q)
                (rf, Option Nothing) -> (rf, empty)

positiveRegionalId :: RealDimension n => RWDiffable n n n
positiveRegionalId = RWDiffable $ \x₀ ->
       if x₀ > 0 then (positivePreRegion, pure id)
                 else (negativePreRegion, notDefinedHere)

infixl 5 ?> , ?<
-- | Return the RHS, if it is less than the LHS.
--   (Really the purpose is just to compare the values, but returning one of them
--   allows chaining of comparison operators like in Python.)
--   Note that less-than comparison is <http://www.paultaylor.eu/ASD/ equivalent>
--   to less-or-equal comparison, because there is no such thing as equality.
(?>) :: (RealDimension n, LocallyScalable n a)
           => RWDfblFuncValue n a n -> RWDfblFuncValue n a n -> RWDfblFuncValue n a n
a ?> b = (positiveRegionalId $~ a-b) ?-> b

-- | Return the RHS, if it is greater than the LHS.
(?<) :: (RealDimension n, LocallyScalable n a)
           => RWDfblFuncValue n a n -> RWDfblFuncValue n a n -> RWDfblFuncValue n a n
a ?< b = (positiveRegionalId $~ b-a) ?-> b

infixl 3 ?|:
-- | Try the LHS, if it is undefined use the RHS. This works analogously to
--   the standard `Control.Applicative.Alternative` method
-- 
--   @
--   ('Control.Applicative.<|>') :: Maybe a -> Maybe a -> Maybe a
--   Just x 'Control.Applicative.<|>' _ = Just x
--   _      'Control.Applicative.<|>' a = a
--   @
-- 
--  Basically a weaker and agent-ised version of 'backupRegions'.
(?|:) :: (RealDimension n, LocallyScalable n a, LocallyScalable n b)
      => RWDfblFuncValue n a b -> RWDfblFuncValue n a b -> RWDfblFuncValue n a b
ConstRWDFV c ?|: _ = ConstRWDFV c
GenericRWDFV (RWDiffable f) ?|: ConstRWDFV c = GenericRWDFV (RWDiffable h)
 where h x₀ = case f x₀ of
                (rd, Option (Just q)) -> (rd, Option (Just q))
                (rd, Option Nothing) -> (rd, Option . Just $ const c)
GenericRWDFV (RWDiffable f) ?|: GenericRWDFV (RWDiffable g) = GenericRWDFV (RWDiffable h)
 where h x₀ = case f x₀ of
                (rf, Option (Just q)) -> (rf, pure q)
                (rf, Option Nothing) | (rg, q) <- g x₀
                        -> (unsafePreRegionIntersect rf rg, q)

-- | Replace the regions in which the first function is undefined with values
--   from the second function.
backupRegions :: (RealDimension n, LocallyScalable n a, LocallyScalable n b)
      => RWDiffable n a b -> PWDiffable n a b -> PWDiffable n a b
backupRegions (RWDiffable f) (PWDiffable g) = PWDiffable h
 where h x₀ = case f x₀ of
                (rf, Option (Just q)) -> (rf, q)
                (rf, Option Nothing) | (rg, q) <- g x₀
                        -> (unsafePreRegionIntersect rf rg, q)




isZeroMap :: ∀ v a . (FiniteDimensional v, AdditiveGroup a, Eq a) => (v:-*a) -> Bool
isZeroMap m = all ((==zeroV) . atBasis m) b
 where (Tagged b) = completeBasis :: Tagged v [Basis v]



