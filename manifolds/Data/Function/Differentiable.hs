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
            -- * Regions within a manifold
              Region
            , smoothIndicator
            -- * Hierarchy of manifold-categories
            -- ** Everywhere differentiable functions
            , Differentiable
            -- ** Almost everywhere diff'able funcs
            , PWDiffable
            -- ** Region-wise defined diff'able funcs
            , RWDiffable
            -- * Misc
            , discretisePathIn
            , discretisePathSegs
            , continuousIntervals
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






discretisePathIn :: WithField ℝ Manifold x
      => Int                    -- ^ Limit the number of steps taken in either direction. Note this will not cap the resolution but /length/ of the discretised path.
      -> (ℝ, ℝ)                 -- ^ Parameter interval of interest.
      -> RieMetric x            -- ^ Inaccuracy allowance /ε/.
      -> (Differentiable ℝ ℝ x) -- ^ Path specification.
      -> [(ℝ,x)]                -- ^ Trail of points along the path, such that a linear interpolation deviates nowhere by more as /ε/.
discretisePathIn nLim (xl, xr) m (Differentiable f)
         = reverse (tail . take nLim $ traceFwd xl xm (-1))
          ++ take nLim (traceFwd xr xm 1)
 where traceFwd xlim x₀ dir
         | signum (x₀-xlim) == signum dir = [(xlim, fxlim)]
         | otherwise                      = (x₀, fx₀) : traceFwd xlim (x₀+xstep) dir
        where (fx₀, _, δx²) = f x₀
              εx = m fx₀
              χ = metric (δx² εx) 1
              xstep = dir * min (abs x₀+1) (recip χ)
              (fxlim, _, _) = f xlim
       xm = (xr - xl) / 2
                      
data ℝInterval = Allℝ | NegTo ℝ | ToPos ℝ | Intv ℝ ℝ deriving (Show)

-- ^ Doesn't work at the moment.
continuityRanges :: WithField ℝ Manifold x
      => RieMetric ℝ       -- ^ Needed resolution of boundaries
      -> RWDiffable ℝ ℝ x
      -> ([ℝInterval], [ℝInterval])
continuityRanges δbf (RWDiffable f)
  | (GlobalRegion, _) <- f 0
                 = ([], [Allℝ])
  | otherwise    = glueMid (go 0 (-1)) (go 0 1)
 where go x₀ dir = exit dir x₀
        where (PreRegion (Differentiable r₀), fq₀) = f x₀
              exit dir' xq
                | xq > hugeℝVal     = [ToPos x₀]
                | xq < -hugeℝVal    = [NegTo x₀]
                | yq==0             = exit dir' (xq + 1/sqrt(resoHere dir))
                | yq'>0             = exit dir' xq'
                | resoHere stepp<1  = Intv (min xq xq') (max xq xq') : go xq' dir
                | otherwise         = exit (dir'/2) xq
               where (yq, jq, δyq) = r₀ xq
                     xq' = xq + stepp
                     yq' = yq + lapply jq stepp
                     stepp = dir' * as_devεδ δyq yq -- TODO: memoise in `exit` recursion
                     resoHere = metricSq $ δbf xq
       glueMid [NegTo le] [ToPos re]         | le==re  = ([], [Allℝ])
       glueMid [NegTo le] (Intv re r:rs)     | le==re  = ([], NegTo r:rs)
       glueMid (Intv l le:ls) [ToPos re]     | le==re  = (ls, [ToPos l])
       glueMid (Intv l le:ls) (Intv re r:rs) | le==re  = (ls, Intv l r:rs)
       glueMid l r = (l,r)

-- ^ Doesn't work at the moment.
discretisePathSegs :: WithField ℝ Manifold x
      => Int              -- ^ Maximum number of path segments and/or points per segment.
      -> ( RieMetric x
         , RieMetric ℝ )  -- ^ Inaccuracy allowance /ε/ for results in the target space, and /δ/ for arguments (only relevant for resolution of discontinuity boundaries).
      -> RWDiffable ℝ ℝ x -- ^ Path specification.
      -> ([[(ℝ,x)]], [[(ℝ,x)]]) -- ^ Discretised paths; continuous segments in either direction
discretisePathSegs = undefined
              
             
continuousIntervals :: RWDiffable ℝ ℝ x -> (ℝ,ℝ) -> [(ℝ,ℝ)]
continuousIntervals (RWDiffable f) (xl,xr) = enter xl
 where enter x₀ = case f x₀ of 
                    (GlobalRegion, _) -> [(xl,xr)]
                    (PreRegion r₀, _) -> exit r₀ x₀
        where exit :: Differentiable ℝ ℝ ℝ -> ℝ -> [(ℝ,ℝ)]
              exit (Differentiable r) x
               | x > xr           = [(x₀,xr)]
               | y' > 0          = exit (Differentiable r)
                                        (x + metricAsLength (δ (metricFromLength y)))
               | -y/y' < 1e-10   = (x₀,x) : enter (x + min 1e-100 (abs x * 1e-8))
               | otherwise       = exit (Differentiable r) xn
               where (y, y'm, δ) = r x
                     xn = bisBack $ x - y/y'
                      where bisBack xq
                              | ybm > 0    = xbm
                              | otherwise  = bisBack xbm
                             where (ybm, _, _) = r xbm
                                   xbm = (xq*9 + x)/10
                     y' = lapply y'm 1
              
analyseLocalBehaviour ::
    RWDiffable ℝ ℝ ℝ
 -> ℝ                      -- ^ /x/₀ value.
 -> Option ( (ℝ,ℝ)
           , ℝ->Option ℝ ) -- ^ /f/ /x/₀, derivative (i.e. Taylor-1-coefficient),
                           --   and reverse propagation of /O/ (/δ/²) bound.
analyseLocalBehaviour (RWDiffable f) x₀ = case f x₀ of
       (_, Option Nothing) -> empty
       (_, Option (Just (Differentiable fd))) -> return $
              let (fx, j, δf) = fd x₀
                  epsprop ε
                    | ε>0  = case metric (δf $ metricFromLength ε) 1 of
                               0  -> empty
                               δ' -> return $ recip δ'
                    | otherwise  = pure 0
              in ((fx, lapply j 1), epsprop)

-- | Represent a 'Region' by a smooth function which is positive within the region,
--   and crosses zero at the boundary.
smoothIndicator :: LocallyScalable ℝ q => Region ℝ q -> Differentiable ℝ q ℝ
smoothIndicator (Region _ GlobalRegion) = const 1
smoothIndicator (Region _ (PreRegion r)) = r

regionOfContinuityAround :: RWDiffable ℝ q x -> q -> Region ℝ q
regionOfContinuityAround (RWDiffable f) q = Region q . fst . f $ q
              


hugeℝVal :: ℝ
hugeℝVal = 1e+100






type LinDevPropag d c = Metric c -> Metric d

dev_ε_δ :: RealDimension a
                => (a -> a) -> LinDevPropag a a
dev_ε_δ f d = let ε'² = metricSq d 1
              in if ε'²>0
                  then let δ = f . sqrt $ recip ε'²
                       in if δ > 0
                           then projector $ recip δ
                           else error "ε-δ propagator function gives negative results."
                  else zeroV

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
          | a>0        = (a, idL, dev_ε_δ $ \ε -> a + ε/2) 
          | a<0        = (-a, negateV idL, dev_ε_δ $ \ε -> ε/2 - a)
          | otherwise  = (0, zeroV, (^/ sqrt 2))
  signum = dfblFnValsFunc dfblSgn
   where dfblSgn a
          | a>0        = (1, zeroV, dev_ε_δ $ const a)
          | a<0        = (-1, zeroV, dev_ε_δ $ \_ -> -a)
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
         | fx==gx   = ( fx, (f'^+^g')^/2
                      , \d -> devf d ^+^ devg d
                               ^+^ transformMetric (f'^-^g')
                                                   (projector $ metric d 1) )
         | fx < gx   = ( fx, f'
                       , \d -> devf d
                               ^+^ transformMetric (f'^-^g')
                                                   (projector $ metric d 1 + gx - fx) )
        where (fx, f', devf) = f x
              (gx, g', devg) = g x


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
  PreRegion :: (Differentiable s m s) -- A function that is positive at reference point /p/,
                                      -- decreases and crosses zero at the region's
                                      -- boundaries. (If it goes positive again somewhere
                                      -- else, these areas shall /not/ be considered
                                      -- belonging to the (by definition connected) region.)
         -> PreRegion s m

-- | Set-intersection of regions would not be guaranteed to yield a connected result
--   or even have the reference point of one region contained in the other. This
--   combinator assumes (unchecked) that the references are in a connected
--   sub-intersection, which is used as the result.
unsafePreRegionIntersect :: (RealDimension s, LocallyScalable s a)
                  => PreRegion s a -> PreRegion s a -> PreRegion s a
unsafePreRegionIntersect GlobalRegion r = r
unsafePreRegionIntersect r GlobalRegion = r
unsafePreRegionIntersect (PreRegion ra) (PreRegion rb) = PreRegion $ minDblfuncs ra rb

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


positivePreRegion, negativePreRegion :: (RealDimension s) => PreRegion s s
positivePreRegion = PreRegion $ Differentiable prr
 where prr x = (1 - 1/xp1, (1/xp1²) *^ idL, dev_ε_δ δ )
                 -- ε = (1 − 1/(1+x)) + (-δ · 1/(x+1)²) − (1 − 1/(1+x−δ))
                 --   = 1/(1+x−δ) − 1/(1+x) − δ · 1/(x+1)²
                 -- ε·(1+x−δ) = 1 − (1+x−δ)/(1+x) − δ·(1+x-δ)/(x+1)²
                 -- ε·(1+x) − ε·δ = 1 − 1/(1+x) − x/(1+x) + δ/(1+x)
                 --                               − δ/(x+1)² − δ⋅x/(x+1)² + δ²/(x+1)²
                 --               = 1 − (1+x)/(1+x) + ((x+1) − 1)⋅δ/(x+1)²
                 --                               − δ⋅x/(x+1)² + δ²/(x+1)²
                 --               = 1 − 1 + x⋅δ/(x+1)² − δ⋅x/(x+1)² + δ²/(x+1)²
                 --               = δ²/(x+1)²
                 -- ε·(x+1)⋅(x+1)² − ε·δ⋅(x+1)² = δ²
                 -- 0 = δ² + ε·(x+1)²·δ − ε·(x+1)³
                 -- δ = let mph = -ε·(x+1)²/2
                 --     in mph + sqrt(mph² + ε·(x+1)³)
        where δ ε = let mph = -ε*xp1²/2
                    in mph + sqrt(mph^2 + ε * xp1² * xp1)
              xp1 = (x+1)
              xp1² = xp1 ^ 2
negativePreRegion = PreRegion $ ppr . ngt
 where PreRegion ppr = positivePreRegion
       ngt = actuallyLinear $ linear negate

preRegionToInfFrom, preRegionFromMinInfTo :: RealDimension s => s -> PreRegion s s
preRegionToInfFrom xs = PreRegion $ ppr . trl
 where PreRegion ppr = positivePreRegion
       trl = actuallyAffine (-xs) idL
preRegionFromMinInfTo xe = PreRegion $ ppr . flp
 where PreRegion ppr = positivePreRegion
       flp = actuallyAffine (-xe) (linear negate)

intervalPreRegion :: RealDimension s => (s,s) -> PreRegion s s
intervalPreRegion (lb,rb) = PreRegion $ Differentiable prr
 where m = lb + radius; radius = (rb - lb)/2
       prr x = ( 1 - ((x-m)/radius)^2
               , (2*(m-x)/radius^2) *^ idL
               , dev_ε_δ $ (*radius) . sqrt )




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
          | a₀<0       = (negativePreRegion, const 1)
          | otherwise  = (positivePreRegion, const $ -1)

instance (RealDimension n, LocallyScalable n a)
            => Fractional (PWDfblFuncValue n a n) where
  fromRational i = point $ fromRational i
  recip = postEndo . PWDiffable $ \a₀ -> if a₀<0
                                          then (negativePreRegion, Differentiable negp)
                                          else (positivePreRegion, Differentiable posp)
   where negp x = (x'¹, (- x'¹^2) *^ idL, dev_ε_δ δ)
                 -- ε = 1/x − δ/x² − 1/(x+δ)
                 -- ε·x + ε·δ = 1 + δ/x − δ/x − δ²/x² − 1
                 --           = -δ²/x²
                 -- 0 = δ² + ε·x²·δ + ε·x³
                 -- δ = let mph = -ε·x²/2 in mph + sqrt (mph² − ε·x³)
          where δ ε = let mph = -ε*x^2/2 in mph + sqrt (mph^2 - ε*x^3)
                x'¹ = recip x
         posp x = (x'¹, (- x'¹^2) *^ idL, dev_ε_δ δ)
          where δ ε = let mph = -ε*x^2/2 in mph + sqrt (mph^2 + ε*x^3)
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
                 (GlobalRegion, Option Nothing)
                  -> (GlobalRegion, notDefinedHere)
                 (GlobalRegion, Option (Just gr))
                  -> let (y₀,_,_) = runDifferentiable gr x₀
                     in case f y₀ of
                         (GlobalRegion, Option Nothing)
                               -> (GlobalRegion, notDefinedHere)
                         (GlobalRegion, Option (Just fr))
                               -> (GlobalRegion, pure (fr . gr))
                         (PreRegion ry, Option Nothing)
                               -> ( PreRegion $ ry . gr, Option Nothing )
                         (PreRegion ry, Option (Just fr))
                               -> ( PreRegion $ ry . gr, pure (fr . gr) )
                 (PreRegion rx, Option Nothing)
                  -> (PreRegion rx, notDefinedHere)
                 (PreRegion rx, Option (Just gr))
                  -> let (y₀,_,_) = runDifferentiable gr x₀
                     in case f y₀ of
                         (GlobalRegion, Option Nothing)
                               -> (PreRegion rx, notDefinedHere)
                         (GlobalRegion, Option (Just fr))
                               -> (PreRegion rx, pure (fr . gr))
                         (PreRegion ry, Option Nothing)
                               -> ( PreRegion $ minDblfuncs (ry . gr) rx
                                  , notDefinedHere )
                         (PreRegion ry, Option (Just fr))
                               -> ( PreRegion $ minDblfuncs (ry . gr) rx
                                  , pure (fr . gr) )
          where (rx, gr) = g x₀


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
          | a₀<0       = (negativePreRegion, pure (const 1))
          | otherwise  = (positivePreRegion, pure (const $ -1))

instance (RealDimension n, LocallyScalable n a)
            => Fractional (RWDfblFuncValue n a n) where
  fromRational i = point $ fromRational i
  recip = postCompRW . RWDiffable $ \a₀ -> if a₀<0
                                    then (negativePreRegion, pure (Differentiable negp))
                                    else (positivePreRegion, pure (Differentiable posp))
   where negp x = (x'¹, (- x'¹^2) *^ idL, dev_ε_δ δ)
                 -- ε = 1/x − δ/x² − 1/(x+δ)
                 -- ε·x + ε·δ = 1 + δ/x − δ/x − δ²/x² − 1
                 --           = -δ²/x²
                 -- 0 = δ² + ε·x²·δ + ε·x³
                 -- δ = let mph = -ε·x²/2 in mph + sqrt (mph² − ε·x³)
          where δ ε = let mph = -ε*x^2/2 in mph + sqrt (mph^2 - ε*x^3)
                x'¹ = recip x
         posp x = (x'¹, (- x'¹^2) *^ idL, dev_ε_δ δ)
          where δ ε = let mph = -ε*x^2/2 in mph + sqrt (mph^2 + ε*x^3)
                x'¹ = recip x





-- Helper for checking ε-estimations in GHCi with dynamic-plot:
-- epsEst (f,f') εsgn δf (ViewXCenter xc) (ViewHeight h)
--    = let δfxc = δf xc
--      in tracePlot $ reverse [ (xc - δ, f xc - δ * f' xc + εsgn*ε) |
--                               ε <- [0, h/500 .. h], let δ = δfxc ε]
--                          ++ [ (xc + δ, f xc + δ * f' xc + εsgn*ε) |
--                               ε <- [0, h/500 .. h], let δ = δfxc ε] 
-- Golfed version:
-- epsEst(f,d)s φ(ViewXCenter ξ)(ViewHeight h)=let ζ=φ ξ in tracePlot$[(ξ-δ,f ξ-δ*d ξ+s*abs ε)|ε<-[-h,-0.998*h..h],let δ=ζ(abs ε)*signum ε]

instance (RealDimension n, LocallyScalable n a)
            => Floating (RWDfblFuncValue n a n) where
  pi = point pi
  
  exp = grwDfblFnValsFunc
    $ \x -> let ex = exp x
            in if ex==0  -- numeric underflow
                then ( 0, zeroV, dev_ε_δ $ \ε -> log ε - x )
                else ( ex, ex *^ idL, dev_ε_δ $ \ε -> acosh(ε/(2*ex) + 1) )
                 -- ε = e^(x+δ) − eˣ − eˣ·δ 
                 --   = eˣ·(e^δ − 1 − δ) 
                 --   ≤ eˣ · (e^δ − 1 + e^(-δ) − 1)
                 --   = eˣ · 2·(cosh(δ) − 1)
                 -- cosh(δ) ≥ ε/(2·eˣ) + 1
                 -- δ ≥ acosh(ε/(2·eˣ) + 1)
  log = postCompRW . RWDiffable $ \x -> if x>0
                                  then (positivePreRegion, pure (Differentiable lnPosR))
                                  else (negativePreRegion, notDefinedHere)
   where lnPosR x = ( log x, recip x *^ idL, dev_ε_δ $ \ε -> x * sqrt(1 - exp(-ε)) )
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
   where sqrtPosR x = ( sx, idL ^/ (2*sx), dev_ε_δ $
                          \ε -> 2 * (s2 * sqrt sx^3 * sqrt ε + signum (ε*2-sx) * sx * ε) )
          where sx = sqrt x; s2 = sqrt 2
                 -- Exact inverse of O(δ²) remainder.
  
  sin = grwDfblFnValsFunc sinDfb
   where sinDfb x = ( sx, cx *^ idL, dev_ε_δ δ )
          where sx = sin x; cx = cos x
                δ ε = let δ₀ = sqrt $ 2 * ε / (abs sx + abs cx/3)
                      in if δ₀ < 1 -- TODO: confirm selection of δ-definition range.
                                   -- (Empirically seems to be ok)
                          then δ₀
                          else max 1 $ (ε - abs sx - 1) / abs cx
                 -- When sin x ≥ 0, cos x ≥ 0, δ ∈ [0,1[
                 -- ε = sin x + δ · cos x − sin(x+δ)
                 --   = sin x + δ · cos x − sin x · cos δ − cos x · sin δ
                 --   ≤ sin x + δ · cos x − sin x · (1−δ²/2) − cos x · (δ − δ³/6)
                 --   = sin x · δ²/2 + cos x · δ³/6
                 --   ≤ δ² · (sin x / 2 + cos x / 6)
                 -- δ ≥ sqrt(2 · ε / (sin x + cos x / 3))
                 -- For general δ≥0,
                 -- ε ≤ δ · cos x + sin x + 1
                 -- δ ≥ (ε − sin x − 1) / cos x
  cos = sin . (globalDiffable' (actuallyAffine (pi/2) idL) $~)
  
  sinh x = (exp x - exp (-x))/2
    {- = grwDfblFnValsFunc sinhDfb
   where sinhDfb x = ( sx, cx *^ idL, dev_ε_δ δ )
          where sx = sinh x; cx = cosh x
                δ ε = undefined -}
                 -- ε = sinh x + δ · cosh x − sinh(x+δ)
                 --   = ½ · ( eˣ − e⁻ˣ + δ · (eˣ + e⁻ˣ) − exp(x+δ) + exp(-x−δ) )
                 --                  = ½·e⁻ˣ · ( e²ˣ − 1 + δ · (e²ˣ + 1) − e²ˣ·e^δ + e^-δ )
                 --   = ½ · ( eˣ − e⁻ˣ + δ · (eˣ + e⁻ˣ) − exp(x+δ) + exp(-x−δ) )
  cosh x = (exp x + exp (-x))/2
  
  tanh = grwDfblFnValsFunc tanhDfb
   where tanhDfb x = ( tnhx, idL ^/ (cosh x^2), dev_ε_δ δ )
          where tnhx = tanh x
                c = (tnhx*2/pi)^2
                p = 1 + abs x/(2*pi)
                δ ε = p * (sqrt ε + ε * c)
                  -- copied from 'atan' definition. Empirically works safely, in fact
                  -- with quite a big margin. TODO: find a tighter definition.

  atan = grwDfblFnValsFunc atanDfb
   where atanDfb x = ( atnx, idL ^/ (1+x^2), dev_ε_δ δ )
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
   where asinDefdR x = ( asinx, asin'x *^ idL, dev_ε_δ δ )
          where asinx = asin x; asin'x = recip (sqrt $ 1 - x^2)
                c = 1 - x^2 
                δ ε = sqrt ε * c
                 -- Empirical, with epsEst upper bound.

  acos = postCompRW . RWDiffable $ \x -> if
                  | x < (-1)   -> (preRegionFromMinInfTo (-1), notDefinedHere)  
                  | x > 1      -> (preRegionToInfFrom 1, notDefinedHere)
                  | otherwise  -> (intervalPreRegion (-1,1), pure (Differentiable acosDefdR))
   where acosDefdR x = ( acosx, acos'x *^ idL, dev_ε_δ δ )
          where acosx = acos x; acos'x = - recip (sqrt $ 1 - x^2)
                c = 1 - x^2
                δ ε = sqrt ε * c -- Like for asin – it's just a translation/reflection.

  asinh = grwDfblFnValsFunc asinhDfb
   where asinhDfb x = ( asinhx, idL ^/ sqrt(1+x^2), dev_ε_δ δ )
          where asinhx = asinh x
                δ ε = abs x * sqrt((1 - exp(-ε))*0.8 + ε^2/(3*abs x)) + sqrt(ε/(abs x+0.5))
                 -- Empirical, modified from log function (the area hyperbolic sine
                 -- resembles two logarithmic lobes), with epsEst-checked lower bound.
  
  acosh = postCompRW . RWDiffable $ \x -> if x>0
                                   then (positivePreRegion, pure (Differentiable acoshDfb))
                                   else (negativePreRegion, notDefinedHere)
   where acoshDfb x = ( acosh x, idL ^/ sqrt(x^2 - 2), dev_ε_δ δ )
          where δ ε = (2 - 1/sqrt x) * (s2 * sqrt sx^3 * sqrt(ε/s2) + signum (ε*s2-sx) * sx * ε/s2) 
                sx = sqrt(x-1)
                s2 = sqrt 2
                 -- Empirical, modified from sqrt function – the area hyperbolic cosine
                 -- strongly resembles \x -> sqrt(2 · (x-1)).
                    
  atanh = postCompRW . RWDiffable $ \x -> if
                  | x < (-1)   -> (preRegionFromMinInfTo (-1), notDefinedHere)  
                  | x > 1      -> (preRegionToInfFrom 1, notDefinedHere)
                  | otherwise  -> (intervalPreRegion (-1,1), pure (Differentiable atnhDefdR))
   where atnhDefdR x = ( atanh x, recip(1-x^2) *^ idL, dev_ε_δ $ \ε -> sqrt(tanh ε)*(1-abs x) )
                 -- Empirical, with epsEst upper bound.
  
  



isZeroMap :: ∀ v a . (FiniteDimensional v, AdditiveGroup a, Eq a) => (v:-*a) -> Bool
isZeroMap m = all ((==zeroV) . atBasis m) b
 where (Tagged b) = completeBasis :: Tagged v [Basis v]


