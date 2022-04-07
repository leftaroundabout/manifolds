-- |
-- Module      : Data.Function.Differentiable
-- Copyright   : (c) Justus Sagemüller 2015
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsag $ hvl.no
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
{-# LANGUAGE TypeApplications         #-}
{-# LANGUAGE UnicodeSyntax            #-}
{-# LANGUAGE MultiWayIf               #-}
{-# LANGUAGE LambdaCase               #-}
{-# LANGUAGE ScopedTypeVariables      #-}
{-# LANGUAGE RecordWildCards          #-}
{-# LANGUAGE CPP                      #-}


module Data.Function.Differentiable (
            -- * Everywhere differentiable functions
              Differentiable
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
            , intervalImages
            ) where
    


import Data.List
import Data.Maybe
import Data.Semigroup
import Data.Embedding
import Data.MemoTrie (HasTrie)

import Data.VectorSpace
import Math.LinearMap.Category
import Data.AffineSpace
import Data.Function.Differentiable.Data
import Data.Function.Affine
import Data.Basis
import Data.Tagged
import Data.Manifold.Types.Primitive
import Data.Manifold.PseudoAffine
import Data.Manifold.WithBoundary
import Data.Manifold.WithBoundary.Class
import Data.Manifold.Atlas

import qualified Prelude
import qualified Control.Applicative as Hask

import Control.Category.Constrained.Prelude hiding ((^))
import Control.Arrow.Constrained
import Control.Monad.Constrained
import Data.Foldable.Constrained



type RealDimension s
       = ( RealFloat' s, Manifold s, SimpleSpace s, Atlas' s
         , s ~ Needle s, s ~ Scalar s, s ~ DualVector s )


discretisePathIn :: (WithField ℝ Manifold y, SimpleSpace (Needle y))
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
              εx = my fx₀ `relaxNorm` [jf $ normalLength $ mx x₀]
              χ = δx² εx |$| 1
              xstep = dir * min (abs x₀+1) (recip χ)
              (fxlim, _, _) = f xlim
       xm = (xr + xl) / 2
                      
type ℝInterval = (ℝ,ℝ)

continuityRanges :: WithField ℝ Manifold y
      => Int                        -- ^ Max number of exploration steps per region
      -> RieMetric ℝ                -- ^ Needed resolution of boundaries
      -> RWDiffable ℝ ℝ y           -- ^ Function to investigate
      -> ([ℝInterval], [ℝInterval]) -- ^ Subintervals on which the function is guaranteed continuous.
continuityRanges nLim δbf (RWDiffable f)
  | (GlobalRegion, _) <- f xc
                 = ([], [(-huge,huge)])
  | otherwise    = glueMid (go xc (-1)) (go xc 1)
 where go x₀ dir
         | yq₀ <= abs ((jq₀$1) * step₀)
                      = go (x₀ + step₀/2) dir
         | RealSubray PositiveHalfSphere xl' <- rangeHere
                      = let stepl' = dir/(δbf xl'|$| 2)
                        in if dir>0
                            then if definedHere then [(max (xl'+stepl') x₀, huge)]
                                                else []
                            else if definedHere && x₀ > xl'+stepl'
                                  then (xl'+stepl',x₀) : go (xl'-stepl') dir
                                  else go (xl'-stepl') dir
         | RealSubray NegativeHalfSphere xr' <- rangeHere
                      = let stepr' = dir/(δbf xr'|$| 2)
                        in if dir<0
                            then if definedHere then [(-huge, min (xr'-stepr') x₀)]
                                                else []
                            else if definedHere && x₀ < xr'-stepr'
                                  then (x₀,xr'-stepr') : go (xr'+stepr') dir
                                  else go (xr'+stepr') dir
         | otherwise  = exit nLim dir x₀
        where (rangeHere, fq₀) = f x₀
              (PreRegion (Differentiable r₀)) = genericisePreRegion rangeHere
              (yq₀, jq₀, δyq₀) = r₀ x₀
              step₀ = dir/(δbf x₀|$| 1)
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
                     f'x = jq $ 1
                     stepp | f'x*dir < 0  = -0.9 * abs dir' * yq/f'x
                           | otherwise    = dir' * as_devεδ δyq yq -- TODO: memoise in `exit` recursion
                     resoHere = normSq $ δbf xq
                     resoStep = dir/sqrt(resoHere 1)
              definedHere = case fq₀ of
                              Just _  -> True
                              Nothing -> False
       glueMid ((l,le):ls) ((re,r):rs) | le==re  = (ls, (l,r):rs)
       glueMid l r = (l,r)
       huge = exp $ fromIntegral nLim
       xc = 0

discretisePathSegs :: (WithField ℝ Manifold y, SimpleSpace (Needle y))
      => Int              -- ^ Maximum number of path segments and/or points per segment.
      -> ( RieMetric ℝ
         , RieMetric y )  -- ^ Inaccuracy allowance /δ/ for arguments
                          --   (mostly relevant for resolution of discontinuity boundaries –
                          --   consider it a “safety margin from singularities”),
                          --   and /ε/ for results in the target space.
      -> RWDiffable ℝ ℝ y -- ^ Path specification. It is recommended that this
                          --   function be limited to a compact interval (e.g. with
                          --   '?>', '?<' and '?->'). For many functions the discretisation
                          --   will even work on an infinite interval: the point density
                          --   is exponentially decreased towards the infinities. But
                          --   this is still pretty bad for performance.
      -> ([[(ℝ,y)]], [[(ℝ,y)]]) -- ^ Discretised paths: continuous segments in either direction
discretisePathSegs nLim (mx,my) f@(RWDiffable ff)
                            = ( map discretise ivsL, map discretise ivsR )
 where (ivsL, ivsR) = continuityRanges nLim mx f
       discretise rng@(l,r) = discretisePathIn nLim rng (mx,my) fr
        where (_, Just fr) = ff $ (l+r)/2

              
analyseLocalBehaviour ::
     RWDiffable ℝ ℝ ℝ
  -> ℝ                      -- ^ /x/₀ value.
  -> Maybe ( (ℝ,ℝ)
           , ℝ->Maybe ℝ ) -- ^ /f/ /x/₀, derivative (i.e. Taylor-1-coefficient),
                           --   and reverse propagation of /O/ (/δ/²) bound.
analyseLocalBehaviour (RWDiffable f) x₀ = case f x₀ of
       (r, Just (Differentiable fd))
           | inRegion r x₀ -> return $
              let (fx, j, δf) = fd x₀
                  epsprop ε
                    | ε>0  = case (δf $ spanNorm [recip ε])|$| 1 of
                               0  -> empty
                               δ' -> return $ recip δ'
                    | otherwise  = pure 0
              in ((fx, j $ 1), epsprop)
       _ -> empty
 where                                    -- This check shouldn't really be necessary,
                                          -- because the initial value lies by definition
       inRegion GlobalRegion _ = True     -- in its domain.
       inRegion (PreRegion (Differentiable rf)) x
         | (yr,_,_) <- rf x   = yr>0
       inRegion (RealSubray PositiveHalfSphere xl) x = x>xl
       inRegion (RealSubray NegativeHalfSphere xr) x = x<xr

-- | Represent a 'Region' by a smooth function which is positive within the region,
--   and crosses zero at the boundary.
smoothIndicator :: (LocallyScalable ℝ q, Manifold q, Atlas' q, SimpleSpace (Needle q))
                       => Region ℝ q -> Differentiable ℝ q ℝ
smoothIndicator (Region _ r₀) = let (PreRegion r) = genericisePreRegion r₀
                                in  r

regionOfContinuityAround :: RWDiffable ℝ q x -> q -> Region ℝ q
regionOfContinuityAround (RWDiffable f) q = Region q . fst . f $ q
              

intervalImages ::
         Int                         -- ^ Max number of exploration steps per region
      -> (RieMetric ℝ, RieMetric ℝ)  -- ^ Needed resolution in (x,y) direction
      -> RWDiffable ℝ ℝ ℝ            -- ^ Function to investigate
      -> ( [(ℝInterval,ℝInterval)]
         , [(ℝInterval,ℝInterval)] ) -- ^ (XInterval, YInterval) rectangles in which
                                     --   the function graph lies.
intervalImages nLim (mx,my) f@(RWDiffable fd)
                  = (map (id&&&ivimg) domsL, map (id&&&ivimg) domsR)
 where (domsL, domsR) = continuityRanges nLim mx f
       ivimg (xl,xr) = go xl 1 i₀ ∪ go xr (-1) i₀
        where (_, Just fdd@(Differentiable fddd))
                    = second (fmap genericiseDifferentiable) $ fd xc
              xc = (xl+xr)/2
              i₀ = minimum&&&maximum $ [fdd$xl, fdd$xc, fdd$xr]
              go x dir (a,b)
                 | dir>0 && x>xc   = (a,b)
                 | dir<0 && x<xc   = (a,b)
                 | χ == 0          = (y + (x-xl)*y', y + (x-xr)*y')
                 | y < a+resoHere  = go (x + dir/χ) dir (y,b)
                 | y > b-resoHere  = go (x + dir/χ) dir (a,y)
                 | otherwise       = go (x + safeStep stepOut₀) dir (a,b)
               where (y, j, δε) = fddd x
                     y' = j $ 1
                     εx = my y
                     resoHere = normalLength εx
                     χ = δε εx|$| 1
                     safeStep s₀
                         | as_devεδ δε (safetyMarg s₀) > abs s₀  = s₀
                         | otherwise                             = safeStep (s₀*0.5)
                     stepOut₀ | y'*dir>0   = 0.5 * (b-y)/y'
                              | otherwise  = -0.5 * (y-a)/y'
                     safetyMarg stp = minimum [y-a, y+stp*y'-a, b-y, b-y-stp*y']
       infixl 3 ∪
       (a,b) ∪ (c,d) = (min a c, max b d)


hugeℝVal :: ℝ
hugeℝVal = 1e+100



showℝ :: RealFloat r => r -> String
showℝ x = show (realToFrac x :: Double)


unsafe_dev_ε_δ :: ∀ a . RealDimension a
                => String -> (a -> a) -> LinDevPropag a a
unsafe_dev_ε_δ = case ( linearManifoldWitness :: LinearManifoldWitness a
                      , closedScalarWitness :: ClosedScalarWitness a ) of
 (LinearManifoldWitness, ClosedScalarWitness) -> \errHint f d
           -> let ε'² = normSq d 1
              in if ε'²>0
                  then let δ = f . sqrt $ recip ε'²
                       in if δ > 0
                           then spanNorm [recip δ]
                           else error $ "ε-δ propagator function for "
                                    ++errHint++", with ε="
                                    ++showℝ (sqrt $ recip ε'²)
                                    ++ " gives non-positive δ="
                                    ++showℝ (realToFrac δ)++"."
                  else mempty
dev_ε_δ :: ∀ a . RealDimension a
         => (a -> a) -> Metric a -> Maybe (Metric a)
dev_ε_δ = case ( linearManifoldWitness :: LinearManifoldWitness a
                      , closedScalarWitness :: ClosedScalarWitness a ) of
 (LinearManifoldWitness, ClosedScalarWitness) -> \f d
           -> let ε'² = normSq d 1
              in if ε'²>0
                  then let δ = f . sqrt $ recip ε'²
                       in if δ > 0
                           then pure (spanNorm [recip δ])
                           else empty
                  else pure mempty

as_devεδ :: ∀ a . RealDimension a => LinDevPropag a a -> a -> a
as_devεδ = asdevεδ linearManifoldWitness closedScalarWitness where
 asdevεδ :: LinearManifoldWitness a -> ClosedScalarWitness a -> LinDevPropag a a -> a -> a
 asdevεδ LinearManifoldWitness ClosedScalarWitness
         ldp ε | ε>0
               , δ'² <- normSq (ldp $ spanNorm [recip ε]) 1
               , δ'² > 0
                    = sqrt $ recip δ'²
               | otherwise  = 0


genericiseDifferentiable :: (LocallyScalable s d, LocallyScalable s c)
                    => Differentiable s d c -> Differentiable s d c
genericiseDifferentiable (AffinDiffable _ af)
     = Differentiable $ \x -> let (y₀, ϕ) = evalAffine af x
                              in (y₀, ϕ, const mempty)
genericiseDifferentiable f = f


instance RealFrac' s => Category (Differentiable s) where
  type Object (Differentiable s) o = ( Manifold o, Atlas' o
                                     , LocallyScalable s o, SimpleSpace (Needle o) )
  id = Differentiable $ \x -> (x, id, const mempty)
  Differentiable f . Differentiable g = Differentiable $
     \x -> let (y, g', devg) = g x
               (z, f', devf) = f y
               devfg δz = let δy = transformNorm f' δz
                              εy = devf δz
                          in transformNorm g' εy <> devg δy <> devg εy
           in (z, f' . g', devfg)
  AffinDiffable ef f . AffinDiffable eg g = AffinDiffable (ef . eg) (f . g)
  f . g = genericiseDifferentiable f . genericiseDifferentiable g


-- instance (RealDimension s) => EnhancedCat (Differentiable s) (Affine s) where
--   arr (Affine co ao sl) = actuallyAffineEndo (ao .-^ lapply sl co) sl
  
instance (RealDimension s) => EnhancedCat (->) (Differentiable s) where
  arr (Differentiable f) x = let (y,_,_) = f x in y
  arr (AffinDiffable _ f) x = f $ x

instance (RealFrac'' s, SimpleSpace s) => Cartesian (Differentiable s) where
  type UnitObject (Differentiable s) = ZeroDim s
  swap = Differentiable $ \(x,y) -> ((y,x), swap, const mempty)
  attachUnit = Differentiable $ \x -> ((x, Origin), attachUnit, const mempty)
  detachUnit = Differentiable $ \(x, Origin) -> (x, detachUnit, const mempty)
  regroup = Differentiable $ \(x,(y,z)) -> (((x,y),z), regroup, const mempty)
  regroup' = Differentiable $ \((x,y),z) -> ((x,(y,z)), regroup', const mempty)


instance ∀ s . (RealFrac'' s, SimpleSpace s) => Morphism (Differentiable s) where
  (***) = prll
   where prll :: ∀ b β c γ . ( ObjectPair (Differentiable s) b β
                             , ObjectPair (Differentiable s) c γ )
                   => Differentiable s b c -> Differentiable s β γ
                        -> Differentiable s (b,β) (c,γ)
         prll (Differentiable f) (Differentiable g) = Differentiable h
          where h (x,y) = ((fx, gy), f'***g', devfg)
                 where (fx, f', devf) = f x
                       (gy, g', devg) = g y
                       devfg δs = transformNorm fst δx 
                                  <> transformNorm snd δy
                         where δx = devf $ transformNorm (id&&&zeroV) δs
                               δy = devg $ transformNorm (zeroV&&&id) δs
         prll (AffinDiffable IsDiffableEndo f) (AffinDiffable IsDiffableEndo g)
                 = case ( semimanifoldWitness @b, semimanifoldWitness @β
                        , smfdWBoundWitness @b, smfdWBoundWitness @β
                        , dualSpaceWitness @(Needle b), dualSpaceWitness @(Needle β)
                        , smfdWBoundWitness @s
                        ) of
           ( SemimanifoldWitness, SemimanifoldWitness
            ,OpenManifoldWitness, OpenManifoldWitness
            ,DualSpaceWitness, DualSpaceWitness
            ,OpenManifoldWitness )
             -> boundaryHasSameScalar @(Needle b)
                 ( boundaryHasSameScalar @(Needle β)
                 ( AffinDiffable IsDiffableEndo $ f *** g ))
         prll (AffinDiffable _ f) (AffinDiffable _ g)
          = boundaryHasSameScalar @(Needle β) (
             boundaryHasSameScalar @(Needle γ) (
              boundaryHasSameScalar @(Needle b) (
               boundaryHasSameScalar @(Needle c) (
              case ( semimanifoldWitness @β, semimanifoldWitness @γ
                   , semimanifoldWitness @b, semimanifoldWitness @c ) of
                 (SemimanifoldWitness, SemimanifoldWitness
                  , SemimanifoldWitness, SemimanifoldWitness)
                   -> AffinDiffable NotDiffableEndo $ f *** g
             ))))
         prll f g = genericiseDifferentiable f *** genericiseDifferentiable g


instance (RealFrac'' s, SimpleSpace s) => PreArrow (Differentiable s) where
  terminal = Differentiable $ \_ -> (Origin, zeroV, const mempty)
  fst = Differentiable $ \(x,_) -> (x, fst, const mempty)
  snd = Differentiable $ \(_,y) -> (y, snd, const mempty)
  Differentiable f &&& Differentiable g = Differentiable h
   where h x = ((fx, gx), f'&&&g', devfg)
          where (fx, f', devf) = f x
                (gx, g', devg) = g x
                devfg δs = (devf $ transformNorm (id&&&zeroV) δs)
                           <> (devg $ transformNorm (zeroV&&&id) δs)
  f &&& g = genericiseDifferentiable f &&& genericiseDifferentiable g


instance (RealFrac'' s, SimpleSpace s) => WellPointed (Differentiable s) where
  unit = Tagged Origin
  globalElement x = Differentiable $ \Origin -> (x, zeroV, const mempty)
  const x = Differentiable $ \_ -> (x, zeroV, const mempty)



type DfblFuncValue s = GenericAgent (Differentiable s)

instance (RealFrac'' s) => HasAgent (Differentiable s) where
  alg = genericAlg
  ($~) = genericAgentMap
instance ∀ s . (RealFloat'' s, SimpleSpace s) => CartesianAgent (Differentiable s) where
  alg1to2 = genericAlg1to2
  alg2to1 = a2t1
   where a2t1 :: ∀ α β γ . ( Manifold α, Manifold β
                           , Atlas' α, Atlas' β
                           , ProjectableBoundary α
                           , LocallyScalable s α, LocallyScalable s β
                           )
           => (∀ q . ( LocallyScalable s q, Manifold q, Atlas q
                     , Interior (Needle q) ~ Needle q
                     , PseudoAffineWithBoundary (Needle q)
                     , LinearManifold (Needle q)
                     , SimpleSpace (Needle q)
                     , HasTrie (ChartIndex q) )
               => DfblFuncValue s q α -> DfblFuncValue s q β -> DfblFuncValue s q γ )
           -> Differentiable s (α,β) γ
         a2t1 f = case ( semimanifoldWitness @α, semimanifoldWitness @β
                       , dualSpaceWitness @(Needle α), dualSpaceWitness @(Needle β) ) of
            ( SemimanifoldWitness, SemimanifoldWitness
             ,DualSpaceWitness, DualSpaceWitness )
                -> needleIsOpenMfd @α
                    (needleIsOpenMfd @β
                      (boundaryHasSameScalar @α
                        (boundaryHasSameScalar @β
                          (boundaryHasSameScalar @(Needle α)
                            (boundaryHasSameScalar @(Needle β)
                              (undefined -- genericAlg2to1 f
                                     ))))))
  alg2to2 = a2t1
   where a2t1 :: ∀ α β γ δ . ( Manifold α, Manifold β, Manifold γ, Manifold δ
                             , Atlas' α, Atlas' β, Atlas' γ, Atlas' δ
                             , LocallyScalable s α, LocallyScalable s β
                             , LocallyScalable s γ, LocallyScalable s δ )
           => (∀ q . ( LocallyScalable s q, Manifold q, Atlas q
                     , Interior (Needle q) ~ Needle q
                     , PseudoAffineWithBoundary (Needle q)
                     , LinearManifold (Needle q)
                     , SimpleSpace (Needle q)
                     , HasTrie (ChartIndex q) )
               => DfblFuncValue s q α -> DfblFuncValue s q β
                     -> (DfblFuncValue s q γ, DfblFuncValue s q δ) )
           -> Differentiable s (α,β) (γ,δ)
         a2t1 f = case ( semimanifoldWitness @α, semimanifoldWitness @β
                       , semimanifoldWitness @γ, semimanifoldWitness @δ
                       , dualSpaceWitness @(Needle α), dualSpaceWitness @(Needle β)
                       , dualSpaceWitness @(Needle γ), dualSpaceWitness @(Needle δ) ) of
            ( SemimanifoldWitness, SemimanifoldWitness
             ,SemimanifoldWitness, SemimanifoldWitness
             ,DualSpaceWitness, DualSpaceWitness
             ,DualSpaceWitness, DualSpaceWitness )
                 -> needleIsOpenMfd @α
                    (needleIsOpenMfd @β
                     (needleIsOpenMfd @γ
                      (needleIsOpenMfd @δ
                       (boundaryHasSameScalar @α
                        (boundaryHasSameScalar @β
                         (boundaryHasSameScalar @γ
                          (boundaryHasSameScalar @δ
                           (boundaryHasSameScalar @(Needle α)
                            (boundaryHasSameScalar @(Needle β)
                             (boundaryHasSameScalar @(Needle γ)
                              (boundaryHasSameScalar @(Needle δ)
                               (undefined -- genericAlg2to2 f
                                 ))))))))))))
instance (RealFrac'' s, SimpleSpace s)
      => PointAgent (DfblFuncValue s) (Differentiable s) a x where
  point = genericPoint


actuallyLinearEndo :: (Object (Affine s) x, Object (LinearMap s) x)
            => (x+>x) -> Differentiable s x x
actuallyLinearEndo = AffinDiffable IsDiffableEndo . arr

actuallyAffineEndo :: (Object (Affine s) x, Object (LinearMap s) x)
            => x -> (x+>Needle x) -> Differentiable s x x
actuallyAffineEndo y₀ f = AffinDiffable IsDiffableEndo $ fromOffsetSlope y₀ f


actuallyLinear :: ( Object (Affine s) x, Object (Affine s) y
                  , Object (LinearMap s) x, Object (LinearMap s) y )
            => (x+>y) -> Differentiable s x y
actuallyLinear = AffinDiffable NotDiffableEndo . arr

actuallyAffine :: ( Object (Affine s) x, Object (Affine s) y
                  , Object (LinearMap s) x, Object (LinearMap s) (Needle y) )
            => y -> (x+>Needle y) -> Differentiable s x y
actuallyAffine y₀ f = AffinDiffable NotDiffableEndo $ fromOffsetSlope y₀ f


-- affinPoint :: (WithField s LinearManifold c, WithField s LinearManifold d)
--                   => c -> DfblFuncValue s d c
-- affinPoint p = GenericAgent (AffinDiffable (const p))


dfblFnValsFunc :: ∀ c c' d v v' ε s
     . ( Manifold c, Manifold d, Manifold c'
       , Atlas' c, Atlas' d, Atlas' c'
       , ProjectableBoundary s, ProjectableBoundary v'
       , ProjectableBoundary (Needle d)
       , SimpleSpace (Needle d)
       , LocallyScalable s c, LocallyScalable s c', LocallyScalable s d
       , v ~ Needle c, v' ~ Needle c'
       , ε ~ Norm v, ε ~ Norm v'
       , SimpleSpace v'
       , RealFrac'' s )
             => (c' -> (c, v'+>v, ε->ε)) -> DfblFuncValue s d c' -> DfblFuncValue s d c
dfblFnValsFunc f = case ( scalarSpaceWitness @s
                        , smfdWBoundWitness @s
                        , semimanifoldWitness @d
                        , semimanifoldWitness @c' ) of
   ( ScalarSpaceWitness, OpenManifoldWitness
    ,SemimanifoldWitness, SemimanifoldWitness )
        -> needleIsOpenMfd @c (needleIsOpenMfd @d (Differentiable f $~))

dfblFnValsCombine :: forall d c c' c'' v v' v'' ε ε' ε'' s. 
         ( LocallyScalable s c,  LocallyScalable s c',  LocallyScalable s c''
         ,  LocallyScalable s d
         , v ~ Needle c, v' ~ Needle c', v'' ~ Needle c''
         , ε ~ Norm v  , ε' ~ Norm v'  , ε'' ~ Norm v'', ε~ε', ε~ε'' 
         , SimpleSpace (Needle d)
         , RealFrac' s )
       => (  c' -> c'' -> (c, (v',v'')+>v, ε -> (ε',ε''))  )
         -> DfblFuncValue s d c' -> DfblFuncValue s d c'' -> DfblFuncValue s d c
dfblFnValsCombine cmb (GenericAgent (Differentiable f))
                      (GenericAgent (Differentiable g)) 
    = GenericAgent . Differentiable $
        \d -> let (c', jf, devf) = f d
                  (c'', jg, devg) = g d
                  (c, jh, devh) = cmb c' c''
                  jhl = jh . (id&&&zeroV); jhr = jh . (zeroV&&&id)
              in ( c
                 , jh <<< jf&&&jg
                 , \εc -> let εc' = transformNorm jhl εc
                              εc'' = transformNorm jhr εc
                              (δc',δc'') = devh εc 
                          in devf εc' <> devg εc''
                               <> transformNorm jf δc'
                               <> transformNorm jg δc''
                 )
dfblFnValsCombine cmb (GenericAgent fa) (GenericAgent ga) 
         = dfblFnValsCombine cmb (GenericAgent $ genericiseDifferentiable fa)
                                 (GenericAgent $ genericiseDifferentiable ga)





instance ∀ v s a . ( LinearManifold v, Scalar v ~ s
                   , LocallyScalable s a, Manifold a, Atlas' a, Atlas' v
                   , SimpleSpace v, SimpleSpace (Needle a)
                   , RealFloat'' s )
    => AdditiveGroup (DfblFuncValue s a v) where
  zeroV = case ( linearManifoldWitness @v, dualSpaceWitness @v
               , semimanifoldWitness @a
               ) of
     (LinearManifoldWitness, DualSpaceWitness, SemimanifoldWitness)
         -> needleIsOpenMfd @a (scalarIsOpenMfd @a
               (needleBoundaryIsTrivallyProjectible @a (point zeroV)))
  (^+^) = needleIsOpenMfd @a ( needleBoundaryIsTrivallyProjectible @a
               (case ( linearManifoldWitness @v
                     , linearManifoldWitness @(Needle a)
                     , dualSpaceWitness @v
                     , dualSpaceWitness @(Needle a) ) of
     (LinearManifoldWitness, LinearManifoldWitness
      ,DualSpaceWitness, DualSpaceWitness)
         -> curry $ \case
        (GenericAgent (AffinDiffable ef f), GenericAgent (AffinDiffable eg g))
              -> GenericAgent $ AffinDiffable (ef<>eg) (f^+^g)
        (α,β) -> dfblFnValsCombine (\a b -> (a^+^b, arr addV, const mempty)) α β
    ))
  negateV = needleIsOpenMfd @a (case ( linearManifoldWitness @v, dualSpaceWitness @v
                                     , semimanifoldWitness @a
                                     ) of
     (LinearManifoldWitness, DualSpaceWitness, SemimanifoldWitness)
         -> needleBoundaryIsTrivallyProjectible @a (\case
         (GenericAgent (AffinDiffable ef f))
           -> GenericAgent $ AffinDiffable ef (negateV f)
         α -> dfblFnValsFunc (\a -> (negateV a, negateV id, const mempty)) α
      )
    )
  
instance ∀ n a . ( RealFloat'' n, Manifold a, LocallyScalable n a
                 , SimpleSpace (Needle a)
                 , Atlas' a, Atlas' n
                 )
            => Num (DfblFuncValue n a n) where
  fromInteger = case ( linearManifoldWitness @n, dualSpaceWitness @n
                     , semimanifoldWitness @a, closedScalarWitness @n
                     ) of
     (LinearManifoldWitness, DualSpaceWitness, SemimanifoldWitness, ClosedScalarWitness)
         -> needleIsOpenMfd @a (scalarIsOpenMfd @a
               (needleBoundaryIsTrivallyProjectible @a (point . fromInteger)))
  (+) = case closedScalarWitness :: ClosedScalarWitness n of
      ClosedScalarWitness -> (^+^)
  (*) = case ( linearManifoldWitness :: LinearManifoldWitness n
             , closedScalarWitness :: ClosedScalarWitness n ) of
      (LinearManifoldWitness, ClosedScalarWitness) -> dfblFnValsCombine $
          \a b -> ( a*b
                  , arr $ addV <<< (scale $ a)***(scale $ b)
                  , unsafe_dev_ε_δ(showℝ a++"*"++showℝ b) (sqrt :: n->n)
                       >>> \d¹₂ -> (d¹₂,d¹₂)
                           -- ε δa δb = (a+δa)·(b+δb) - (a·b + (a·δa + b·δb)) 
                           --         = δa·δb
                           --   so choose δa = δb = √ε
                  )
  negate = case closedScalarWitness :: ClosedScalarWitness n of
     ClosedScalarWitness -> negateV
  abs = needleBoundaryIsTrivallyProjectible @a (
   case (linearManifoldWitness @n, closedScalarWitness @n) of
         (LinearManifoldWitness, ClosedScalarWitness) -> dfblFnValsFunc dfblAbs
          where dfblAbs a
                 | a>0        = (a, id, unsafe_dev_ε_δ("abs "++showℝ a) $ \ε -> a + ε/2) 
                 | a<0        = (-a, negateV id, unsafe_dev_ε_δ("abs "++showℝ a)
                                       $ \ε -> ε/2 - a)
                 | otherwise  = (0, zeroV, scaleNorm (sqrt 0.5))
     )
  signum = needleBoundaryIsTrivallyProjectible @a (
   case (linearManifoldWitness @n, closedScalarWitness @n) of
         (LinearManifoldWitness, ClosedScalarWitness) -> dfblFnValsFunc dfblSgn
          where dfblSgn a
                 | a>0        = (1, zeroV, unsafe_dev_ε_δ("signum "++showℝ a) $ const a)
                 | a<0        = (-1, zeroV, unsafe_dev_ε_δ("signum "++showℝ a) $ \_ -> -a)
                 | otherwise  = (0, zeroV, const $ spanNorm [1])
     )



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
minDblfuncs :: ∀ m s . (LocallyScalable s m, RealFloat'' s)
     => Differentiable s m s -> Differentiable s m s -> Differentiable s m s
minDblfuncs (Differentiable f) (Differentiable g)
             = Differentiable $ h linearManifoldWitness closedScalarWitness
 where h :: LinearManifoldWitness s -> ClosedScalarWitness s
             -> m -> (s, Needle m+>Needle s, LinDevPropag m s)
       h (LinearManifoldWitness) ClosedScalarWitness x
         | fx < gx   = ( fx, jf
                       , \d -> devf d <> devg d
                               <> transformNorm δj
                                      (spanNorm [recip $ recip(d|$|1) + gx - fx]) )
         | fx > gx   = ( gx, jg
                       , \d -> devf d <> devg d
                               <> transformNorm δj
                                      (spanNorm [recip $ recip(d|$|1) + fx - gx]) )
         | otherwise = ( fx, (jf^+^jg)^/2
                       , \d -> devf d <> devg d
                               <> transformNorm δj d )
        where (fx, jf, devf) = f x
              (gx, jg, devg) = g x
              δj = jf ^-^ jg


postEndo :: ∀ c a b . (HasAgent c, Object c a, Object c b)
                        => c a a -> GenericAgent c b a -> GenericAgent c b a
postEndo = genericAgentMap



genericisePreRegion :: ∀ m s
    . ( RealFloat'' s, LocallyScalable s m, Manifold m
      , Atlas' m, Atlas' s, SimpleSpace (Needle m)
      )
                          => PreRegion s m -> PreRegion s m
genericisePreRegion
 = scalarIsOpenMfd @m (needleIsOpenMfd @m (needleBoundaryIsTrivallyProjectible @m 
    (scalarBoundaryIsTrivallyProjectible @m (
      case ( linearManifoldWitness @s, closedScalarWitness @s, semimanifoldWitness @m ) of
    (LinearManifoldWitness, ClosedScalarWitness, SemimanifoldWitness)
          -> \case
          GlobalRegion -> PreRegion $ const 1
          RealSubray PositiveHalfSphere xl -> preRegionToInfFrom' xl
          RealSubray NegativeHalfSphere xr -> preRegionFromMinInfTo' xr
          r -> r
  ))))

-- | Set-intersection of regions would not be guaranteed to yield a connected result
--   or even have the reference point of one region contained in the other. This
--   combinator assumes (unchecked) that the references are in a connected
--   sub-intersection, which is used as the result.
unsafePreRegionIntersect :: ∀ a s
    . ( RealFloat'' s, LocallyScalable s a
      , Manifold a, Atlas' a, Atlas' s
      , SimpleSpace (Needle a) )
                  => PreRegion s a -> PreRegion s a -> PreRegion s a
unsafePreRegionIntersect GlobalRegion r = r
unsafePreRegionIntersect r GlobalRegion = r
unsafePreRegionIntersect (RealSubray PositiveHalfSphere xl) (RealSubray PositiveHalfSphere xl')
                 = RealSubray PositiveHalfSphere $ max xl xl'
unsafePreRegionIntersect (RealSubray NegativeHalfSphere xr) (RealSubray NegativeHalfSphere xr')
                 = RealSubray NegativeHalfSphere $ min xr xr'
unsafePreRegionIntersect (PreRegion ra) (PreRegion rb) = case scalarSpaceWitness @s of
      ScalarSpaceWitness -> PreRegion $ minDblfuncs ra rb
unsafePreRegionIntersect ra rb
   = unsafePreRegionIntersect (genericisePreRegion ra) (genericisePreRegion rb)

-- | Cartesian product of two regions.
regionProd :: ∀ a b s . ( RealDimension s, ObjectPair (Differentiable s) a b )
                  => Region s a -> Region s b -> Region s (a,b)
regionProd (Region a₀ ra) (Region b₀ rb) = Region (a₀,b₀) (preRegionProd ra rb)

-- | Cartesian product of two pre-regions.
preRegionProd :: ∀ a b s . ( RealDimension s, ObjectPair (Differentiable s) a b )
                  => PreRegion s a -> PreRegion s b -> PreRegion s (a,b)
preRegionProd = boundaryHasSameScalar @b
              ( case ( semimanifoldWitness @a, semimanifoldWitness @b
                     , linearManifoldWitness @s, closedScalarWitness @s
                     , smfdWBoundWitness @b ) of
     ( SemimanifoldWitness, SemimanifoldWitness
      ,LinearManifoldWitness, ClosedScalarWitness
      ,OpenManifoldWitness ) -> \case
                      GlobalRegion -> \case
                          GlobalRegion -> GlobalRegion
                          (PreRegion rb) -> PreRegion $ rb . snd
                      (PreRegion ra) -> \case
                          GlobalRegion -> PreRegion $ ra . fst
                          (PreRegion rb) -> PreRegion $ minDblfuncs (ra.fst) (rb.snd)
                      ra -> \rb -> preRegionProd (genericisePreRegion ra)
                                                 (genericisePreRegion rb)
   )


positivePreRegion, negativePreRegion :: (RealDimension s) => PreRegion s s
positivePreRegion = RealSubray PositiveHalfSphere 0
negativePreRegion = RealSubray NegativeHalfSphere 0


positivePreRegion', negativePreRegion' :: ∀ s . (RealDimension s) => PreRegion s s
positivePreRegion' = PreRegion . Differentiable
                       $ prr linearManifoldWitness closedScalarWitness
 where prr :: LinearManifoldWitness s -> ClosedScalarWitness s
           -> s -> (s, Needle s+>Needle s, LinDevPropag s s)
       prr (LinearManifoldWitness) ClosedScalarWitness
           x = ( 1 - 1/xp1
               , (1/xp1²) *^ id
               , unsafe_dev_ε_δ("positivePreRegion@"++showℝ x) δ )
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
negativePreRegion' = npr (linearManifoldWitness :: LinearManifoldWitness s)
                         (closedScalarWitness :: ClosedScalarWitness s)
 where npr (LinearManifoldWitness)
           (ClosedScalarWitness :: ClosedScalarWitness s)
                  = PreRegion $ ppr . ngt
        where PreRegion ppr = positivePreRegion' :: PreRegion s s
              ngt = actuallyLinearEndo $ negateV id

preRegionToInfFrom, preRegionFromMinInfTo :: RealDimension s => s -> PreRegion s s
preRegionToInfFrom = RealSubray PositiveHalfSphere
preRegionFromMinInfTo = RealSubray NegativeHalfSphere

preRegionToInfFrom', preRegionFromMinInfTo' :: ∀ s . RealDimension s => s -> PreRegion s s
preRegionToInfFrom' = prif (linearManifoldWitness :: LinearManifoldWitness s)
                           (closedScalarWitness :: ClosedScalarWitness s)
 where prif (LinearManifoldWitness)
            (ClosedScalarWitness :: ClosedScalarWitness s)
            xs = PreRegion $ ppr . trl
        where PreRegion ppr = positivePreRegion' :: PreRegion s s
              trl = actuallyAffineEndo (-xs) id
preRegionFromMinInfTo' = prif (linearManifoldWitness :: LinearManifoldWitness s)
                           (closedScalarWitness :: ClosedScalarWitness s)
 where prif (LinearManifoldWitness)
            (ClosedScalarWitness :: ClosedScalarWitness s)
            xe = PreRegion $ ppr . flp
        where PreRegion ppr = positivePreRegion' :: PreRegion s s
              flp = actuallyAffineEndo xe (negateV id)

intervalPreRegion :: ∀ s . RealDimension s => (s,s) -> PreRegion s s
intervalPreRegion (lb,rb) = PreRegion . Differentiable
                             $ prr linearManifoldWitness closedScalarWitness
 where m = lb + radius; radius = (rb - lb)/2
       prr :: LinearManifoldWitness s -> ClosedScalarWitness s
                -> s -> (s, Needle s+>Needle s, LinDevPropag s s)
       prr (LinearManifoldWitness) ClosedScalarWitness
           x = ( 1 - ((x-m)/radius)^2
               , (2*(m-x)/radius^2) *^ id
               , unsafe_dev_ε_δ("intervalPreRegion@"++showℝ x) $ (*radius) . sqrt )











instance (RealDimension s) => Category (RWDiffable s) where
  type Object (RWDiffable s) o = Object (Differentiable s) o
  id = rwdid
   where rwdid :: ∀ a . Object (RWDiffable s) a => RWDiffable s a a
         rwdid = RWDiffable $ \x -> (GlobalRegion, pure id)
  RWDiffable f . RWDiffable g = RWDiffable h where
   h x₀ = case g x₀ of
           ( rg, Just gr'@(AffinDiffable IsDiffableEndo gr) )
            -> let (y₀, ϕg) = evalAffine gr x₀
               in case f y₀ of
                   (GlobalRegion, Just (AffinDiffable fe fr))
                         -> (rg, Just (AffinDiffable fe (fr.gr)))
                   (GlobalRegion, fhr)
                         -> (rg, fmap (. gr') fhr)
                   (RealSubray diry yl, fhr)
                      -> let hhr = fmap (. gr') fhr
                         in case ϕg $ 1 of
                              y' | y'>0 -> ( unsafePreRegionIntersect rg
                                                  $ RealSubray diry (x₀ + (yl-y₀)/y')
                                   -- y'⋅(xl−x₀) + y₀ ≝ yl
                                           , hhr )
                                 | y'<0 -> ( unsafePreRegionIntersect rg
                                                  $ RealSubray (otherHalfSphere diry)
                                                               (x₀ + (yl-y₀)/y')
                                           , hhr )
                                 | otherwise -> (rg, hhr)
                   (PreRegion ry, fhr)
                         -> ( PreRegion $ ry . gr', fmap (. gr') fhr )
           ( rg, Just gr'@(AffinDiffable _ gr) )
            -> error "( rg, Just gr'@(AffinDiffable gr) )"
           (GlobalRegion, Just gr@(Differentiable grd))
            -> let (y₀,_,_) = grd x₀
               in case f y₀ of
                   (GlobalRegion, Nothing)
                         -> (GlobalRegion, notDefinedHere)
                   (GlobalRegion, Just fr)
                         -> (GlobalRegion, pure (fr . gr))
                   (r, Nothing) | PreRegion ry <- genericisePreRegion r
                         -> ( PreRegion $ ry . gr, notDefinedHere )
                   (r, (Just fr)) | PreRegion ry <- genericisePreRegion r
                         -> ( PreRegion $ ry . gr, pure (fr . gr) )
           (rg@(RealSubray _ _), Just gr@(Differentiable grd))
            -> let (y₀,_,_) = grd x₀
               in case f y₀ of
                   (GlobalRegion, Nothing)
                         -> (rg, notDefinedHere)
                   (GlobalRegion, Just fr)
                         -> (rg, pure (fr . gr))
                   (rf, Nothing)
                     | PreRegion rx <- genericisePreRegion rg
                     , PreRegion ry <- genericisePreRegion rf
                         -> ( PreRegion $ minDblfuncs (ry . gr) rx
                            , notDefinedHere )
                   (rf, Just fr)
                     | PreRegion rx <- genericisePreRegion rg
                     , PreRegion ry <- genericisePreRegion rf
                         -> ( PreRegion $ minDblfuncs (ry . gr) rx
                            , pure (fr . gr) )
           (PreRegion rx, Just gr@(Differentiable grd))
            -> let (y₀,_,_) = grd x₀
               in case f y₀ of
                   (GlobalRegion, Nothing)
                         -> (PreRegion rx, notDefinedHere)
                   (GlobalRegion, Just fr)
                         -> (PreRegion rx, pure (fr . gr))
                   (r, Nothing) | PreRegion ry <- genericisePreRegion r
                         -> ( PreRegion $ minDblfuncs (ry . gr) rx
                            , notDefinedHere )
                   (r, Just fr) | PreRegion ry <- genericisePreRegion r

                         -> ( PreRegion $ minDblfuncs (ry . gr) rx
                            , pure (fr . gr) )
           (r, Nothing)
            -> (r, notDefinedHere)
          


globalDiffable' :: Differentiable s a b -> RWDiffable s a b
globalDiffable' f = RWDiffable $ const (GlobalRegion, pure f)



instance (RealDimension s) => EnhancedCat (RWDiffable s) (Differentiable s) where
  arr = globalDiffable'
                
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
  RWDFV_IdVar :: RWDfblFuncValue s c c
  GenericRWDFV :: RWDiffable s d c -> RWDfblFuncValue s d c

genericiseRWDFV ::
   ( RealDimension s, Object (Differentiable s) d, Object (Differentiable s) c )
                    => RWDfblFuncValue s d c -> RWDfblFuncValue s d c
genericiseRWDFV (ConstRWDFV c) = GenericRWDFV $ const c
genericiseRWDFV RWDFV_IdVar = GenericRWDFV id
genericiseRWDFV v = v

instance RealDimension s => HasAgent (RWDiffable s) where
  type AgentVal (RWDiffable s) d c = RWDfblFuncValue s d c
  alg fq = case fq RWDFV_IdVar of
    GenericRWDFV f -> f
    ConstRWDFV c -> const c
    RWDFV_IdVar -> id
  ($~) = postCompRW
instance RealDimension s => CartesianAgent (RWDiffable s) where
  alg1to2 fgq = case fgq RWDFV_IdVar of
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
        , Object (Differentiable s) d, Object (Differentiable s) c, Object (Differentiable s) c'
        , v ~ Needle c, v' ~ Needle c'
        , SimpleSpace v
        , ε ~ Norm v, ε ~ Norm v' )
             => (c' -> (c, v'+>v, ε->ε)) -> RWDfblFuncValue s d c' -> RWDfblFuncValue s d c
grwDfblFnValsFunc f = (RWDiffable (\_ -> (GlobalRegion, pure (Differentiable f))) $~)

grwDfblFnValsCombine :: forall d c c' c'' v v' v'' ε ε' ε'' s. 
         ( RealDimension s
         , Object (Differentiable s) d, Object (Differentiable s) c'
         , Object (Differentiable s) c', Object (Differentiable s) c''
         , v ~ Needle c, v' ~ Needle c', v'' ~ Needle c''
         , SimpleSpace v
         , ε ~ Norm v  , ε' ~ Norm v'  , ε'' ~ Norm v'', ε~ε', ε~ε''  )
       => (  c' -> c'' -> (c, (v',v'')+>v, ε -> (ε',ε''))  )
         -> RWDfblFuncValue s d c' -> RWDfblFuncValue s d c'' -> RWDfblFuncValue s d c
grwDfblFnValsCombine cmb (GenericRWDFV (RWDiffable fpcs))
                         (GenericRWDFV (RWDiffable gpcs)) 
    = GenericRWDFV . RWDiffable $
        \d₀ -> let (rc', fmay) = fpcs d₀
                   (rc'',gmay) = gpcs d₀
               in (unsafePreRegionIntersect rc' rc'',) $
                    case (genericiseDifferentiable<$>fmay, genericiseDifferentiable<$>gmay) of
                      (Just(Differentiable f), Just(Differentiable g)) ->
                        pure . Differentiable $ \d
                         -> let (c', jf, devf) = f d
                                (c'',jg, devg) = g d
                                (c, jh, devh) = cmb c' c''
                                jhl = jh . (id&&&zeroV); jhr = jh . (zeroV&&&id)
                            in ( c
                               , jh <<< jf&&&jg
                               , \εc -> let εc' = transformNorm jhl εc
                                            εc'' = transformNorm jhr εc
                                            (δc',δc'') = devh εc 
                                        in devf εc' <> devg εc''
                                             <> transformNorm jf δc'
                                             <> transformNorm jg δc''
                               )
                      _ -> notDefinedHere
grwDfblFnValsCombine cmb fv gv
        = grwDfblFnValsCombine cmb (genericiseRWDFV fv) (genericiseRWDFV gv)

          
rwDfbl_plus :: ∀ a v s .
        ( RealDimension s
        , Object (Differentiable s) a, Object (Differentiable s) v
        , LinearSpace v )
      => RWDiffable s a v -> RWDiffable s a v -> RWDiffable s a v
rwDfbl_plus (RWDiffable f) (RWDiffable g) = RWDiffable
              $ needleIsOpenMfd @a (needleBoundaryIsTrivallyProjectible @a (
                   h linearManifoldWitness linearManifoldWitness
                        dualSpaceWitness dualSpaceWitness))
   where h :: (OpenManifold (Needle a), ProjectableBoundary (Needle a))
               => LinearManifoldWitness v -> LinearManifoldWitness (Needle a)
               -> DualSpaceWitness v -> DualSpaceWitness (Needle a)
                -> a -> (PreRegion s a, Maybe (Differentiable s a v))
         h LinearManifoldWitness LinearManifoldWitness DualSpaceWitness DualSpaceWitness
           x₀ = (rh, liftA2 fgplus ff gf)
          where (rf, ff) = f x₀
                (rg, gf) = g x₀
                rh = unsafePreRegionIntersect rf rg
                fgplus :: Differentiable s a v -> Differentiable s a v -> Differentiable s a v
                fgplus (Differentiable fd) (Differentiable gd) = Differentiable hd
                 where hd x = (fx^+^gx, jf^+^jg, \ε -> δf(scaleNorm 2 ε)
                                                     <> δg(scaleNorm 2 ε))
                        where (fx, jf, δf) = fd x
                              (gx, jg, δg) = gd x
                fgplus (Differentiable fd) (AffinDiffable _ ga)
                                 = Differentiable hd
                 where hd x = (fx^+^gx, jf^+^ϕg, δf)
                        where (fx, jf, δf) = fd x
                              (gx, ϕg) = evalAffine ga x
                fgplus (AffinDiffable _ fa) (Differentiable gd)
                                 = Differentiable hd
                 where hd x = (fx^+^gx, ϕf^+^jg, δg)
                        where (gx, jg, δg) = gd x
                              (fx, ϕf) = evalAffine fa x
                fgplus (AffinDiffable fe fa) (AffinDiffable ge ga)
                           = AffinDiffable (fe<>ge) (fa^+^ga)

rwDfbl_negateV :: ∀ a v s .
        ( WithField s Manifold a
        , LinearSpace v, Scalar v ~ s
        , RealDimension s )
      => RWDiffable s a v -> RWDiffable s a v
rwDfbl_negateV (RWDiffable f) = RWDiffable
           $ needleIsOpenMfd @a (needleBoundaryIsTrivallyProjectible @a (
                  h linearManifoldWitness dualSpaceWitness
                    linearManifoldWitness dualSpaceWitness))
   where h :: (OpenManifold (Needle a), ProjectableBoundary (Needle a))
             => LinearManifoldWitness v -> DualSpaceWitness v
              -> LinearManifoldWitness (Needle a) -> DualSpaceWitness (Needle a)
                -> a -> (PreRegion s a, Maybe (Differentiable s a v))
         h LinearManifoldWitness DualSpaceWitness LinearManifoldWitness DualSpaceWitness
           x₀ = (rf, fmap fneg ff)
          where (rf, ff) = f x₀
                fneg :: Differentiable s a v -> Differentiable s a v
                fneg (Differentiable fd) = Differentiable hd
                 where hd x = (negateV fx, negateV jf, δf)
                        where (fx, jf, δf) = fd x
                fneg (AffinDiffable ef af) = AffinDiffable ef $ negateV af

postCompRW :: ∀ a b c s . ( RealDimension s
                          , Object (Differentiable s) a
                          , Object (Differentiable s) b
                          , Object (Differentiable s) c )
              => RWDiffable s b c -> RWDfblFuncValue s a b -> RWDfblFuncValue s a c
postCompRW (RWDiffable f) (ConstRWDFV x) = case f x of
     (_, Just fd) -> ConstRWDFV $ fd $ x
postCompRW f RWDFV_IdVar = GenericRWDFV f
postCompRW f (GenericRWDFV g) = GenericRWDFV $ f . g


instance ∀ s a v . ( RealDimension s
                   , Object (Differentiable s) a, Object (Differentiable s) v
                   , LinearSpace v )
    => AdditiveGroup (RWDfblFuncValue s a v) where
  zeroV = case ( linearManifoldWitness :: LinearManifoldWitness v
               , dualSpaceWitness :: DualSpaceWitness v ) of
      (LinearManifoldWitness, DualSpaceWitness) -> point zeroV
  (^+^) = case ( linearManifoldWitness :: LinearManifoldWitness v
               , dualSpaceWitness :: DualSpaceWitness v ) of
      (LinearManifoldWitness, DualSpaceWitness)
         -> curry $ \case
              (ConstRWDFV c₁, ConstRWDFV c₂) -> ConstRWDFV (c₁^+^c₂)
              (ConstRWDFV c₁, RWDFV_IdVar) -> GenericRWDFV $
                               globalDiffable' (actuallyAffineEndo c₁ id)
              (RWDFV_IdVar, ConstRWDFV c₂) -> GenericRWDFV $
                               globalDiffable' (actuallyAffineEndo c₂ id)
              (ConstRWDFV c₁, GenericRWDFV g) -> GenericRWDFV $
                               globalDiffable' (actuallyAffineEndo c₁ id) . g
              (GenericRWDFV f, ConstRWDFV c₂) -> GenericRWDFV $
                                  globalDiffable' (actuallyAffineEndo c₂ id) . f
              (fa, ga) | GenericRWDFV f <- genericiseRWDFV fa
                       , GenericRWDFV g <- genericiseRWDFV ga
                                -> GenericRWDFV $ rwDfbl_plus f g
  negateV = case ( linearManifoldWitness :: LinearManifoldWitness v
                 , dualSpaceWitness :: DualSpaceWitness v ) of
      (LinearManifoldWitness, DualSpaceWitness) -> \case
        (ConstRWDFV c) -> ConstRWDFV (negateV c)
        RWDFV_IdVar -> GenericRWDFV $ globalDiffable' (actuallyLinearEndo $ negateV id)
        (GenericRWDFV f) -> GenericRWDFV $ rwDfbl_negateV f

dualCoCoProduct :: ∀ v w s .
                   ( SimpleSpace v, HilbertSpace v
                   , SimpleSpace w, Scalar v ~ s, Scalar w ~ s )
           => LinearMap s w v -> LinearMap s w v -> Norm w
dualCoCoProduct = dccp (dualSpaceWitness::DualSpaceWitness w)
 where dccp DualSpaceWitness s t = Norm $ (tSpread*sSpread) *^ t²Ps²M
        where t' = adjoint $ t :: LinearMap s v (DualVector w)
              s' = adjoint $ s :: LinearMap s v (DualVector w)
              tSpread = sum . map recip_t²PLUSs² $ snd (decomposeLinMap t') []
              sSpread = sum . map recip_t²PLUSs² $ snd (decomposeLinMap s') []
              t²PLUSs²'@(Norm t²Ps²M)
                = transformNorm t euclideanNorm <> transformNorm s euclideanNorm :: Norm w
              recip_t²PLUSs² = normSq (dualNorm t²PLUSs²') :: DualVector w -> s

instance ∀ n a . ( RealDimension n, Object (Differentiable n) a, SimpleSpace (Needle a) )
            => Num (RWDfblFuncValue n a n) where
  fromInteger i = point $ fromInteger i
  (+) = (^+^)
  ConstRWDFV c₁ * ConstRWDFV c₂ = ConstRWDFV (c₁*c₂)
  ConstRWDFV c₁ * RWDFV_IdVar = GenericRWDFV $
                               globalDiffable' (actuallyLinearEndo . arr $ scale $ c₁)
  RWDFV_IdVar * ConstRWDFV c₂ = GenericRWDFV $
                               globalDiffable' (actuallyLinearEndo . arr $ scale $ c₂)
  ConstRWDFV c₁ * GenericRWDFV g = GenericRWDFV $
                               globalDiffable' (actuallyLinearEndo . arr $ scale $ c₁) . g
  GenericRWDFV f * ConstRWDFV c₂ = GenericRWDFV $
                               globalDiffable' (actuallyLinearEndo . arr $ scale $ c₂) . f
  f*g = genericiseRWDFV f ⋅ genericiseRWDFV g
   where (⋅) :: RWDfblFuncValue n a n -> RWDfblFuncValue n a n -> RWDfblFuncValue n a n 
         GenericRWDFV (RWDiffable fpcs) ⋅ GenericRWDFV (RWDiffable gpcs)
           = GenericRWDFV . RWDiffable $
               \d₀ -> let (rc₁, fmay) = fpcs d₀
                          (rc₂,gmay) = gpcs d₀
                      in (unsafePreRegionIntersect rc₁ rc₂, mulDi <$> fmay <*> gmay)
          where mulDi :: Differentiable n a n -> Differentiable n a n -> Differentiable n a n
                mulDi f@(AffinDiffable ef af) g@(AffinDiffable eg ag) = case ef<>eg of
                   IsDiffableEndo ->
                  {- let f' = lapply slf 1; g' = lapply slg 1
                     in case f'*g' of
                          0 -> AffinDiffableEndo $ const (aof*aog)
                          f'g' -> -} Differentiable $
                           \d -> let (fd,ϕf) = evalAffine af d
                                     (gd,ϕg) = evalAffine ag d
                                     jf = ϕf $ 1; jg = ϕg $ 1
                                     invf'g' = recip $ jf*jg
                                 in ( fd*gd
                                    , arr $ scale $ fd*jg + gd*jf
                                    , unsafe_dev_ε_δ "*" $ sqrt . (*invf'g') )
                   _ -> mulDi (genericiseDifferentiable f) (genericiseDifferentiable g)
                mulDi (Differentiable f) (Differentiable g)
                   = Differentiable $
                       \d -> let (c₁, jf, devf) = f d
                                 (c₂, jg, devg) = g d
                                 c = c₁*c₂; c₁² = c₁^2; c₂² = c₂^2
                                 h' = c₁*^jg ^+^ c₂*^jf
                                 in ( c
                                    , h'
                                    , \εc -> let rε = εc|$|1
                                                 c₁worst = sqrt $ c₁² + recip(1 + c₂²*rε^2)
                                                 c₂worst = sqrt $ c₂² + recip(1 + c₁²*rε^2)
                                             in scaleNorm (2*rε) (dualCoCoProduct jf jg)
                                                <> devf (scaleNorm (2*c₂worst) εc)
                                                <> devg (scaleNorm (2*c₁worst) εc)
                    -- TODO: add formal proof for this (or, if necessary, the correct form)
                                        )
                mulDi f g = mulDi (genericiseDifferentiable f) (genericiseDifferentiable g)
                
  negate = negateV
  abs = (RWDiffable absPW $~)
   where absPW a₀
          | a₀<0       = (negativePreRegion, pure desc)
          | otherwise  = (positivePreRegion, pure asc)
         desc = actuallyLinearEndo $ negateV id
         asc = actuallyLinearEndo id
  signum = (RWDiffable sgnPW $~)
   where sgnPW a₀
          | a₀<0       = (negativePreRegion, pure (const $ -1))
          | otherwise  = (positivePreRegion, pure (const 1))

instance ∀ n a . ( RealDimension n, Object (Differentiable n) a, SimpleSpace (Needle a) )
            => Fractional (RWDfblFuncValue n a n) where
  fromRational i = point $ fromRational i
  recip = postCompRW . RWDiffable $ \a₀ -> if a₀<0
                                    then (negativePreRegion, pure (Differentiable negp))
                                    else (positivePreRegion, pure (Differentiable posp))
   where negp x = (x'¹, (- x'¹^2) *^ id, unsafe_dev_ε_δ("1/"++showℝ x) δ)
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
         posp x = (x'¹, (- x'¹^2) *^ id, unsafe_dev_ε_δ("1/"++showℝ x) δ)
          where δ ε = let mph = ε*x^2/2
                          δ₀ = sqrt (mph^2 + ε*x^3) - mph
                      in if δ₀>0 then δ₀ else x
                x'¹ = recip x




instance ∀ n a . ( RealDimension n, Object (Differentiable n) a, SimpleSpace (Needle a) )
            => Floating (RWDfblFuncValue n a n) where
  pi = point pi
  
  exp = grwDfblFnValsFunc
    $ \x -> let ex = exp x
            in if ex*2 == ex  -- numerical trouble...
                then if x<0 then ( 0, zeroV, unsafe_dev_ε_δ("exp "++showℝ x) $ \ε -> log ε - x )
                            else ( ex, ex*^id
                                 , unsafe_dev_ε_δ("exp "++showℝ x) $ \_ -> 1e-300 :: n )
                else ( ex, ex *^ id, unsafe_dev_ε_δ("exp "++showℝ x)
                          $ \ε -> case acosh(ε/(2*ex) + 1) of
                                    δ | δ==δ      -> δ
                                      | otherwise -> log ε - x )
                 -- ε = e^(x+δ) − eˣ − eˣ·δ 
                 --   = eˣ·(e^δ − 1 − δ) 
                 --   ≤ eˣ · (e^δ − 1 + e^(-δ) − 1)
                 --   = eˣ · 2·(cosh(δ) − 1)
                 -- cosh(δ) ≥ ε/(2·eˣ) + 1
                 -- δ ≥ acosh(ε/(2·eˣ) + 1)
  log = postCompRW . RWDiffable $ \x -> if x>0
                                  then (positivePreRegion, pure (Differentiable lnPosR))
                                  else (negativePreRegion, notDefinedHere)
   where lnPosR x = ( log x, recip x *^ id, unsafe_dev_ε_δ("log "++showℝ x) $ \ε -> x * sqrt(1 - exp(-ε)) )
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
   where sqrtPosR x = ( sx, id ^/ (2*sx), unsafe_dev_ε_δ("sqrt "++showℝ x) $
                          \ε -> 2 * (s2 * sqrt sx^3 * sqrt ε + signum (ε*2-sx) * sx * ε) )
          where sx = sqrt x; s2 = sqrt 2
                 -- Exact inverse of O(δ²) remainder.
  
  sin = grwDfblFnValsFunc sinDfb
   where sinDfb x = ( sx, cx *^ id, unsafe_dev_ε_δ("sin "++showℝ x) δ )
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
                      
  cos = sin . (globalDiffable' (actuallyAffineEndo (pi/2) id) $~)
  
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
   where tanhDfb x = ( tnhx, id ^/ (cosh x^2), unsafe_dev_ε_δ("tan "++showℝ x) δ )
          where tnhx = tanh x
                c = (tnhx*2/pi)^2
                p = 1 + abs x/(2*pi)
                δ ε = p * (sqrt ε + ε * c)
                  -- copied from 'atan' definition. Empirically works safely, in fact
                  -- with quite a big margin. TODO: find a tighter definition.

  atan = grwDfblFnValsFunc atanDfb
   where atanDfb x = ( atnx, id ^/ (1+x^2), unsafe_dev_ε_δ("atan "++showℝ x) δ )
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
   where asinDefdR x = ( asinx, asin'x *^ id, unsafe_dev_ε_δ("asin "++showℝ x) δ )
          where asinx = asin x; asin'x = recip (sqrt $ 1 - x^2)
                c = 1 - x^2 
                δ ε = sqrt ε * c
                 -- Empirical, with epsEst upper bound.

  acos = postCompRW . RWDiffable $ \x -> if
                  | x < (-1)   -> (preRegionFromMinInfTo (-1), notDefinedHere)  
                  | x > 1      -> (preRegionToInfFrom 1, notDefinedHere)
                  | otherwise  -> (intervalPreRegion (-1,1), pure (Differentiable acosDefdR))
   where acosDefdR x = ( acosx, acos'x *^ id, unsafe_dev_ε_δ("acos "++showℝ x) δ )
          where acosx = acos x; acos'x = - recip (sqrt $ 1 - x^2)
                c = 1 - x^2
                δ ε = sqrt ε * c -- Like for asin – it's just a translation/reflection.

  asinh = grwDfblFnValsFunc asinhDfb
   where asinhDfb x = ( asinhx, id ^/ sqrt(1+x^2), unsafe_dev_ε_δ("asinh "++showℝ x) δ )
          where asinhx = asinh x
                δ ε = abs x * sqrt((1 - exp(-ε))*0.8 + ε^2/(3*abs x + 1)) + sqrt(ε/(abs x+0.5))
                 -- Empirical, modified from log function (the area hyperbolic sine
                 -- resembles two logarithmic lobes), with epsEst-checked lower bound.
  
  acosh = postCompRW . RWDiffable $ \x -> if x>1
                                   then (preRegionToInfFrom 1, pure (Differentiable acoshDfb))
                                   else (preRegionFromMinInfTo 1, notDefinedHere)
   where acoshDfb x = ( acosh x, id ^/ sqrt(x^2 - 1), unsafe_dev_ε_δ("acosh "++showℝ x) δ )
          where δ ε = (2 - 1/sqrt x) * (s2 * sqrt sx^3 * sqrt(ε/s2) + signum (ε*s2-sx) * sx * ε/s2) 
                sx = sqrt(x-1)
                s2 = sqrt 2
                 -- Empirical, modified from sqrt function – the area hyperbolic cosine
                 -- strongly resembles \x -> sqrt(2 · (x-1)).
                    
  atanh = postCompRW . RWDiffable $ \x -> if
                  | x < (-1)   -> (preRegionFromMinInfTo (-1), notDefinedHere)  
                  | x > 1      -> (preRegionToInfFrom 1, notDefinedHere)
                  | otherwise  -> (intervalPreRegion (-1,1), pure (Differentiable atnhDefdR))
   where atnhDefdR x = ( atanh x, recip(1-x^2) *^ id, unsafe_dev_ε_δ("atanh "++showℝ x) $ \ε -> sqrt(tanh ε)*(1-abs x) )
                 -- Empirical, with epsEst upper bound.
  



-- $definitionRegionOps
-- Because the agents of 'RWDiffable' aren't really values in /Hask/, you can't use
-- the standard comparison operators on them, nor the built-in syntax of guards
-- or if-statements.
-- 
-- However, because this category allows functions to be undefined in some region,
-- such decisions can be faked quite well: '?->' restricts a function to
-- some region, by simply marking it undefined outside, and '?|:' replaces these
-- regions with values from another function.
-- 
-- Example: define a function that is compactly supported on the interval ]-1,1[,
-- i.e. exactly zero everywhere outside.
--
-- @
-- Graphics.Dynamic.Plot.R2> plotWindow [fnPlot (\\x -> -1 '?<' x '?<' 1 '?->' cos (x*pi/2)^2 '?|:' 0)]
-- @
-- 
-- <<images/examples/DiffableFunction-plots/Hann-window.png>>
-- 
-- Note that it may not be necessary to restrict explicitly: for instance if a
-- square root appears somewhere in an expression, then the expression is automatically
-- restricted so that the root has a positive argument!
-- 
-- @
-- Graphics.Dynamic.Plot.R2> plotWindow [fnPlot (\\x -> sqrt x '?|:' -sqrt (-x))]
-- @
-- 
-- <<images/examples/DiffableFunction-plots/safe-sqrt.png>>
  
infixr 4 ?->
-- | Require the LHS to be defined before considering the RHS as result.
--   This works analogously to the standard `Control.Applicative.Applicative` method
-- 
--   @
--   ('Control.Applicative.*>') :: Maybe a -> Maybe b -> Maybe b
--   Just _ 'Control.Applicative.*>' a = a
--   _      'Control.Applicative.*>' a = Nothing
--   @
(?->) :: ( RealDimension n, Object (Differentiable n) a, Object (Differentiable n) b
         , Object (Differentiable n) c )
      => RWDfblFuncValue n c a -> RWDfblFuncValue n c b -> RWDfblFuncValue n c b
ConstRWDFV _ ?-> f = f
RWDFV_IdVar ?-> f = f
GenericRWDFV (RWDiffable r) ?-> ConstRWDFV c = GenericRWDFV (RWDiffable s)
 where s x₀ = case r x₀ of
                (rd, Just q)  -> (rd, return $ const c)
                (rd, Nothing) -> (rd, empty)
GenericRWDFV (RWDiffable f) ?-> GenericRWDFV (RWDiffable g) = GenericRWDFV (RWDiffable h)
 where h x₀ = case f x₀ of
                (rf, Just _) | (rg, q) <- g x₀
                        -> (unsafePreRegionIntersect rf rg, q)
                (rf, Nothing) -> (rf, empty)
c ?-> f = c ?-> genericiseRWDFV f

positiveRegionalId :: RealDimension n => RWDiffable n n n
positiveRegionalId = RWDiffable $ \x₀ ->
       if x₀ > 0 then (positivePreRegion, pure . AffinDiffable IsDiffableEndo $ id)
                 else (negativePreRegion, notDefinedHere)

infixl 5 ?> , ?<
-- | Return the RHS, if it is less than the LHS.
--   (Really the purpose is just to compare the values, but returning one of them
--   allows chaining of comparison operators like in Python.)
--   Note that less-than comparison is <http://www.paultaylor.eu/ASD/ equivalent>
--   to less-or-equal comparison, because there is no such thing as equality.
(?>) :: ( RealDimension n, Object (Differentiable n) a, SimpleSpace (Needle a) )
           => RWDfblFuncValue n a n -> RWDfblFuncValue n a n -> RWDfblFuncValue n a n
a ?> b = (positiveRegionalId $~ a-b) ?-> b

-- | Return the RHS, if it is greater than the LHS.
(?<) :: ( RealDimension n, Object (Differentiable n) a, SimpleSpace (Needle a) )
           => RWDfblFuncValue n a n -> RWDfblFuncValue n a n -> RWDfblFuncValue n a n
ConstRWDFV a ?< RWDFV_IdVar = GenericRWDFV . RWDiffable $
       \x₀ -> if a < x₀ then ( preRegionToInfFrom a
                             , pure . AffinDiffable IsDiffableEndo $ id)
                        else (preRegionFromMinInfTo a, notDefinedHere)
RWDFV_IdVar ?< ConstRWDFV a = GenericRWDFV . RWDiffable $
       \x₀ -> if x₀ < a then ( preRegionFromMinInfTo a
                             , pure . AffinDiffable IsDiffableEndo $ const a)
                        else (preRegionToInfFrom a, notDefinedHere)
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
(?|:) :: ( RealDimension n, Object (Differentiable n) a, Object (Differentiable n) b )
      => RWDfblFuncValue n a b -> RWDfblFuncValue n a b -> RWDfblFuncValue n a b
ConstRWDFV c ?|: _ = ConstRWDFV c
RWDFV_IdVar ?|: _ = RWDFV_IdVar
GenericRWDFV (RWDiffable f) ?|: ConstRWDFV c = GenericRWDFV (RWDiffable h)
 where h x₀ = case f x₀ of
                (rd, Just q) -> (rd, Just q)
                (rd, Nothing) -> (rd, Just $ const c)
GenericRWDFV (RWDiffable f) ?|: GenericRWDFV (RWDiffable g) = GenericRWDFV (RWDiffable h)
 where h x₀ = case f x₀ of
                (rf, Just q) -> (rf, pure q)
                (rf, Nothing) | (rg, q) <- g x₀
                        -> (unsafePreRegionIntersect rf rg, q)
c ?|: f = c ?|: genericiseRWDFV f

-- | Replace the regions in which the first function is undefined with values
--   from the second function.
backupRegions :: (RealDimension n, Object (Differentiable n) a, Object (Differentiable n) b)
      => RWDiffable n a b -> RWDiffable n a b -> RWDiffable n a b
backupRegions (RWDiffable f) (RWDiffable g) = RWDiffable h
 where h x₀ = case f x₀ of
                (rf, q@(Just _)) -> (rf, q)
                (rf, Nothing) | (rg, q) <- g x₀
                        -> (unsafePreRegionIntersect rf rg, q)





-- | Like 'Data.VectorSpace.lerp', but gives a differentiable function
--   instead of a Hask one.
lerp_diffable :: ∀ m s . ( LinearSpace m, RealDimension s, Object (Differentiable s) m )
      => m -> m -> Differentiable s s m
lerp_diffable = case ( linearManifoldWitness @m
                     , dualSpaceWitness @m
                     , smfdWBoundWitness @m) of
     (LinearManifoldWitness, DualSpaceWitness, OpenManifoldWitness)
         -> \a b -> actuallyAffine a . arr $ flipBilin scale $ b.-.a








