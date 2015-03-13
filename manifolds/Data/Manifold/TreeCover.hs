-- |
-- Module      : Data.Manifold.TreeCover
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
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE RankNTypes               #-}
{-# LANGUAGE TupleSections            #-}
{-# LANGUAGE ParallelListComp         #-}
{-# LANGUAGE ConstraintKinds          #-}
{-# LANGUAGE PatternGuards            #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE ScopedTypeVariables      #-}
{-# LANGUAGE RecordWildCards          #-}
{-# LANGUAGE DataKinds                #-}


module Data.Manifold.TreeCover (
         Shade(..), pointsShades, ShadeTree(..), fromLeafPoints
    ) where


import Data.List
import Data.Maybe
import qualified Data.Map as Map
import Data.Semigroup
import Data.Ord (comparing)
import Data.Fixed

import Data.VectorSpace
import Data.LinearMap
import Data.LinearMap.HerMetric
import Data.AffineSpace
import Data.Basis
import Data.Complex hiding (magnitude)
import Data.Void
import Data.Tagged

import Data.Manifold.Types
import Data.Manifold.PseudoAffine

import qualified Prelude as Hask
import qualified Control.Monad as Hask

import Control.Category.Constrained.Prelude hiding ((^))
import Control.Arrow.Constrained
import Control.Monad.Constrained
import Data.Foldable.Constrained

import GHC.TypeLits



-- | A 'Shade' is a very crude description of a region within a manifold. It
--   can be interpreted as either an ellipsoid shape, or as the Gaussian peak
--   of a normal distribution (use <http://hackage.haskell.org/package/manifold-random>
--   for actually sampling from that distribution).
-- 
--   For a /precise/ description of an arbitrarily-shaped connected subset of a manifold,
--   there is 'Region', whose implementation is vastly more complex.
data Shade x = Shade { shadeCtr :: x
                     , shadeExpanse :: HerMetric' (PseudoDiff x) }

subshadeId :: (PseudoAffine x, HasMetric (PseudoDiff x), Scalar (PseudoDiff x) ~ ℝ)
                  => Shade x -> x -> Int
subshadeId (Shade c expa) = \x
             -> case x .-~. c of
                 Option (Just v) -> let (iu,vl) = maximumBy (comparing $ abs . snd)
                                                   $ zip [0,2..] (map (v <.>^) expvs)
                                    in iu + if vl>0 then 1 else 0
                 _ -> -1
                 
 where expvs = eigenCoSpan expa


-- | Attempt to find a 'Shade' that &#x201c;covers&#x201d; the given points.
--   At least in an affine space (and thus locally in any manifold), this can be used to
--   estimate the parameters of a normal distribution from which some points were
--   sampled.
-- 
--   For /nonconnected/ manifolds it will be necessary to yield separate shades
--   for each connected component. And for an empty input list, there is no shade!
--   Hence the list result.
pointsShades :: (PseudoAffine x, HasMetric (PseudoDiff x), Scalar (PseudoDiff x) ~ ℝ)
                 => [x] -> [Shade x]
pointsShades = map snd . pointsShades'

pointsShades' :: (PseudoAffine x, HasMetric (PseudoDiff x), Scalar (PseudoDiff x) ~ ℝ)
                 => [x] -> [([x], Shade x)]
pointsShades' [] = []
pointsShades' ps@(p₀:_) = case expa of 
                           Option (Just e) -> (ps,Shade ctr e)
                                              : pointsShades' unreachable
                           _ -> pointsShades' inc'd ++ pointsShades' unreachable
 where (ctr,(inc'd,unreachable))
             = foldl' ( \(acc, (rb,nr)) (i,p)
                           -> case p.-~.acc of 
                               Option (Just δ) -> (acc .+~^ δ^/i, (p:rb, nr))
                               _ -> (acc, (rb, p:nr)) )
                     (p₀, mempty)
                     ( zip [1..] ps )
       expa = ( (^/ fromIntegral(length ps)) . sumV . map projector' )
              <$> mapM (.-~.ctr) ps
       
  
-- | Check the statistical likelyhood of a point being within a shade.
occlusion :: (PseudoAffine x, HasMetric (PseudoDiff x)
             , s ~ (Scalar (PseudoDiff x)), RealDimension s )
                => Shade x -> x -> s
occlusion (Shade p₀ δ) = occ
 where occ p = case p .-~. p₀ of
         Option(Just vd) -> exp . negate $ metricSq δinv vd
         _               -> zeroV
       δinv = recipMetric δ



data ShadeTree x = PlainLeaves [x]
                 | DisjointBranches Int [ShadeTree x]
                 | OverlappingBranches Int (Shade x) [ShadeTree x]

fromLeafPoints :: (PseudoAffine x, HasMetric (PseudoDiff x), Scalar (PseudoDiff x) ~ ℝ)
                 => [x] -> ShadeTree x
fromLeafPoints = \xs -> case pointsShades' xs of
                     [] -> PlainLeaves []
                     [(_,rShade)] -> OverlappingBranches (length xs)
                                                         rShade
                                                         (branches rShade xs)
                     partitions -> DisjointBranches (length xs)
                                    $ map (\(xs',pShade) ->
                                        OverlappingBranches (length xs')
                                                            pShade
                                                            (branches pShade xs'))
                                       partitions
 where branches shade = map fromLeafPoints
                        . foldr (\p -> cons2nth p $ subshadeId shade p) []
                                           

cons2nth :: a -> Int -> [[a]] -> [[a]]
cons2nth _ n l | n<0 = l
cons2nth x 0 (c:r) = (x:c):r
cons2nth x n [] = cons2nth x n [[]]
cons2nth x n (l:r) = l : cons2nth x (n-1) r



data Simplex x n where
   ZeroSimplex :: x -> Simplex x 0
   Simplex :: x -> Simplex x (n-1) -> Simplex x n

newtype Triangulation x n = Triangulation { getTriangulation :: [Simplex x n] }


splxVertices :: Simplex x n -> [x]
splxVertices (ZeroSimplex x) = [x]
splxVertices (Simplex x s') = x : splxVertices s'


data Branchwise :: * -> (Nat -> *) -> Nat -> * where
   Branchwise :: { branchResult :: r n
                 , bResBounary :: r (n-1)
                 , branchBoundary :: ShadeTree x
                 } -> Branchwise x r n


triangBranches :: (PseudoAffine x, HasMetric (PseudoDiff x), Scalar (PseudoDiff x) ~ ℝ)
                 => ShadeTree x -> Branchwise x (Triangulation x) n
triangBranches _ = undefined

triangulate :: (PseudoAffine x, HasMetric (PseudoDiff x), Scalar (PseudoDiff x) ~ ℝ)
                 => ShadeTree x -> Triangulation x n
triangulate = branchResult . triangBranches

tringComplete :: (PseudoAffine x, HasMetric (PseudoDiff x), Scalar (PseudoDiff x) ~ ℝ)
                 => Triangulation x (n-1) -> Triangulation x n -> Triangulation x n
tringComplete (Triangulation trr) (Triangulation tr) = undefined
 where 
       bbSimplices = Map.fromList [(i, Left s) | s <- tr | i <- [0::Int ..] ]
       bbVertices =       [(i, splxVertices s) | s <- tr | i <- [0::Int ..] ]

