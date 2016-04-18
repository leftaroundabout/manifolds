-- |
-- Module      : Data.Manifold.Web
-- Copyright   : (c) Justus Sagemüller 2016
-- License     : GPL v3
-- 
-- Maintainer  : (@) sagemueller $ geo.uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE ParallelListComp           #-}
{-# LANGUAGE UnicodeSyntax              #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE PatternGuards              #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE ViewPatterns               #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE LiberalTypeSynonyms        #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE DataKinds                  #-}


module Data.Manifold.Web where


import Data.List hiding (filter, all, elem, sum, foldr1)
import Data.Maybe
import qualified Data.Set as Set
import qualified Data.Vector as Arr
import qualified Data.Vector.Unboxed as UArr
import Data.List.NonEmpty (NonEmpty(..))
import Data.List.FastNub
import qualified Data.List.NonEmpty as NE
import Data.Semigroup
import Data.Ord (comparing)
import Control.DeepSeq

import Data.VectorSpace
import Data.AffineSpace
import Data.LinearMap
import Data.LinearMap.HerMetric
import Data.LinearMap.Category
import Data.AffineSpace
import Data.Basis
import Data.Complex hiding (magnitude)
import Data.Void
import Data.Tagged
import Data.Proxy

import Data.SimplicialComplex
import Data.Manifold.Types
import Data.Manifold.Types.Primitive ((^), empty)
import Data.Manifold.PseudoAffine
import Data.Function.Differentiable
import Data.Function.Differentiable.Data
import Data.Manifold.TreeCover
    
import Data.Embedding
import Data.CoNat

import qualified Prelude as Hask hiding(foldl, sum, sequence)
import qualified Control.Applicative as Hask
import qualified Control.Monad       as Hask hiding(forM_, sequence)
import Data.Functor.Identity
import Control.Monad.Trans.State
import Control.Monad.Trans.Writer
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Class
import qualified Data.Foldable       as Hask
import Data.Foldable (all, elem, toList, sum, foldr1)
import qualified Data.Traversable as Hask
import Data.Traversable (forM)

import qualified Numeric.LinearAlgebra.HMatrix as HMat

import Control.Category.Constrained.Prelude hiding
     ((^), all, elem, sum, forM, Foldable(..), foldr1, Traversable, traverse)
import Control.Arrow.Constrained
import Control.Monad.Constrained hiding (forM)
import Data.Foldable.Constrained
import Data.Traversable.Constrained (traverse)

import GHC.Generics (Generic)


type WebNodeId = Int
type NeighbourRefs = UArr.Vector WebNodeId

data PointsWeb x y = PointsWeb {
       _webNodeRsc :: ShadeTree x
     , _webNodeAssocData :: Arr.Vector (y, NeighbourRefs)
     }



fromShadeTree_auto :: ∀ x . WithField ℝ Manifold x => ShadeTree x -> PointsWeb x ()
fromShadeTree_auto = fromShaded (recipMetric . _shadeExpanse) . constShaded ()

fromShadeTree :: ∀ x . WithField ℝ Manifold x
     => (Shade x -> Metric x) -> ShadeTree x -> PointsWeb x ()
fromShadeTree mf = fromShaded mf . constShaded ()

fromShaded :: ∀ x y . WithField ℝ Manifold x
     => (Shade x -> Metric x) -- ^ Local scalar-product generator. You can always
                              --   use @'recipMetric' . '_shadeExpanse'@ (but this
                              --   may give distortions compared to an actual
                              --   Riemannian metric).
     -> x`Shaded`y            -- ^ Source tree.
     -> PointsWeb x y
fromShaded metricf shd = PointsWeb shd' assocData 
 where shd' = stripShadedUntopological shd
       assocData = Hask.foldMap locMesh $ twigsWithEnvirons shd
       
       locMesh :: ((Int, ShadeTree (x`WithAny`y)), [(Int, ShadeTree (x`WithAny`y))])
                   -> Arr.Vector (y, NeighbourRefs)
       locMesh ((i₀, locT), neighRegions) = Arr.map findNeighbours locLeaves
        where locLeaves = Arr.map (first (+i₀)) . Arr.indexed . Arr.fromList
                                          $ onlyLeaves locT
              findNeighbours :: (Int, x`WithAny`y) -> (y, NeighbourRefs)
              findNeighbours (i, WithAny y x)
                         = (y, UArr.fromList $ fst<$>execState seek mempty)
               where seek = do
                        Hask.forM_ locLeaves $ \(iNgb, WithAny _ xNgb) ->
                           when (iNgb/=i) `id`do
                              let (Option (Just v)) = xNgb.-~.x
                              oldNgbs <- get
                              when (all (\(_,(_,nw)) -> nw<.>^v < 1) oldNgbs) `id`do
                                 let w = w₀ ^/ (w₀<.>^v)
                                      where w₀ = toDualWith locRieM v
                                 put $ (iNgb, (v,w))
                                       : [ neighbour
                                         | neighbour@(_,(nv,_))<-oldNgbs
                                                   , w<.>^nv < 1
                                         ]
              
              locRieM :: Metric x
              locRieM = case pointsCovers . map _topological
                                  $ onlyLeaves locT
                                   ++ Hask.foldMap (onlyLeaves . snd) neighRegions of
                          [sh₀] -> metricf sh₀

indexWeb :: WithField ℝ Manifold x => PointsWeb x y -> WebNodeId -> Option (x,y)
indexWeb (PointsWeb rsc assocD) i
  | i>=0, i<Arr.length assocD
  , Right (_,x) <- indexShadeTree rsc i  = pure (x, fst (assocD Arr.! i))
  | otherwise                            = empty

webEdges :: ∀ x y . WithField ℝ Manifold x
            => PointsWeb x y -> [((x,y), (x,y))]
webEdges web@(PointsWeb rsc assoc) = (lookId***lookId) <$> toList allEdges
 where allEdges :: Set.Set (WebNodeId,WebNodeId)
       allEdges = Hask.foldMap (\(i,(_,ngbs))
                    -> Set.fromList [(min i i', max i i')
                                    | i'<-UArr.toList ngbs ]
                               ) $ Arr.indexed assoc
       lookId i | Option (Just xy) <- indexWeb web i  = xy
