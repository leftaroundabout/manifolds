-- |
-- Module      : Main
-- Copyright   : (c) Justus Sagemüller 2017
-- License     : GPL v3
-- 
-- Maintainer  : (@) sagemueller $ geo.uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 

{-# LANGUAGE OverloadedLists #-}

module Main where

import Data.Manifold.Types
import Data.Manifold.TreeCover
import Data.Manifold.Web
import Data.Manifold.Web.Internal
import Data.VectorSpace
import Math.LinearMap.Category

import Test.Tasty
import Test.Tasty.HUnit

import Data.Foldable (toList)
import Control.Arrow
import Control.Lens


main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests"
 [ testGroup "Graph structure of webs"
  [ testCase "Manually-defined empty web."
    $ toList (fst $ toGraph emptyWeb) @?= []
  , testCase "Manually-defined single-point web."
    $ toList (fst $ toGraph singletonWeb) @?= [[]]
  , testCase "Manually-defined simple triangular web."
    $ toList (fst $ toGraph triangularWeb) @?= [[1,2],[0,2],[0,1]]
  , testCase "Manually-defined simple quadratic web."
    $ toList (fst $ toGraph quadraticWeb) @?= [[1,2],[0,3],[0,3],[1,2]]
  , testCase "Envi-aware traversal over simple quadratic web."
    $ toList (fst . toGraph $ dummyWebFmap quadraticWeb) @?= [[1,2],[0,3],[0,3],[1,2]]
  , testCase "Next-neighbours in empty web."
    $ toList (nextNeighbours emptyWeb) @?= []
  , testCase "Next-neighbours in single-point web."
    $ toList (nextNeighbours singletonWeb) @?= [[]]
  , testCase "Next-neighbours in simple triangular web."
    $ toList (nextNeighbours triangularWeb) @?= [[]]
  , testCase "Next-neighbours in simple quadratic web."
    $ toList (nextNeighbours quadraticWeb) @?=
     [[(1,()),(2,())],[(0,()),(3,())],[(0,()),(3,())],[(1,()),(2,())]]
  ]
 ]

emptyWeb, singletonWeb, triangularWeb, quadraticWeb :: PointsWeb ℝ⁰ ()

emptyWeb = PointsWeb $ PlainLeaves []

singletonWeb = PointsWeb $
         PlainLeaves [ (o, Neighbourhood () mempty euclideanNorm Nothing) ]

triangularWeb = PointsWeb $
         PlainLeaves [ (o, Neighbourhood () [1,2] euclideanNorm Nothing)
                     , (o, Neighbourhood () [-1,1] euclideanNorm Nothing)
                     , (o, Neighbourhood () [-2,-1] euclideanNorm Nothing)
                     ]

quadraticWeb = PointsWeb $
        OverlappingBranches 6 (Shade o mempty) (pure . DBranch o $ Hourglass
         (PlainLeaves [ (o, Neighbourhood () [1,2] euclideanNorm Nothing)
                      , (o, Neighbourhood () [-1,2] euclideanNorm Nothing)
                      ])
         (PlainLeaves [ (o, Neighbourhood () [-2,1] euclideanNorm Nothing)
                      , (o, Neighbourhood () [-2,-1] euclideanNorm Nothing)
                      ])
         )


o = zeroV :: ℝ⁰

dummyWebFmap :: PointsWeb ℝ⁰ a -> PointsWeb ℝ⁰ a
dummyWebFmap = localFmapWeb $ \info -> info^.thisNodeData

nextNeighbours :: PointsWeb ℝ⁰ a -> PointsWeb ℝ⁰ [(Int, a)]
nextNeighbours = localFmapWeb $
     \info -> second (\(_, ngb)->ngb^.thisNodeData) <$> info^.nodeNeighbours
