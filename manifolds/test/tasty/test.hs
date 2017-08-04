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
  , testCase "Direct neighbours in empty web."
    $ toList (directNeighbours emptyWeb) @?= []
  , testCase "Direct neighbours in single-point web."
    $ toList (directNeighbours singletonWeb) @?= [[]]
  , testCase "Direct neighbours in simple triangular web."
    $ toList (directNeighbours triangularWeb) @?= [[1,2],[0,2],[0,1]]
  , testCase "Direct neighbours in simple quadratic web."
    $ toList (directNeighbours quadraticWeb) @?= [[1,2],[0,3],[0,3],[1,2]]
  , testCase "Direct neighbours in unsymmetric web."
    $ toList (directNeighbours unsymmetricWeb)
         @?= [[5],[2,3,0],[4,3],[4,2,5,1],[5],[0,1,6],[5],[4,6]]
  , testCase "Next-neighbours in simple quadratic web."
    $ toList (nextNeighbours quadraticWeb) @?=
      [ [(1,[0,3]),(2,[0,3])]
      , [(0,[1,2]),(3,[1,2])]
      , [(0,[1,2]),(3,[1,2])]
      , [(1,[0,3]),(2,[0,3])] ]
  , testCase "Layers in a nested web"
    $ toList (pointsLocInEnvi nestedWeb) @?=
      [ [((1, 朳[(o,朳[            {-LEAF-} (o,朳[])                              ])]), 0)
        ,((2, 朳[(o,朳[      {-    {-    -} {-    -}-} (o,朳[(o,朳[]),(o,朳[])])  ])]), 0)
        ,((4, 朳[(o,朳[(o,朳[(o,朳[(o,朳[]),(o,朳[])]),(o,朳[(o,朳[]),(o,朳[])])])])]), 0)
        ]
      , [((1, 朳[(o,朳[            (o,朳[]) {-LEAF-}                              ])]), 1)
        ,((2, 朳[(o,朳[      {-    {-    -} {-    -}-} (o,朳[(o,朳[]),(o,朳[])])  ])]), 0)
        ,((4, 朳[(o,朳[(o,朳[(o,朳[(o,朳[]),(o,朳[])]),(o,朳[(o,朳[]),(o,朳[])])])])]), 0)
        ]
      , [((1, 朳[(o,朳[                                      {-LEAF-} (o,朳[])    ])]), 0)
        ,((2, 朳[(o,朳[      (o,朳[(o,朳[]),(o,朳[])]) {-    {-    -} {-    -}-}  ])]), 2)
        ,((4, 朳[(o,朳[(o,朳[(o,朳[(o,朳[]),(o,朳[])]),(o,朳[(o,朳[]),(o,朳[])])])])]), 0)
        ]
      , [((1, 朳[(o,朳[                                      (o,朳[]) {-LEAF-}    ])]), 1)
        ,((2, 朳[(o,朳[      (o,朳[(o,朳[]),(o,朳[])]) {-    {-    -} {-    -}-}  ])]), 2)
        ,((4, 朳[(o,朳[(o,朳[(o,朳[(o,朳[]),(o,朳[])]),(o,朳[(o,朳[]),(o,朳[])])])])]), 0)
        ]
      , [((1, 朳[(o,朳[            {-LEAF-} (o,朳[])                              ])]), 0)
        ,((2, 朳[(o,朳[      {-    {-    -} {-    -}-} (o,朳[(o,朳[]),(o,朳[])])  ])]), 0)
        ,((4, 朳[(o,朳[(o,朳[(o,朳[(o,朳[]),(o,朳[])]),(o,朳[(o,朳[]),(o,朳[])])])])]), 4)
        ]
      , [((1, 朳[(o,朳[            (o,朳[]) {-LEAF-}                              ])]), 1)
        ,((2, 朳[(o,朳[      {-    {-    -} {-    -}-} (o,朳[(o,朳[]),(o,朳[])])  ])]), 0)
        ,((4, 朳[(o,朳[(o,朳[(o,朳[(o,朳[]),(o,朳[])]),(o,朳[(o,朳[]),(o,朳[])])])])]), 4)
        ]
      , [((1, 朳[(o,朳[                                      {-LEAF-} (o,朳[])    ])]), 0)
        ,((2, 朳[(o,朳[      (o,朳[(o,朳[]),(o,朳[])]) {-    {-    -} {-    -}-}  ])]), 2)
        ,((4, 朳[(o,朳[(o,朳[(o,朳[(o,朳[]),(o,朳[])]),(o,朳[(o,朳[]),(o,朳[])])])])]), 4)
        ]
      , [((1, 朳[(o,朳[                                      (o,朳[]) {-LEAF-}    ])]), 1)
        ,((2, 朳[(o,朳[      (o,朳[(o,朳[]),(o,朳[])]) {-    {-    -} {-    -}-}  ])]), 2)
        ,((4, 朳[(o,朳[(o,朳[(o,朳[(o,朳[]),(o,朳[])]),(o,朳[(o,朳[]),(o,朳[])])])])]), 4)
        ]
      ]
  , testCase "Next-neighbours in nested web."
    $ toList (nextNeighbours nestedWeb) @?=
        [ [ (1,[0,3,4]), (2,[0,3])                ]
        , [ (0,[1,2])  , (3,[1,6])  , (4,[1,5,6]) ]
        , [ (0,[1,2])  , (3,[1,6])                ] 
        , [ (1,[0,3,4]), (6,[3,4,7])              ]
        , [ (1,[0,3,4]), (5,[4,7])  , (6,[3,4,7]) ]
        , [ (4,[1,5,6]), (7,[5,6])                ]
        , [ (3,[1,6])  , (4,[1,5,6]), (7,[5,6])   ]
        , [ (5,[4,7])  , (6,[3,4,7])              ] ]
  , testCase "Next-neighbours in unsymmetric web."
    $ toList (nextNeighbours unsymmetricWeb) @?=
       [ [ (5,[0,1,6])                                          ]
       , [ (2,[4,3])  , (3,[4,2,5,1]), (0,[5])                  ]
       , [ (4,[5])    , (3,[4,2,5,1])                           ]
       , [ (4,[5])    , (2,[4,3])    , (5,[0,1,6]), (1,[2,3,0]) ]
       , [ (5,[0,1,6])                                          ]
       , [ (0,[5])    , (1,[2,3,0])  , (6,[5])                  ]
       , [ (5,[0,1,6])                                          ]
       , [ (4,[5])    , (6,[5])                                 ] ]
  ]
 ]

emptyWeb, singletonWeb, triangularWeb, quadraticWeb, nestedWeb, unsymmetricWeb
    :: PointsWeb ℝ⁰ ()

emptyWeb = PointsWeb $ PlainLeaves []

singletonWeb = PointsWeb $
         PlainLeaves [ (o, Neighbourhood () mempty euclideanNorm Nothing) ]

triangularWeb = PointsWeb $
         PlainLeaves [ (o, Neighbourhood () [1,2] euclideanNorm Nothing)
                     , (o, Neighbourhood () [-1,1] euclideanNorm Nothing)
                     , (o, Neighbourhood () [-2,-1] euclideanNorm Nothing)
                     ]

quadraticWeb = PointsWeb $
        OverlappingBranches 4 (Shade o mempty) (pure . DBranch o $ Hourglass
         (PlainLeaves [ (o, Neighbourhood () [1,2] euclideanNorm Nothing)
                      , (o, Neighbourhood () [-1,2] euclideanNorm Nothing)
                      ])
         (PlainLeaves [ (o, Neighbourhood () [-2,1] euclideanNorm Nothing)
                      , (o, Neighbourhood () [-2,-1] euclideanNorm Nothing)
                      ])
         )

nestedWeb = PointsWeb $
        OverlappingBranches 8 (Shade o mempty) (pure . DBranch o $ Hourglass
         (OverlappingBranches 4 (Shade o mempty) (pure . DBranch o $ Hourglass
          (PlainLeaves [ (o, Neighbourhood () [1,2] euclideanNorm Nothing)
                       , (o, Neighbourhood () [-1,2,3] euclideanNorm Nothing)
                       ])
          (PlainLeaves [ (o, Neighbourhood () [-2,1] euclideanNorm Nothing)
                       , (o, Neighbourhood () [-2,3] euclideanNorm Nothing)
                       ])
         ))
         (OverlappingBranches 4 (Shade o mempty) (pure . DBranch o $ Hourglass
          (PlainLeaves [ (o, Neighbourhood () [-3,1,2] euclideanNorm Nothing)
                       , (o, Neighbourhood () [-1,2] euclideanNorm Nothing)
                       ])
          (PlainLeaves [ (o, Neighbourhood () [-3,-2,1] euclideanNorm Nothing)
                       , (o, Neighbourhood () [-2,-1] euclideanNorm Nothing)
                       ])
         ))
        )

unsymmetricWeb = PointsWeb $
        OverlappingBranches 8 (Shade o mempty) (pure . DBranch o $ Hourglass
         (OverlappingBranches 4 (Shade o mempty) (pure . DBranch o $ Hourglass
          (PlainLeaves [ (o, Neighbourhood () [5] euclideanNorm Nothing)
                       , (o, Neighbourhood () [1,2,-1] euclideanNorm Nothing)
                       ])
          (PlainLeaves [ (o, Neighbourhood () [2,1] euclideanNorm Nothing)
                       , (o, Neighbourhood () [1,-1,2,-2] euclideanNorm Nothing)
                       ])
         ))
         (OverlappingBranches 4 (Shade o mempty) (pure . DBranch o $ Hourglass
          (PlainLeaves [ (o, Neighbourhood () [1] euclideanNorm Nothing)
                       , (o, Neighbourhood () [-5,-4,1] euclideanNorm Nothing)
                       ])
          (PlainLeaves [ (o, Neighbourhood () [-1] euclideanNorm Nothing)
                       , (o, Neighbourhood () [-3,-1] euclideanNorm Nothing)
                       ])
         ))
        )



o = zeroV :: ℝ⁰

dummyWebFmap :: PointsWeb ℝ⁰ a -> PointsWeb ℝ⁰ a
dummyWebFmap = localFmapWeb $ \info -> info^.thisNodeData

directNeighbours :: PointsWeb ℝ⁰ () -> PointsWeb ℝ⁰ [WebNodeId]
directNeighbours = localFmapWeb $
     \info -> fst <$> info^.nodeNeighbours

nextNeighbours :: PointsWeb ℝ⁰ a -> PointsWeb ℝ⁰ [(WebNodeId, [WebNodeId])]
nextNeighbours = webLocalInfo >>> localFmapWeb `id`
     \info -> [ ( nId ≡! nId' ≡! (nInfo^.thisNodeId) ≡! (nInfo'^.thisNodeId)
                , (fst<$>nInfo^.nodeNeighbours) ≡! (fst<$>nInfo'^.nodeNeighbours) )
              | ((nId,(_,nInfo)),(nId',(_,nInfo')))
                    <- zip (info^.nodeNeighbours)
                           (info^.thisNodeData.nodeNeighbours)
              ]

pointsLocInEnvi :: PointsWeb ℝ⁰ a -> PointsWeb ℝ⁰ [((Int, Trees ℝ⁰), WebNodeId)]
pointsLocInEnvi = fmapNodesInEnvi $
     \(NodeInWeb (_, orig) env)
         -> fmap (const $ first ((nLeaves&&&onlyNodes) . fmap (const ())) <$> env) orig


infixl 4 ≡!
(≡!) :: (Eq a, Show a) => a -> a -> a
x ≡! y | x==y       = x
       | otherwise  = error $ show x++" ≠ "++show y
