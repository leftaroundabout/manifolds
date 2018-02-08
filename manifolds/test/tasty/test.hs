-- |
-- Module      : Main
-- Copyright   : (c) Justus Sagemüller 2017
-- License     : GPL v3
-- 
-- Maintainer  : (@) sagemueller $ geo.uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 

{-# LANGUAGE OverloadedLists, TypeFamilies, FlexibleContexts, UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE TypeOperators, TypeApplications, ScopedTypeVariables, UnicodeSyntax #-}

module Main where

import Data.Manifold.Types
import Data.Manifold.PseudoAffine
import Data.Manifold.TreeCover
import Data.Manifold.Web
import Data.Manifold.Web.Internal
import Data.Manifold.Function.LocalModel
import Data.VectorSpace
import Linear.V2 (V2(V2))
import Math.LinearMap.Category
import Prelude hiding (id, fst, snd)
import Control.Category.Constrained (id)
import Control.Arrow.Constrained (fst,snd)

import Test.Tasty
import Test.Tasty.HUnit
import qualified Test.Tasty.QuickCheck as QC
import Test.Tasty.QuickCheck ((==>))

import Data.Foldable (toList)
import Data.List (nub)
import qualified Data.Graph as Graph
import qualified Data.Set as Set
import Control.Arrow
import Control.Lens

import qualified Text.Show.Pragmatic as SP


main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests"
 [ testGroup "Semimanifold laws"
  [ testGroup "Asymptotic associativity"
   [ QC.testProperty "Real vector space" (nearlyAssociative @(ℝ,ℝ))
   , QC.testProperty "1-sphere" (nearlyAssociative @S¹)
   , QC.testProperty "Projective line" (nearlyAssociative @ℝP¹)
   , QC.testProperty "2-sphere" (QC.expectFailure $ nearlyAssociative @S²)
   , QC.testProperty "Projective plane" (QC.expectFailure $ nearlyAssociative @ℝP²)
   ]
  ]
 , testGroup "Pseudoaffine laws"
  [ testGroup "Displacement cancellation"
   [ QC.testProperty "Real vector space" (originCancellation @(ℝ,ℝ))
   , QC.testProperty "1-sphere" (originCancellation @S¹)
   , QC.testProperty "Projective line" (originCancellation @ℝP¹)
   , QC.testProperty "2-sphere" (originCancellation @S²)
   , QC.testProperty "Projective plane" (originCancellation @ℝP²)
   ]
  ]
 , testGroup "Graph structure of webs"
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
  , testCase "Direct neighbours in quadratic web with one-direction diagonals."
    $ toList (directNeighbours unidirDiagonalLinkedWeb) @?= [[1,2,3],[0,3],[0,1,3],[1,2]]
  , testCase "Direct neighbours in 1-dir diag quadratic web after bidirectionalisation."
    $ toList (directNeighbours $ bidirectionaliseWebLinks unidirDiagonalLinkedWeb)
          @?= [[1,2,3],[0,2,3],[0,1,3],[0,1,2]]
  , testCase "Direct neighbours in unsymmetric web."
    $ toList (directNeighbours unsymmetricWeb)
         @?= [[5],[2,3,0],[4,3],[4,2,5,1],[5],[0,1,6],[5],[4,6]]
  , testCase "Next-neighbours in simple quadratic web."
    $ toList (nextNeighbours quadraticWeb) @?=
      [ [(1,[0,3]),(2,[0,3])]
      , [(0,[1,2]),(3,[1,2])]
      , [(0,[1,2]),(3,[1,2])]
      , [(1,[0,3]),(2,[0,3])] ]
  , testCase "Next-neighbours in triangular web (after scrambling)"
    $ toList (nextNeighbours $ scrambleKnitting triangularWeb) @?=
      [ [(2,[1,0]),(1,[2,0])]
      , [(2,[1,0]),(0,[2,1])]
      , [(1,[2,0]),(0,[2,1])] ]
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
  , testCase "Neighbours in unsymmetric web after scrambling."
    $ toList (directNeighbours $ scrambleKnitting unsymmetricWeb) @?=
       [ [1,6], [4,3,2,5], [5,4,1], [5,4,0,1,6,2], [0,1,6], [2,3,0], [0,1], [5] ]
  ]
 , testGroup "Adjacency layers around points in a web"
  [ testCase "Onions in nested web"
     $ toList (webOnions $ localFmapWeb _thisNodeId nestedWeb)
      @?= [ [[(o,0)],[(o,1),(o,2)],[(o,3),(o,4)],[(o,6),(o,5)],[(o,7)]]
          , [[(o,1)],[(o,0),(o,3),(o,4)],[(o,6),(o,2),(o,5)],[(o,7)]]
          , [[(o,2)],[(o,0),(o,3)],[(o,1),(o,6)],[(o,4),(o,7)],[(o,5)]]
          , [[(o,3)],[(o,1),(o,6)],[(o,4),(o,0),(o,7)],[(o,5),(o,2)]]
          , [[(o,4)],[(o,1),(o,5),(o,6)],[(o,3),(o,7),(o,0)],[(o,2)]]
          , [[(o,5)],[(o,4),(o,7)],[(o,6),(o,1)],[(o,3),(o,0)],[(o,2)]]
          , [[(o,6)],[(o,3),(o,4),(o,7)],[(o,1),(o,5)],[(o,0)],[(o,2)]]
          , [[(o,7)],[(o,5),(o,6)],[(o,4),(o,3)],[(o,1)],[(o,0)],[(o,2)]]
          ]
  ]
 , testGroup "Neighbour-search for web knitting."
    [ testCase "1D line of points"
       $ bestNeighbours (euclideanNorm :: Norm ℝ)
               (zip [0..] [-1, -0.7 .. 1])
               @?= ([3,4], Nothing)
    , testCase "Origin-boundary excluding two points on the x- and y-axes"
       $ bestNeighbours (euclideanNorm :: Norm (ℝ,ℝ))
               [(0, (1,0)), (1, (0,1))]
               @?= ([0,1], Just (sqrt 2/2, sqrt 2/2))
    , testCase "Origin-boundary excluding points in the x≥0 half plane"
       $ bestNeighbours (euclideanNorm :: Norm (ℝ,ℝ))
               [(0, (1,0)), (1, (0,1)), (2, (0,-1))]
               @?= ([0,1,2], Just (1, -1.922877998462862e-16))
    , testCase "Best neighbours in a quadratic surrounding"
       $ bestNeighbours (euclideanNorm :: Norm (ℝ,ℝ))
               [               (1, (0,-1)), (2, (1,-1))
               , (3, (-1,0)),               (4, (1,0))
               , (5, (-1,1)),  (6, (0,1)),  (7, (1,1)) ]
               @?= ([1,3,4,6], Nothing)
    , testCase "Best neighbours to the corner of a rectangular grid"
       $ bestNeighbours (euclideanNorm :: Norm (ℝ,ℝ))
               [             ( 1,(1,0)), ( 2,(2,0)), ( 3,(3,0))
               , (10,(0,1)), (11,(1,1)), (12,(2,1)), (13,(3,1))
               , (20,(0,2)), (21,(1,2)), (22,(2,2)), (23,(3,2)) ]
               @?= ([1,10], Just (sqrt 2/2, sqrt 2/2))
    , testCase "Best neighbours in a rectangular grid"
       $ bestNeighbours (euclideanNorm :: Norm (ℝ,ℝ))
           ((id&&&id) <$>
               [ (-2,-1), (-1,-1), ( 0,-1), ( 1,-1), ( 2,-1)
               , (-2, 0), (-1, 0),{-ORIGIN-}( 1, 0), ( 2, 0)
               , (-2, 1), (-1, 1), ( 0, 1), ( 1, 1), ( 2, 1) ])
          @?= ([(0,-1), (-1,0), (1,0), (0,1)], Nothing)
    , testCase "Best neighbours in a big rectangular grid"
       $ bestNeighbours (euclideanNorm :: Norm (ℝ,ℝ))
           ((id&&&id) <$>
               [ (-3,-3), (-2,-3), (-1,-3), ( 0,-3), ( 1,-3), ( 2,-3), ( 3,-3)
               , (-3,-2), (-2,-2), (-1,-2), ( 0,-2), ( 1,-2), ( 2,-2), ( 3,-2)
               , (-3,-1), (-2,-1), (-1,-1), ( 0,-1), ( 1,-1), ( 2,-1), ( 3,-1)
               , (-3, 0), (-2, 0), (-1, 0),{-ORIGIN-}( 1, 0), ( 2, 0), ( 3, 0)
               , (-3, 1), (-2, 1), (-1, 1), ( 0, 1), ( 1, 1), ( 2, 1), ( 3, 1)
               , (-3, 2), (-2, 2), (-1, 2), ( 0, 2), ( 1, 2), ( 2, 2), ( 3, 2) ])
          @?= ([(0,-1), (-1,0), (1,0), (0,1)], Nothing)
    , testCase "Best neighbours in an irregular point-cloud"
       $ bestNeighbours (euclideanNorm :: Norm (ℝ,ℝ))
           ((id&&&id) <$>
               [                               (-1,-6)

               ,                                     (0,-5),          (4,-5),(5,-5)

               ,                               (-1,-4)

               ,(-6,-3),    (-4,-3),(2,-3)

               ,                          (-2,-2),   (0,-2)

               ,                                         (1,-1),     (4,-1),(5,-1)

                                                   {-ORIGIN-}

                      ,(-5,1),     (-3,1),(-2,1),              (2,1), (4,1), (5,1)

               ,                   (-3,2),(-2,3),        (1,3),(2,3)

                      ,(-5,4),                 (-1,4),(3,4)

               ,                   (-3,5),                         (3,5)

               ,                                               (2,6),        (5,6),(6,6) ])
          @?= ([(1,-1), (-2,-2), (2,1), (-6,-3), (-2,1)], Nothing)
    , testCase "Best neighbours in degenerate near-boundary constellation"
       $ bestNeighbours (euclideanNorm :: Norm (ℝ,ℝ))
           ((id &&& (^-^(3.6, 3.0))) <$> reverse
               [ (3.15,3.6)
                          , (3.29,3.4)
                           , (3.3,3.2), (3.45,3.2), (3.6,3.2)
               , (3.15,3.0), (3.3,3.0)              {-ORIGIN-}
               , (3.15,2.8), (3.3,2.8), (3.45,2.8), (3.6,2.8), (3.75,2.8)
                                      , (3.45,2.6), (3.6,2.6), (3.75,2.6), (3.9,2.6)
               , (3.15,2.2)
               ])
          @?= ([(3.6,2.8), (3.3,3.0), (3.6,3.2), (3.75,2.8)], Nothing)
    , testCase "Best neighbours in point selection from almost-rectangular grid"
        $ bestNeighbours (euclideanNorm :: Norm (ℝ,ℝ))
           ([ (235,(0.0,-0.2))
            , (248,(-0.7499999999999996,0.0))
            , (267,(0.0,0.2))
            , (268,(0.15,0.0))
            , (271,(-0.14999,0.0))
            ])
          @?= ([271,267,268,235], Nothing)
    , testCase "Best neighbours in point selection of 1D web test"
        $ bestNeighbours (euclideanNorm :: Norm ℝ)
           ((id &&& (^-^467)) <$>
            [ 565.5193483520385, 254.62827644949562
            , 203.3896874080876, 214.87356399193985 ])
          @?= ([565.5193483520385, 254.62827644949562], Nothing)
    ]
 , testGroup "Automatically building webs"
    [ testCase "Minimal, 3-point 1D “web”"
        $ let web = fromWebNodes euclideanMetric [(x, ()) | x<-[0,1,2]]
                         :: PointsWeb ℝ ()
          in toList (localFmapWeb (\info
                       -> ( fst <$> info^.nodeNeighbours
                          , info^.webBoundingPlane ) ) web)
               @?= [([1], Just 1), ([0,2], Nothing), ([1], Just $ -1)]
    , testCase "Linear 1D “web”"
        $ toList (directNeighbours (fromWebNodes euclideanMetric
                                       [(x, ()) | x<-[0, 0.1 .. 2]] :: PointsWeb ℝ () ))
          @?= [ [1,9], [0,2], [1,3], [2,4], [3], [6,12], [5,7], [6,8], [7,9], [0,8], [11,15]
              , [10,12],[11,5],[14,20],[13,15],[10,14],[17],[16,18],[17,19],[18,20],[13,19]
              ]
    , testCase "Small linear 1D web with nonuniform spacing"
        $ toList (directNeighbours (fromWebNodes euclideanMetric
                                       [ (x, ()) | x<-[ 203.3896874080876
                                                      , 214.87356399193985
                                                      , 254.62827644949562
                                                      , 467.0
                                                      , 565.5193483520385 ]
                                       ] :: PointsWeb ℝ () ))
          @?= [ [1], [0,2], [1,3], [4,2], [3] ]
    , QC.testProperty "Random 1D web should be strongly connected"
       $ \ps -> length ps >= 2 ==>
                 length (Graph.scc . fst
                          $ toGraph ( fromWebNodes euclideanMetric
                                        [(x, ()) | x<-Set.toList ps] :: PointsWeb ℝ () )
                      ) == 1
    , QC.testProperty "Random 1D web should have only 2 boundary-points"
       $ \ps -> length ps >= 2 ==>
                 length (webBoundary (fromWebNodes euclideanMetric
                                        [(x, ()) | x<-Set.toList ps] :: PointsWeb ℝ () )
                      ) == 2
    ]
 , testGroup "Shades"
    [ testCase "Equality of `Shade`s"
       $ (1 :± [1]) @?≈ (1 :± [1] :: Shade ℝ)
    , testCase "Equality of `Shade'`s"
       $ ((1,0)|±|[(1,-2),(3,4)]) @?≈ ((1,0)|±|[(1,-2),(3,4)] :: Shade' (ℝ,ℝ))
    , testCase "Pragmatically showing"
       $ SP.show ((1,0)|±|[(1,-2),(3,4)] :: Shade' (ℝ,ℝ))
                 @?= "(1,0)|±|[(5,2),(0,2)]"
    , testCase "Pragmatically showing (with orthogonal span)"
       $ SP.show ((1,0)|±|[(6,0),(0,2)] :: Shade' (ℝ,ℝ))
                 @?= "(1,0)|±|[(6,0),(0,2)]"
    ]
 , testGroup "Function models for uncertain data"
    [ testCase "Fitting a 1D affine model to constant data"
       $ fitLocally [ (-1, 5|±|[1]), (0, 5|±|[1]), (1, 5|±|[1]) ]
          @?≈ Just (
               AffineModel (5:±[1.15]) (zeroV:±[id^/sqrt 2]) :: AffineModel ℝ ℝ )
    , testCase "Fitting a 2D affine model to constant data"
       $ fitLocally [                    ((0,1), 5|±|[1])
                    , ((-1,0), 5|±|[1]), ((0,0), 5|±|[1]), ((1,0), 5|±|[1])
                    ,                    ((0,-1), 5|±|[1])                  ]
          @?≈ Just (
               AffineModel (5:±[0.9]) (zeroV:±((^/sqrt 2)<$>[fst, snd]))
                  :: AffineModel (ℝ,ℝ) ℝ )
    , testCase "Fitting a 1D affine model to rising-uncertainty data"
       $ fitLocally [ (-1, 3|±|[0.1]), (0, 4|±|[0.5]), (1, 5|±|[1]) ]
          @?≈ Just (
               AffineModel (4:±[1/sqrt 2]) (id:±[id^*0.36]) :: AffineModel ℝ ℝ )
    , testCase "Fitting a 1D affine model to quadratic data"
       $ fitLocally [ (-1, 3|±|[0.1]), (0, 0|±|[0.1]), (1, 3|±|[0.1]) ]
          @?≈ Just (
               AffineModel (2:±[2.94]) (zeroV:±[id^*1.8]) :: AffineModel ℝ ℝ )
    ]
 ]

emptyWeb, singletonWeb, triangularWeb, quadraticWeb, nestedWeb, unsymmetricWeb
  , unidirDiagonalLinkedWeb
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

unidirDiagonalLinkedWeb = PointsWeb $
        OverlappingBranches 4 (Shade o mempty) (pure . DBranch o $ Hourglass
         (PlainLeaves [ (o, Neighbourhood () [1,2,3] euclideanNorm Nothing)
                      , (o, Neighbourhood () [-1,2] euclideanNorm Nothing)
                      ])
         (PlainLeaves [ (o, Neighbourhood () [-2,-1,1] euclideanNorm Nothing)
                      , (o, Neighbourhood () [-2,-1] euclideanNorm Nothing)
                      ])
         )



o = zeroV :: ℝ⁰

dummyWebFmap :: PointsWeb ℝ⁰ a -> PointsWeb ℝ⁰ a
dummyWebFmap = localFmapWeb $ \info -> info^.thisNodeData

directNeighbours :: WithField ℝ Manifold v => PointsWeb v () -> PointsWeb v [WebNodeId]
directNeighbours = localFmapWeb $
     \info -> fst <$> info^.nodeNeighbours

nextNeighbours :: PointsWeb ℝ⁰ a -> PointsWeb ℝ⁰ [(WebNodeId, [WebNodeId])]
nextNeighbours = webLocalInfo >>> localFmapWeb `id`
     \info -> [ ( nId ≡! nId' ≡! (nInfo^.thisNodeId) ≡! (nInfo'^.thisNodeId)
                , (fst<$>nInfo^.nodeNeighbours) ≡! (fst<$>nInfo'^.nodeNeighbours) )
              | ((nId,(_,nInfo)),(nId',(_,nInfo')))
                    <- zip (info^.nodeNeighbours)
                           (info^.thisNodeData.nodeNeighbours)
              , all (==Origin) [ nInfo''^.thisNodeCoord
                               | (_,(_,nInfo''))<-nInfo'^.nodeNeighbours ]
              ]

pointsLocInEnvi :: PointsWeb ℝ⁰ a -> PointsWeb ℝ⁰ [((Int, Trees ℝ⁰), WebNodeId)]
pointsLocInEnvi = fmapNodesInEnvi $
     \(NodeInWeb (_, orig) env)
         -> fmap (const $ first ((nLeaves&&&onlyNodes) . fmap (const ())) <$> env) orig


scrambleKnitting :: PointsWeb ℝ⁰ a -> PointsWeb ℝ⁰ a
scrambleKnitting = tweakWebGeometry euclideanMetric
         $ \info -> nub [ i'
                        | (_, (_, nInfo)) <- info^.nodeNeighbours
                        , (i',_) <- nInfo^.nodeNeighbours
                        , i' /= info^.thisNodeId ]

infixl 4 ≡!
(≡!) :: (Eq a, Show a) => a -> a -> a
x ≡! y | x==y       = x
       | otherwise  = error $ show x++" ≠ "++show y


infix 4 ≈
class AEq e where
  (≈) :: e -> e -> Bool

instance AEq Double where
  x ≈ y  = x + abs x*1e-9 >= y
          && x - abs x*1e-9 <= y
instance (SimpleSpace v, Needle v~v, Interior v~v, Floating (Scalar v))
             => AEq (Shade' v) where
  Shade' c₀ σ₀ ≈ Shade' c₁ σ₁
    = (σ₀|$|δ) < ε && (σ₀|$|δ) < ε
     && all (is1 . (σ₀|$|)) (normSpanningSystem' σ₁)
     && all (is1 . (σ₁|$|)) (normSpanningSystem' σ₀)
   where δ = c₁ ^-^ c₀
         ε = 1e-2
         is1 x = abs (x-1) < ε
instance ( SimpleSpace v, DualVector (Needle' v) ~ v, Interior v ~ v
         , InnerSpace (Scalar v), Scalar (Needle' v) ~ Scalar v )
              => AEq (Shade v) where
  Shade c₀ σ₀ ≈ Shade c₁ σ₁
    = (dualNorm σ₀|$|δ) < ε && (dualNorm σ₀|$|δ) < ε
     && all (is1 . (dualNorm σ₀|$|)) (normSpanningSystem σ₁)
     && all (is1 . (dualNorm σ₁|$|)) (normSpanningSystem σ₀)
   where δ = c₁ ^-^ c₀
         ε = 1e-2
         is1 x = abs (x-1) < ε
instance AEq a => AEq (Maybe a) where
  Just x ≈ Just y = x ≈ y
  Nothing ≈ Nothing = True
  _ ≈ _ = False
instance (AEq (Shade y), AEq (Shade (Needle x +> Needle y)))
              => AEq (AffineModel x y) where
  AffineModel b₀ a₀ ≈ AffineModel b₁ a₁ = b₀ ≈ b₁ && a₀ ≈ a₁

instance (AEq a, AEq b) => (AEq (a,b)) where
  (x,y) ≈ (ξ,υ) = x≈ξ && y≈υ
instance AEq S¹ where
  S¹ φ ≈ S¹ ϕ
   | φ > pi/2, ϕ < -pi/2  = S¹ (φ - 2*pi) ≈ S¹ ϕ
   | ϕ > pi/2, φ < -pi/2  = S¹ φ ≈ S¹ (ϕ - 2*pi)
   | otherwise            = abs (φ - ϕ) < 1e-9
instance AEq S² where
  S² θ φ ≈ S² ϑ ϕ
   | φ > pi/2, ϕ < -pi/2  = S² θ (φ - 2*pi) ≈ S² ϑ ϕ
   | ϕ > pi/2, φ < -pi/2  = S² θ φ ≈ S² ϑ (ϕ - 2*pi)
   | otherwise            = abs (θ - ϑ) < 1e-9 && abs (φ - ϕ) * sin θ < 1e-9

instance AEq ℝP⁰ where
  ℝPZero ≈ ℝPZero  = True
instance AEq ℝP¹ where
  ℝP¹ h ≈ ℝP¹ h'
   | h > 1/2, h'< -1/2  = S¹ (h - 2) ≈ S¹ h'
   | h'> 1/2, h < -1/2  = S¹ h ≈ S¹ (h'- 2)
   | otherwise          = abs (h - h') < 1e-9
instance AEq ℝP² where
  ℝP² r φ ≈ ℝP² r' ϕ
   | φ > pi/2, ϕ < -pi/2  = ℝP² r (φ - 2*pi) ≈ ℝP² r' ϕ
   | ϕ > pi/2, φ < -pi/2  = ℝP² r φ ≈ ℝP² r' (ϕ - 2*pi)
   | r < 1                = abs (r - r') < 1e-9 && abs (φ - ϕ) * r < 1e-9
   | φ > pi/4, ϕ < -pi/4  = ℝP² 1 (φ - pi) ≈ ℝP² 1 ϕ
   | ϕ > pi/4, φ < -pi/4  = ℝP² 1 φ ≈ ℝP² 1 (ϕ - pi)
   | otherwise            = abs (φ - ϕ) < 1e-9
                                        
infix 1 @?≈       
(@?≈) :: (AEq e, Show e) => e -> e -> Assertion
a@?≈b
 | a≈b        = return ()
 | otherwise  = assertFailure $ "Expected "++show b++", but got "++show a

instance QC.Arbitrary ℝ² where
  arbitrary = (\(x,y)->V2 x y) <$> QC.arbitrary

nearlyAssociative :: ∀ m . (AEq m, Semimanifold m, Interior m ~ m)
                         => m -> Needle m -> Needle m -> Bool
nearlyAssociative p v w = (p .+~^ v) .+~^ w ≈ (p .+~^ (v^+^w) :: m)

originCancellation :: ∀ m . (AEq m, Manifold m)
                         => m -> m -> Bool
originCancellation p q = case ( boundarylessWitness :: BoundarylessWitness m
                              , p.-~.q ) of
      (BoundarylessWitness, Just v) -> q.+~^v ≈ p

