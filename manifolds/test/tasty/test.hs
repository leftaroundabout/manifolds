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
{-# LANGUAGE FlexibleInstances, AllowAmbiguousTypes  #-}
{-# LANGUAGE TypeOperators, TypeApplications, ScopedTypeVariables, UnicodeSyntax #-}

module Main where

import Data.Manifold.Types
import Data.Manifold.PseudoAffine
import Data.Manifold.FibreBundle
import Data.Manifold.TreeCover
import Data.Manifold.Web
import Data.Manifold.Web.Internal
import Data.Manifold.Function.LocalModel
import Math.Manifold.Embedding.Simple.Class
import Data.VectorSpace
import Data.Cross (cross3)
import Linear.V2 (V2(V2))
import Linear.V3 (V3(V3))
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
import Control.Lens hiding ((<.>))

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
   , testGroup "2-sphere corner cases"
    [ QC.testProperty "To north pole"
        $ \(S¹ φ) p -> originCancellation (S² 0 φ) p
    , QC.testProperty "From north pole"
        $ \(S¹ φ) p -> originCancellation p (S² 0 φ)
    , QC.testProperty "To south pole"
        $ \(S¹ φ) p -> originCancellation (S² pi φ) p
    , QC.testProperty "From south pole"
        $ \(S¹ φ) p -> originCancellation p (S² pi φ)
    , QC.testProperty "South- to north pole"
        $ \(S¹ φ) (S¹ ψ) -> originCancellation (S² 0 φ) (S² pi ψ)
    , QC.testProperty "North- to south pole"
        $ \(S¹ φ) (S¹ ψ) -> originCancellation (S² pi ψ) (S² 0 φ)
    , QC.testProperty "Along equator"
        $ \(S¹ φ) (S¹ ψ) -> originCancellation (S² (pi/2) ψ) (S² (pi/2) φ)
    , QC.testProperty "Just south of equator"
        $ \(S¹ φ) (S¹ ψ) -> originCancellation (S² (pi/2 + 1e-10) ψ) (S² (pi/2 + 1e-10) φ)
    , QC.testProperty "Just across the equator"
        $ \(S¹ φ) (S¹ ψ) -> originCancellation (S² (pi/2) ψ) (S² (pi/2 + 1e-10) φ)
    , QC.testProperty "To equator"
        $ \(S¹ φ) p -> originCancellation (S² (pi/2) φ) p
    , QC.testProperty "From equator"
        $ \(S¹ φ) p -> originCancellation p (S² (pi/2) φ)
    ]
   , QC.testProperty "Projective plane" (originCancellation @ℝP²)
   ]
  ]
 , testGroup "Natural embeddings"
  [ testGroup "1-sphere"
     [ testCase "North pole" $ embed (S¹ $ pi/2) @?≈ (V2 0 1 :: ℝ²)
     , testCase "South pole" $ embed (S¹ $ -pi/2) @?≈ (V2 0 (-1) :: ℝ²)
     ]
  , testGroup "2-sphere"
     [ testCase "North pole" $ embed (S² 0 0) @?≈ (V3 0 0 1 :: ℝ³)
     , testCase "South pole" $ embed (S² pi 0) @?≈ (V3 0 0 (-1) :: ℝ³)
     ]
  , testGroup "1-sphere tangent bundle"
     [ testCase "North pole"
           $ embed (FibreBundle (S¹ $  pi/2) 1 :: TangentBundle S¹)
               @?≈ (FibreBundle (V2 0 1) (V2 (-1) 0) :: TangentBundle ℝ²)
     , testCase "South pole"
           $ embed (FibreBundle (S¹ $ -pi/2) 1 :: TangentBundle S¹)
               @?≈ (FibreBundle (V2 0 (-1)) (V2 1 0) :: TangentBundle ℝ²)
     , testCase "45°"
           $ embed (FibreBundle (S¹ $ pi/4) 1 :: TangentBundle S¹)
               @?≈ (FibreBundle (V2 1 1^/sqrt 2) (V2 (-1) 1^/sqrt 2) :: TangentBundle ℝ²)
     ]
  , testGroup "2-sphere tangent bundle"
     [ testCase "North pole, x-dir"
           $ embed (FibreBundle (S² 0 0) (V2 1 0) :: TangentBundle S²)
               @?≈ (FibreBundle (V3 0 0 1) (V3 1 0 0) :: TangentBundle ℝ³)
     , testCase "North pole (alternative φ), x-dir"
           $ embed (FibreBundle (S² 0 1.524) (V2 1 0) :: TangentBundle S²)
               @?≈ (FibreBundle (V3 0 0 1) (V3 1 0 0) :: TangentBundle ℝ³)
     , testCase "North pole, y-dir"
           $ embed (FibreBundle (S² 0 0) (V2 0 1) :: TangentBundle S²)
               @?≈ (FibreBundle (V3 0 0 1) (V3 0 1 0) :: TangentBundle ℝ³)
     , testCase "Close to north pole"
           $ embed (FibreBundle (S² 1e-11 0.602) (V2 3.7 1.1) :: TangentBundle S²)
               @?≈ (FibreBundle (V3 0 0 1) (V3 3.7 1.1 0) :: TangentBundle ℝ³)
     , testCase "South pole, x-dir"
           $ embed (FibreBundle (S² pi 0) (V2 1 0) :: TangentBundle S²)
               @?≈ (FibreBundle (V3 0 0 (-1)) (V3 (-1) 0 0) :: TangentBundle ℝ³)
     , testCase "South pole, y-dir"
           $ embed (FibreBundle (S² pi 0) (V2 0 1) :: TangentBundle S²)
               @?≈ (FibreBundle (V3 0 0 (-1)) (V3 0 1 0) :: TangentBundle ℝ³)
     , testCase "Close to south pole"
           $ embed (FibreBundle (S² (pi-1e-11) 0.602) (V2 3.7 1.1) :: TangentBundle S²)
               @?≈ (FibreBundle (V3 0 0 (-1)) (V3 (-3.7) 1.1 0) :: TangentBundle ℝ³)
     , testCase "Equator, y-dir"
           $ embed (FibreBundle (S² (pi/2) 0) (V2 0 1) :: TangentBundle S²)
               @?≈ (FibreBundle (V3 1 0 0) (V3 0 1 0) :: TangentBundle ℝ³)
     , testCase "Equator, x-dir"
           $ embed (FibreBundle (S² (pi/2) (pi/2)) (V2 1 0) :: TangentBundle S²)
               @?≈ (FibreBundle (V3 0 1 0) (V3 (-1) 0 0) :: TangentBundle ℝ³)
     , testCase "Equator, z-dir"
           $ embed (FibreBundle (S² (pi/2) 0) (V2 1 0) :: TangentBundle S²)
               @?≈ (FibreBundle (V3 1 0 0) (V3 0 0 (-1)) :: TangentBundle ℝ³)
     ]
  ]
 , testGroup "Embedding tangent bundles"
  [ QC.testProperty "Real vector space" (embeddingTangentiality @ℝ² @ℝ² 1)
  , QC.testProperty "1-sphere (unlimited)" (QC.expectFailure
                                       $ embeddingTangentiality @ℝ² @S¹ 1)
  , QC.testProperty "1-sphere" (embeddingTangentiality @ℝ² @S¹ 1e-5)
  , QC.testProperty "2-sphere" (embeddingTangentiality @ℝ³ @S² 1e-5)
  ]
 , testGroup "Embedding back-projection"
  [ QC.testProperty "Real vector space" (embeddingBackProject @(ℝ,ℝ) @ℝ)
  , QC.testProperty "1-sphere" (embeddingBackProject @ℝ² @S¹)
  , QC.testProperty "2-sphere" (embeddingBackProject @ℝ³ @S²)
  , QC.testProperty "Vector space tangent bundle"
       (embeddingBackProject @(TangentBundle (ℝ,ℝ)) @(TangentBundle ℝ) )
  , QC.testProperty "S¹ tangent bundle"
       (embeddingBackProject @(TangentBundle ℝ²) @(TangentBundle S¹) )
  , QC.testProperty "S² tangent bundle"
       (embeddingBackProject @(TangentBundle ℝ³) @(TangentBundle S²) )
  ]
 , testGroup "Special properties of translations"
  [ testGroup "2-sphere"
   [ QC.testProperty "S²-movement as rotation in ℝ³"
      $ \p v -> let FibreBundle pCart vCart :: TangentBundle ℝ³
                         = embed (FibreBundle p v :: TangentBundle S²)
                    q = p .+~^ v :: S²
                    qCart = embed q :: ℝ³
                    axis = pCart `cross3` qCart
                    FibreBundle _ axisProj :: TangentBundle S²
                        = coEmbed (FibreBundle pCart axis :: TangentBundle ℝ³)
                in vCart <.> axis + 1 ≈ 1    -- i.e. the movement vector is always
                  && v <.> axisProj + 1 ≈ 1  -- orthogonal to the rotation axis.
   ]
  ]
 , testGroup "Parallel transport"
  [ testGroup "Displacement cancellation"
   [ QC.testProperty "Real vector space" (parTransportAssociativity @(ℝ,ℝ))
   , QC.testProperty "1-sphere" (parTransportAssociativity @S¹)
   ]
  , testGroup "Nearby tangent spaces of embedding"
   [ QC.testProperty "Real vector space" (nearbyTangentSpaceEmbedding @(ℝ,ℝ) @ℝ 1)
   , QC.testProperty "1-sphere (unlimited)"
         $ QC.expectFailure (nearbyTangentSpaceEmbedding @ℝ² @S¹ 1)
   , QC.testProperty "1-sphere" (nearbyTangentSpaceEmbedding @ℝ² @S¹ 1e-5)
   , QC.testProperty "2-sphere" (nearbyTangentSpaceEmbedding @ℝ³ @S² 1e-5)
   ]
  , testGroup "2-sphere"
   [ testCase "Non-movement on the equator"
        $ sphereParallelTransportTest
            (S² (pi/2) 0) (S² (pi/2) 0) [V3 0 0 1] [V3 0 0 1]
   , testCase "Micro-movement on the equator"
        $ sphereParallelTransportTest
            (S² (pi/2) 0) (S² (pi/2) 1e-3) [V3 0 0 1] [V3 0 0 1]
   , testCase "Small movement on the equator (ez)"
        $ sphereParallelTransportTest
            (S² (pi/2) 0) (S² (pi/2) (pi/2)) [V3 0 0 1, V3   0  1 0]
                                             [V3 0 0 1, V3 (-1) 0 0]
   , testCase "Big movement on the equator"
        $ sphereParallelTransportTest
            (S² (pi/2) 0) (S² (pi/2) 3) [V3 0 0 1] [V3 0 0 1]
   , testCase "Big negative movement on the equator"
        $ sphereParallelTransportTest
            (S² (pi/2) 0) (S² (pi/2) (-3)) [V3 0 0 1] [V3 0 0 1]
   , testCase "Movement on the zero meridian from north pole"
        $ sphereParallelTransportTest
            (S² 0 0) (S² (pi/2) 0) [V3 0 1 0] [V3 0 1 0]
   , testCase "Movement on the zero meridian to north pole"
        $ sphereParallelTransportTest
            (S² (pi/2) 0) (S² 0 0) [V3 0 1 0, V3   0  0 1]
                                   [V3 0 1 0, V3 (-1) 0 0]
   , testCase "Crossing the equator on the zero meridian"
        $ sphereParallelTransportTest
            (S² (pi/4) 0) (S² (3*pi/4) 0) [V3 0 1 0, V3 (-1) 0 1] 
                                          [V3 0 1 0, V3   1  0 1]
   , testCase "Crossing the equator on the 90° meridian"
        $ sphereParallelTransportTest
            (S² (pi/4) (pi/2)) (S² (3*pi/4) (pi/2)) [V3 1 0 0, V3 0 (-1) 1]
                                                    [V3 1 0 0, V3 0   1  1]
   , testCase "Crossing the equator on the 180° meridian"
        $ sphereParallelTransportTest
            (S² (pi/4) pi) (S² (3*pi/4) pi) [V3 0 1 0, V3   1  0 1]
                                            [V3 0 1 0, V3 (-1) 0 1]
   , testCase "Crossing the equator on the -90° meridian"
        $ sphereParallelTransportTest
            (S² (pi/4) (-pi/2)) (S² (3*pi/4) (-pi/2)) [V3 1 0 0, V3 0   1  1]
                                                      [V3 1 0 0, V3 0 (-1) 1]
   , QC.testProperty "Movement on the equator" . QC.expectFailure
        $ \(S¹ φ₀) (S¹ φ₁) -> assertParTransportNeedleTargetFixpoint
                 (S² 0 0, Just "north pole")
                 (S² (pi/2) φ₀)
                 (S² (pi/2) φ₁)
   , QC.testProperty "Just north of the equator"
        $ \p@(S¹ φ₀) q@(S¹ φ₁) -> abs (p.-~!q) < 2
            ==> assertParTransportNeedleTargetFixpoint
                 (S² 0 0, Just "north pole")
                 (S² (pi/2-1e-13) φ₀)
                 (S² (pi/2-1e-13) φ₁)
   , QC.testProperty "Just slightly crossing the equator"
        $ \(S¹ φ₀) (S¹ φ₁) -> assertParTransportNeedleTargetFixpoint
                 (S² 0 0, Just "north pole")
                 (S² (pi/2-1e-13) φ₀)
                 (S² (pi/2+1e-13) φ₁)
   , QC.testProperty "Just south of the equator"
        $ \p@(S¹ φ₀) q@(S¹ φ₁) -> abs (p.-~!q) < 2
            ==> assertParTransportNeedleTargetFixpoint
                 (S² pi 0, Just "south pole")
                 (S² (pi/2+1e-13) φ₀)
                 (S² (pi/2+1e-13) φ₁)
   , QC.testProperty "Movement on the zero meridian"
        $ \(S¹ θ₀) (S¹ θ₁) -> assertParTransportNeedleTargetFixpoint
                 (S² (pi/2) (pi/2), Nothing)
                 (S² (abs θ₀) (if θ₀>0 then 0 else pi))
                 (S² (abs θ₁) (if θ₁>0 then 0 else pi))
   , QC.testProperty "Rotation axis"
        $ \p vbig -> let
                      v = vbig ^/ 20
                      q = p .+~^ v :: S²
                      w = parallelTransport p v v
                      FibreBundle pCart vCart
                          = embed (FibreBundle p v :: TangentBundle S²) :: TangentBundle ℝ³
                      FibreBundle qCart wCart
                          = embed (FibreBundle q w :: TangentBundle S²) :: TangentBundle ℝ³
                      pxv = pCart`cross3`vCart
                      qxw = qCart`cross3`wCart
                    in magnitude v < 2*pi ==>
                       QC.counterexample
                           ("  𝑝 = "++SP.show p++"\t ≃ "++SP.show pCart
                        ++"\n  𝑞 = "++SP.show q++"\t ≃ "++SP.show qCart
                        ++"\n  𝑣 = "++SP.show v++"\t = "++SP.show vCart++" @ 𝑝"
                        ++"\n  𝑤 = "++SP.show w++"\t = "++SP.show wCart++" @ 𝑞"
                        ++"\n𝑝×𝑣 = "++SP.show pxv    -- rotation axis
                        ++"\n𝑞×𝑤 = "++SP.show qxw    -- rotation axis
                             )
                       $ pxv ≈ qxw
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
  fuzzyEq :: ℝ -> e -> e -> Bool
  unitEpsilon :: ℝ
  unitEpsilon = 1e-9
  (≈) :: e -> e -> Bool
  (≈) = fuzzyEq (unitEpsilon @e)

instance AEq Double where
  fuzzyEq η x y  = x + abs x*η >= y
          && x - abs x*η <= y
instance (SimpleSpace v, Needle v~v, Interior v~v, Floating (Scalar v))
             => AEq (Shade' v) where
  fuzzyEq η (Shade' c₀ σ₀) (Shade' c₁ σ₁)
    = (σ₀|$|δ) < ε && (σ₀|$|δ) < ε
     && all (is1 . (σ₀|$|)) (normSpanningSystem' σ₁)
     && all (is1 . (σ₁|$|)) (normSpanningSystem' σ₀)
   where δ = c₁ ^-^ c₀
         ε = 1e-2 + realToFrac η
         is1 x = abs (x-1) < ε
instance ( SimpleSpace v, DualVector (Needle' v) ~ v, Interior v ~ v
         , InnerSpace (Scalar v), Scalar (Needle' v) ~ Scalar v )
              => AEq (Shade v) where
  fuzzyEq η (Shade c₀ σ₀) (Shade c₁ σ₁)
    = (dualNorm σ₀|$|δ) < ε && (dualNorm σ₀|$|δ) < ε
     && all (is1 . (dualNorm σ₀|$|)) (normSpanningSystem σ₁)
     && all (is1 . (dualNorm σ₁|$|)) (normSpanningSystem σ₀)
   where δ = c₁ ^-^ c₀
         ε = 1e-2 + realToFrac η
         is1 x = abs (x-1) < ε
instance AEq a => AEq (Maybe a) where
  fuzzyEq η (Just x) (Just y) = fuzzyEq η x y
  fuzzyEq _ Nothing Nothing = True
  fuzzyEq _ _ _ = False
instance (AEq (Shade y), AEq (Shade (Needle x +> Needle y)))
              => AEq (AffineModel x y) where
  fuzzyEq η (AffineModel b₀ a₀) (AffineModel b₁ a₁) = fuzzyEq η b₀ b₁ && fuzzyEq η a₀ a₁

instance (AEq a, AEq b) => (AEq (a,b)) where
  fuzzyEq η (x,y) (ξ,υ) = fuzzyEq η x ξ && fuzzyEq η y υ
instance AEq S¹ where
  fuzzyEq η (S¹ φ) (S¹ ϕ)
   | φ > pi/2, ϕ < -pi/2  = fuzzyEq η (S¹ $ φ - 2*pi) (S¹ ϕ)
   | ϕ > pi/2, φ < -pi/2  = fuzzyEq η (S¹ φ) (S¹ $ ϕ - 2*pi)
   | otherwise            = abs (φ - ϕ) < η
instance AEq S² where
  fuzzyEq η (S² θ φ) (S² ϑ ϕ)
   | φ > pi/2, ϕ < -pi/2  = fuzzyEq η (S² θ $ φ - 2*pi) (S² ϑ ϕ)
   | ϕ > pi/2, φ < -pi/2  = fuzzyEq η (S² θ φ) (S² ϑ $ ϕ - 2*pi)
   | otherwise            = abs (θ - ϑ) < η && abs (φ - ϕ) * sin θ < η

instance AEq ℝ² where
  fuzzyEq η (V2 x y) (V2 ξ υ) = abs (x - ξ) <= ε && abs (y - υ) <= ε
   where ε = (maximum @[]) (abs<$>[x,y,ξ,υ]) * η
instance AEq ℝ³ where
  fuzzyEq η (V3 x y z) (V3 ξ υ ζ) = (all @[]) ((ε>=) . abs) $ [x-ξ, y-υ, z-ζ]
   where ε = (maximum @[]) (abs<$>[x,y,z,ξ,υ,ζ]) * η

instance AEq ℝP⁰ where
  fuzzyEq _ ℝPZero ℝPZero  = True
instance AEq ℝP¹ where
  fuzzyEq η (ℝP¹ h) (ℝP¹ h')
   | h > 1/2, h'< -1/2  = fuzzyEq η (S¹ $ h - 2) (S¹ h')
   | h'> 1/2, h < -1/2  = fuzzyEq η (S¹ h) (S¹ $ h'- 2)
   | otherwise          = abs (h - h') < η
instance AEq ℝP² where
  fuzzyEq η (ℝP² r φ) (ℝP² r' ϕ)
   | φ > pi/2, ϕ < -pi/2  = fuzzyEq η (ℝP² r $ φ - 2*pi) (ℝP² r' ϕ)
   | ϕ > pi/2, φ < -pi/2  = fuzzyEq η (ℝP² r φ) (ℝP² r' $ ϕ - 2*pi)
   | r < 1                = abs (r - r') < η && abs (φ - ϕ) * r < η
   | φ > pi/4, ϕ < -pi/4  = fuzzyEq η (ℝP² 1 $ φ - pi) (ℝP² 1 ϕ)
   | ϕ > pi/4, φ < -pi/4  = fuzzyEq η (ℝP² 1 φ) (ℝP² 1 $ ϕ - pi)
   | otherwise            = abs (φ - ϕ) < η

instance (AEq (Interior m), AEq f) => AEq (FibreBundle m f) where
  fuzzyEq η (FibreBundle p v) (FibreBundle q w) = fuzzyEq η p q && fuzzyEq η v w
                                        
infix 1 @?≈       
(@?≈) :: (AEq e, Show e) => e -> e -> Assertion
a@?≈b
 | a≈b        = return ()
 | otherwise  = assertFailure $ "Expected "++show b++", but got "++show a

instance QC.Arbitrary ℝ² where
  arbitrary = (\(x,y)->V2 x y) <$> QC.arbitrary
  shrink (V2 x y) = V2 <$> ((/12)<$>QC.shrink (x*12))
                       <*> ((/12)<$>QC.shrink (y*12))

nearlyAssociative :: ∀ m . (AEq m, Semimanifold m, Interior m ~ m)
                         => m -> Needle m -> Needle m -> Bool
nearlyAssociative p v w = (p .+~^ v) .+~^ w ≈ (p .+~^ (v^+^w) :: m)

originCancellation :: ∀ m . (AEq m, Manifold m, Show m, Show (Needle m))
                         => m -> m -> QC.Property
originCancellation p q = case ( boundarylessWitness :: BoundarylessWitness m
                              , p.-~.q ) of
      (BoundarylessWitness, Just v)
          -> let p' = q.+~^v
             in QC.counterexample ("v = "++show v++", q+v = "++show p') $ p' ≈ p

embeddingBackProject :: ∀ m n . ( NaturallyEmbedded n m, AEq n, SP.Show m, SP.Show n )
       => n -> QC.Property
embeddingBackProject p = QC.counterexample ("Embedded: "++SP.show ep
                                          ++", back-projected: "++SP.show p')
                           $ p' ≈ p
 where ep = embed p :: m
       p' = coEmbed ep

embeddingTangentiality :: ∀ m n . ( Semimanifold m, Semimanifold n
                                  , NaturallyEmbedded n m
                                  , NaturallyEmbedded (TangentBundle n) (TangentBundle m)
                                  , SP.Show n, AEq n
                                  , InnerSpace (Needle n), RealFloat (Scalar (Needle n)) )
       => Scalar (Needle n) -> Interior n -> Needle n -> QC.Property
embeddingTangentiality consistRadius p vub
         = QC.counterexample ("p+v = "++SP.show q++", coEmbed (embed p+v) = "++SP.show q')
            $ fuzzyEq (unitEpsilon @n * (1+rvub^2)) q q'
 where rvub = realToFrac $ magnitude vub
       v = vub ^* consistRadius
       q, q' :: n
       q = p .+~^ v
       q' = coEmbed $ (pEmbd .+~^ vEmbd :: m)
       o :: TangentBundle n
       o = FibreBundle p v
       FibreBundle pEmbd vEmbd = embed o :: TangentBundle m

nearbyTangentSpaceEmbedding :: ∀ m n
                     . ( Semimanifold m, Semimanifold n
                       , m ~ Interior m, n ~ Interior n
                       , NaturallyEmbedded n m
                       , NaturallyEmbedded (TangentBundle n) (TangentBundle m)
                       , ParallelTransporting (->) n (Needle n)
                       , SP.Show n, SP.Show (Needle n), AEq (Needle n)
                       , InnerSpace (Needle n), RealFloat (Scalar (Needle n)) )
       => Scalar (Needle n) -> Interior n -> Needle n -> Needle n -> QC.Property
nearbyTangentSpaceEmbedding consistRadius p vub f
         = QC.counterexample ("𝑓 embd. at 𝑝, then proj. at 𝑝+𝑣 = "++SP.show fReProj
                              ++", 𝑓 moved by 𝑣 = "++SP.show g)
            $ fuzzyEq (unitEpsilon @(Needle n) * (1+rvub^2)) g fReProj
 where rvub = realToFrac $ magnitude vub
       v = vub ^* consistRadius
       q :: n
       q = p .+~^ v :: n
       qEmbd = embed q :: m
       FibreBundle _ fReProj :: TangentBundle n
               = coEmbed (FibreBundle qEmbd fEmbd :: TangentBundle m)
       g = parallelTransport p v f
       o :: TangentBundle n
       o = FibreBundle p f
       FibreBundle pEmbd fEmbd = embed o :: TangentBundle m

parTransportAssociativity :: ∀ m
           . ( AEq m, Manifold m, SP.Show m
             , ParallelTransporting (->) m (Needle m)
             , InnerSpace (Needle m), RealFloat (Scalar (Needle m)) )
                         => m -> Needle m -> Needle m -> QC.Property
parTransportAssociativity p v w
 = maximum (map magnitude [v,w]) < 1000
       -- Very vast vectors incur inevitable floating-point uncertainty
  ==> let q, q' :: m
          q = (p .+~^ v) .+~^ parallelTransport p v w
          q' = p .+~^ (v^+^w)
      in QC.counterexample ("(p+v) + 〔pTp. v〕w = "++SP.show q++", p+(v+w) = "++SP.show q')
          $ q ≈ q'

assertParTransportNeedleTargetFixpoint :: ∀ m
     . ( AEq m, Manifold m, SP.Show m, Show (Needle m)
       , ParallelTransporting (->) m (Needle m) )
    => (m, Maybe String) -> m -> m -> QC.Property
assertParTransportNeedleTargetFixpoint (q, qName) p₀ p₁
         = let q'= p₁ .+~^ parallelTransport p₀ (p₁ .-~! p₀) (q .-~! p₀)
           in QC.counterexample
                 ("Should keep pointing on "++qShw++", but got "++ SP.show q')
               $ q' ≈ q
 where qShw = case qName of
        Just s  -> s
        Nothing -> SP.show q


sphereParallelTransportTest :: S² -> S² -> [ℝ³] -> [ℝ³] -> Assertion
sphereParallelTransportTest p q [] [] = assert True
sphereParallelTransportTest p q (v:vs) (w:ws)
     = (parallelTransport p (q.-~!p) vSph @?≈ wSph)
        >> sphereParallelTransportTest p q vs ws
 where [FibreBundle _ vSph, FibreBundle _ wSph]
          = [ coEmbed (FibreBundle (embed o) u :: TangentBundle ℝ³) :: TangentBundle S²
            | (o,u) <- [(p,v), (q,w)] ]
