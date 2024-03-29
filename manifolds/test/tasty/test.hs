-- |
-- Module      : Main
-- Copyright   : (c) Justus Sagemüller 2017
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsag $ hvl.no
-- Stability   : experimental
-- Portability : portable
-- 

{-# LANGUAGE OverloadedLists, TypeFamilies, FlexibleContexts, UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances, AllowAmbiguousTypes  #-}
{-# LANGUAGE TypeOperators, TypeApplications, ScopedTypeVariables, UnicodeSyntax #-}
{-# LANGUAGE DataKinds #-}

module Main where

import Data.Manifold.Types
import Data.Manifold.PseudoAffine
import Data.Manifold.FibreBundle
import Data.Manifold.TreeCover
import Math.Manifold.Real.Coordinates
import Data.Manifold.Web
import Data.Manifold.Web.Internal
import Data.Manifold.Function.LocalModel
import Math.Manifold.Embedding.Simple.Class
import Math.Manifold.Homogeneous
import Data.VectorSpace
import Data.Cross (cross3)
import Linear.V2 (V2(V2))
import Linear.V3 (V3(V3))
import Math.LinearMap.Category
import Prelude hiding (id, fst, snd, asinh)
import Control.Category.Constrained (id)
import Control.Arrow.Constrained (fst,snd)

import Math.Rotations.Class
import Data.Simplex.Abstract

import Test.Tasty
import Test.Tasty.HUnit
import qualified Test.Tasty.QuickCheck as QC
import Test.Tasty.QuickCheck ((==>))
import Data.Typeable

import Data.Foldable (toList)
import Data.List (nub, sort)
import qualified Data.Graph as Graph
import qualified Data.Set as Set
import Control.Arrow
import Control.Lens hiding ((<.>))

import Data.Fixed (mod')

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
        $ \(S¹Polar φ) p -> originCancellation @S² (S²Polar 0 φ) p
    , QC.testProperty "From north pole"
        $ \(S¹Polar φ) p -> originCancellation @S² p (S²Polar 0 φ)
    , QC.testProperty "To south pole"
        $ \(S¹Polar φ) p -> originCancellation @S² (S²Polar pi φ) p
    , QC.testProperty "From south pole"
        $ \(S¹Polar φ) p -> originCancellation @S² p (S²Polar pi φ)
    , QC.testProperty "South- to north pole"
        $ \(S¹Polar φ) (S¹Polar ψ) -> originCancellation @S² (S²Polar 0 φ) (S²Polar pi ψ)
    , QC.testProperty "North- to south pole"
        $ \(S¹Polar φ) (S¹Polar ψ) -> originCancellation @S² (S²Polar pi ψ) (S²Polar 0 φ)
    , QC.testProperty "Along equator"
        $ \(S¹Polar φ) (S¹Polar ψ) -> originCancellation @S² (S²Polar (pi/2) ψ) (S²Polar (pi/2) φ)
    , QC.testProperty "Just south of equator"
        $ \(S¹Polar φ) (S¹Polar ψ) -> originCancellation @S² (S²Polar (pi/2 + 1e-10) ψ) (S²Polar (pi/2 + 1e-10) φ)
    , QC.testProperty "Just across the equator"
        $ \(S¹Polar φ) (S¹Polar ψ)
              -> originCancellation @S² (S²Polar (pi/2) ψ) (S²Polar (pi/2 + 1e-10) φ)
    , QC.testProperty "To equator"
        $ \(S¹Polar φ) p -> originCancellation @S² (S²Polar (pi/2) φ) p
    , QC.testProperty "From equator"
        $ \(S¹Polar φ) p -> originCancellation @S² p (S²Polar (pi/2) φ)
    ]
   , QC.testProperty "Projective plane" (originCancellation @ℝP²)
   ]
  ]
 , testGroup "Natural embeddings"
  [ testGroup "1-sphere"
     [ testCase "North pole" $ embed @S¹ (S¹Polar $ pi/2) @?≈ (V2 0 1 :: ℝ²)
     , testCase "South pole" $ embed @S¹ (S¹Polar $ -pi/2) @?≈ (V2 0 (-1) :: ℝ²)
     ]
  , testGroup "2-sphere"
     [ testCase "North pole" $ embed @S² (S²Polar 0 0) @?≈ (V3 0 0 1 :: ℝ³)
     , testCase "South pole" $ embed @S² (S²Polar pi 0) @?≈ (V3 0 0 (-1) :: ℝ³)
     ]
  , testGroup "1-sphere tangent bundle"
     [ testCase "North pole"
           $ embed (TangentBundle @S¹ (S¹Polar $  pi/2) 1)
               @?≈ (FibreBundle @ℝ² (V2 0 1) (V2 (-1) 0))
     , testCase "South pole"
           $ embed (TangentBundle @S¹ (S¹Polar $ -pi/2) 1)
               @?≈ (FibreBundle @ℝ² (V2 0 (-1)) (V2 1 0))
     , testCase "45°"
           $ embed (TangentBundle @S¹ (S¹Polar $ pi/4) 1)
               @?≈ (FibreBundle @ℝ² (V2 1 1^/sqrt 2) (V2 (-1) 1^/sqrt 2))
     ]
  , testGroup "2-sphere tangent bundle"
     [ testCase "North pole, x-dir"
           $ embed (TangentBundle @S² (S²Polar 0 0) (V2 1 0))
               @?≈ (FibreBundle @ℝ³ (V3 0 0 1) (V3 1 0 0))
     , testCase "North pole (alternative φ), x-dir"
           $ embed (TangentBundle @S² (S²Polar 0 1.524) (V2 1 0))
               @?≈ (FibreBundle @ℝ³ (V3 0 0 1) (V3 1 0 0))
     , testCase "North pole, y-dir"
           $ embed (TangentBundle @S² (S²Polar 0 0) (V2 0 1))
               @?≈ (FibreBundle @ℝ³ (V3 0 0 1) (V3 0 1 0))
     , testCase "Close to north pole"
           $ embed (TangentBundle @S² (S²Polar 1e-11 0.602) (V2 3.7 1.1))
               @?≈ (FibreBundle @ℝ³ (V3 0 0 1) (V3 3.7 1.1 0))
     , testCase "South pole, x-dir"
           $ embed (TangentBundle @S² (S²Polar pi 0) (V2 1 0))
               @?≈ (FibreBundle @ℝ³ (V3 0 0 (-1)) (V3 (-1) 0 0))
     , testCase "South pole, y-dir"
           $ embed (TangentBundle @S² (S²Polar pi 0) (V2 0 1))
               @?≈ (FibreBundle @ℝ³ (V3 0 0 (-1)) (V3 0 1 0))
     , testCase "Close to south pole"
           $ embed (TangentBundle @S² (S²Polar (pi-1e-11) 0.602) (V2 3.7 1.1))
               @?≈ (FibreBundle @ℝ³ (V3 0 0 (-1)) (V3 (-3.7) 1.1 0))
     , testCase "Equator, y-dir"
           $ embed (TangentBundle @S² (S²Polar (pi/2) 0) (V2 0 1))
               @?≈ (FibreBundle @ℝ³ (V3 1 0 0) (V3 0 1 0))
     , testCase "Equator, x-dir"
           $ embed (TangentBundle @S² (S²Polar (pi/2) (pi/2)) (V2 1 0))
               @?≈ (FibreBundle @ℝ³ (V3 0 1 0) (V3 (-1) 0 0))
     , testCase "Equator, z-dir"
           $ embed (TangentBundle @S² (S²Polar (pi/2) 0) (V2 1 0))
               @?≈ (FibreBundle @ℝ³ (V3 1 0 0) (V3 0 0 (-1)))
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
      $ \p v -> magnitude v < 1e6
            ==> let TangentBundle pCart vCart :: TangentBundle ℝ³
                         = embed $ TangentBundle p v
                    q = p .+~^ v :: S²
                    qCart = embed q :: ℝ³
                    axis = pCart `cross3` qCart
                    TangentBundle _ axisProj :: TangentBundle S²
                        = coEmbed $ TangentBundle pCart axis
                in vCart <.> axis + 1 ≈ 1    -- i.e. the movement vector is always
                  && v <.> axisProj + 1 ≈ 1  -- orthogonal to the rotation axis.
   ]
  ]
 , testGroup "Rotation"
  [ testCase "Pole to eqt / prime meridian"
           $ let rotated = 90° yAxis $ V2 1 0 :@. (S²Polar 0 0 :: S²)
             in V2 (rotated ^. delta zenithAngle) (rotated ^. delta azimuth)
                    @?≈ V2 1 0
  , testCase "Pole to eqt / 90°E"
           $ let rotated = 90° xAxis $ V2 1 0 :@. (S²Polar 0 0 :: S²)
             in V2 (rotated ^. delta zenithAngle) (rotated ^. delta azimuth)
                    @?≈ V2 0 1
  , QC.testProperty "Undo – arbitrary axis / angle and points in 𝑇S²."
           $ \ax ψ p -> rotateAboutThenUndo @(TangentBundle S²) ax ψ p ≈ p
  ]
 , testGroup "Homogeneous spaces"
  $ let lieGroupTests :: ∀ m g . ( g`ActsOn`m
                                 , QC.Arbitrary m
                                 , AEq m, Show m, SP.Show m
                                 , QC.Arbitrary g, Show g )
           => String -> TestTree
        lieGroupTests descr = testGroup descr $
         [ QC.testProperty "`mempty` acts as identity"
          $ \(p :: m) -> action (mempty :: g) p ?≈! p
         , QC.testProperty "There are non-identic elements" -- This is strictly speaking
          . QC.expectFailure                                -- not true for all homogeneous
          $ \a (p :: m) -> action (a :: g) p ?≈! p          -- spaces, but the trivial
                                                            -- ones don't need testing.
         , QC.testProperty "Compatibility of action"
          $ \a b (p :: m) -> action (a<>b :: g) p ?≈! action a (action b p)
         ]
    in [ lieGroupTests @S¹ @(SO 2) "SO(2) acting on S¹"
       , lieGroupTests @S² @(SO 3) "SO(3) acting on S²"
       ]
 , testGroup "Coordinates"
  [ testGroup "Single dimension"
   [ QC.testProperty "Access" $ \x -> x^.xCoord ≈ x
   , QC.testProperty "Update" $ \x₀ x₁ -> (xCoord.~x₁) x₀ ≈ (x₁ :: ℝ) ]
  , testGroup "x-coordinate"
   [ QC.testProperty "Access" $ \x y -> V2 x y^.xCoord ≈ x
   , QC.testProperty "Update" $ \x₀ y x₁ -> (xCoord.~x₁) (V2 x₀ y) ≈ V2 x₁ y ]
  , testGroup "y-coordinate"
   [ QC.testProperty "Access" $ \x y -> V2 x y^.yCoord ≈ y
   , QC.testProperty "Update" $ \x y₀ y₁ -> (yCoord.~y₁) (V2 x y₀) ≈ V2 x y₁ ]
  , testGroup "z-coordinate"
   [ QC.testProperty "Access" $ \x y z -> V3 x y z^.zCoord ≈ z
   , QC.testProperty "Update" $ \x y z₀ z₁ -> (zCoord.~z₁) (V3 x y z₀) ≈ V3 x y z₁ ]
  , testGroup "Lens laws"
   [ coordinateLensLaws @ℝ
   , coordinateLensLaws @ℝ²
   , coordinateLensLaws @ℝ³
   , coordinateLensLaws @S¹
   , coordinateLensLaws @S²
   , coordinateLensLaws @(TangentBundle ℝ)
   , coordinateLensLaws @(TangentBundle ℝ²)
   , coordinateLensLaws @(TangentBundle ℝ³)
   , coordinateLensLaws @(TangentBundle S¹)
   , coordinateLensLaws @(TangentBundle S²)
   ]
  , testGroup "Finite differences"
   [ QC.testProperty "ℝ" $ coordinateFiniteDifference @ℝ 1 1e6 1e100
   , QC.testProperty "ℝ²" $ coordinateFiniteDifference @ℝ² 1 1e6 1e100
   , QC.testProperty "ℝ³" $ coordinateFiniteDifference @ℝ³ 1 1e6 1e100
   , QC.testProperty "(ℝ,ℝ)" $ coordinateFiniteDifference @(ℝ,ℝ) 1 1e6 1e100
   , QC.testProperty "S¹" $ coordinateFiniteDifference @S¹ 1 1e6 (2*pi)
   , QC.testProperty "S² (unlimited)"
         . QC.expectFailure $ coordinateFiniteDifference @S² 0.5 pi (2*pi)
   , QC.testProperty "S²" $ \p@(S²Polar θ _)
         -> let poleDist = sin θ
            in poleDist > 0.1
                 ==> coordinateFiniteDifference @S² (poleDist^2 * 1e-6)
                                                    (poleDist/2)
                                                    (2*pi) p
   ]
  , testGroup "Location"
   [ QC.testProperty "S²" $ \p v
          -> TangentBundle @S² p v ^. location's azimuth ≈ p^.azimuth
   ]
  , testGroup "x-coordinate diff"
   [ QC.testProperty "Access" $ \x y δx δy
             -> (TangentBundle (V2 x y) (V2 δx δy))
                    ^.delta xCoord ≈ δx
   , QC.testProperty "Update" $ \x y δx₀ δx₁ δy
                     -> (delta xCoord.~δx₁)
                         (TangentBundle (V2 x y) (V2 δx₀ δy))
                          ≈ TangentBundle (V2 x y) (V2 δx₁ δy) ]
  , testGroup "Spheres"
   [ testGroup "S¹"
    [ QC.testProperty "Azimuth access" $ \φ -> S¹Polar φ^.azimuth ≈ φ
    , QC.testProperty "Azimuth update" $ \p φ -> (azimuth .~ φ) p ≈ S¹Polar φ
    ]
   , testGroup "S²"
    [ QC.testProperty "Azimuth access" $ \θ φ -> S²Polar θ φ^.azimuth ≈ φ
    , QC.testProperty "Azimuth update" $ \θ φ₀ φ₁
               -> (azimuth .~ φ₁) (S²Polar θ φ₀) ≈ S²Polar θ φ₁
    , QC.testProperty "Zenith-distance access" $ \θ φ -> S²Polar θ φ^.zenithAngle ≈ θ
    , QC.testProperty "Zenith-distance update" $ \θ₀ θ₁ φ
               -> (zenithAngle .~ θ₁) (S²Polar θ₀ φ) ≈ S²Polar θ₁ φ
    , testGroup "Tangent space examples"
     [ testCase "Zenith-angle at equator | prime meridian"
         $ (TangentBundle @S² (S²Polar (pi/2-1e-6) 0) (V2 1 0))
              ^. delta zenithAngle @?≈ 1
     , testCase "Azimuth at just north of equator | prime meridian"
         $ (TangentBundle @S² (S²Polar (pi/2-1e-6) 0) (V2 0 1))
              ^. delta azimuth @?≈ 1
     , testCase "Azimuth at just north of equator | 90°E"
         $ (TangentBundle @S² (S²Polar (pi/2-1e-6) (pi/2)) (V2 1 0))
              ^. delta azimuth @?≈ -1
     , testCase "Azimuth at 45°N | prime meridian"
         $ (TangentBundle @S² (S²Polar (pi/4) 0) (V2 0 1))
              ^. delta azimuth @?≈ sqrt 2
     ]
    ]
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
            (S²Polar (pi/2) 0) (S²Polar (pi/2) 0) [V3 0 0 1] [V3 0 0 1]
   , testCase "Micro-movement on the equator"
        $ sphereParallelTransportTest
            (S²Polar (pi/2) 0) (S²Polar (pi/2) 1e-3) [V3 0 0 1] [V3 0 0 1]
   , testCase "Small movement on the equator (ez)"
        $ sphereParallelTransportTest
            (S²Polar (pi/2) 0) (S²Polar (pi/2) (pi/2)) [V3 0 0 1, V3   0  1 0]
                                                       [V3 0 0 1, V3 (-1) 0 0]
   , testCase "Big movement on the equator"
        $ sphereParallelTransportTest
            (S²Polar (pi/2) 0) (S²Polar (pi/2) 3) [V3 0 0 1] [V3 0 0 1]
   , testCase "Big negative movement on the equator"
        $ sphereParallelTransportTest
            (S²Polar (pi/2) 0) (S²Polar (pi/2) (-3)) [V3 0 0 1] [V3 0 0 1]
   , testCase "Movement on the zero meridian from north pole"
        $ sphereParallelTransportTest
            (S²Polar 0 0) (S²Polar (pi/2) 0) [V3 0 1 0] [V3 0 1 0]
   , testCase "Movement on the zero meridian to north pole"
        $ sphereParallelTransportTest
            (S²Polar (pi/2) 0) (S²Polar 0 0) [V3 0 1 0, V3   0  0 1]
                                             [V3 0 1 0, V3 (-1) 0 0]
   , testCase "Crossing the equator on the zero meridian"
        $ sphereParallelTransportTest
            (S²Polar (pi/4) 0) (S²Polar (3*pi/4) 0) [V3 0 1 0, V3 (-1) 0 1] 
                                                    [V3 0 1 0, V3   1  0 1]
   , testCase "Crossing the equator on the 90° meridian"
        $ sphereParallelTransportTest
            (S²Polar (pi/4) (pi/2)) (S²Polar (3*pi/4) (pi/2)) [V3 1 0 0, V3 0 (-1) 1]
                                                              [V3 1 0 0, V3 0   1  1]
   , testCase "Crossing the equator on the 180° meridian"
        $ sphereParallelTransportTest
            (S²Polar (pi/4) pi) (S²Polar (3*pi/4) pi) [V3 0 1 0, V3   1  0 1]
                                                      [V3 0 1 0, V3 (-1) 0 1]
   , testCase "Crossing the equator on the -90° meridian"
        $ sphereParallelTransportTest
            (S²Polar (pi/4) (-pi/2)) (S²Polar (3*pi/4) (-pi/2)) [V3 1 0 0, V3 0   1  1]
                                                                [V3 1 0 0, V3 0 (-1) 1]
   , QC.testProperty "Movement on the equator" . QC.expectFailure
        $ \(S¹Polar φ₀) (S¹Polar φ₁) -> assertParTransportNeedleTargetFixpoint @S²
                 (S²Polar 0 0, Just "north pole")
                 (S²Polar (pi/2) φ₀)
                 (S²Polar (pi/2) φ₁)
   , QC.testProperty "Just north of the equator"
        $ \p@(S¹Polar φ₀) q@(S¹Polar φ₁) -> abs (p.-~!q) < 2
            ==> assertParTransportNeedleTargetFixpoint @S²
                 (S²Polar 0 0, Just "north pole")
                 (S²Polar (pi/2-1e-13) φ₀)
                 (S²Polar (pi/2-1e-13) φ₁)
   , QC.testProperty "Just slightly crossing the equator"
        $ \(S¹Polar φ₀) (S¹Polar φ₁) -> assertParTransportNeedleTargetFixpoint @S²
                 (S²Polar 0 0, Just "north pole")
                 (S²Polar (pi/2-1e-13) φ₀)
                 (S²Polar (pi/2+1e-13) φ₁)
   , QC.testProperty "Just south of the equator"
        $ \p@(S¹Polar φ₀) q@(S¹Polar φ₁) -> abs (p.-~!q) < 2
            ==> assertParTransportNeedleTargetFixpoint @S²
                 (S²Polar pi 0, Just "south pole")
                 (S²Polar (pi/2+1e-13) φ₀)
                 (S²Polar (pi/2+1e-13) φ₁)
   , QC.testProperty "Movement on the zero meridian"
        $ \(S¹Polar θ₀) (S¹Polar θ₁) -> assertParTransportNeedleTargetFixpoint @S²
                 (S²Polar (pi/2) (pi/2), Nothing)
                 (S²Polar (abs θ₀) (if θ₀>0 then 0 else pi))
                 (S²Polar (abs θ₁) (if θ₁>0 then 0 else pi))
   , QC.testProperty "Rotation axis – heading-vector"
        $ \p v -> magnitude v < 1e6
              ==> let q = p .+~^ v :: S²
                      w = parallelTransport p v v
                      vCart :@. pCart = embed (v:@.p) :: TangentBundle ℝ³
                      wCart :@. qCart = embed (w:@.q) :: TangentBundle ℝ³
                      pxv = pCart`cross3`vCart
                      qxw = qCart`cross3`wCart
                    in QC.counterexample
                           ("  𝑝 = "++SP.show p++"\t ≃ "++SP.show pCart
                        ++"\n  𝑞 = "++SP.show q++"\t ≃ "++SP.show qCart
                        ++"\n  𝑣 = "++SP.show v++"\t = "++SP.show vCart++" @ 𝑝"
                        ++"\n  𝑤 = "++SP.show w++"\t = "++SP.show wCart++" @ 𝑞"
                        ++"\n𝑝×𝑣 = "++SP.show pxv    -- rotation axis
                        ++"\n𝑞×𝑤 = "++SP.show qxw    -- rotation axis
                             )
                       $ pxv ≈ qxw
   , QC.testProperty "Rotation axis – arbitrary vectors"
        $ \p v f -> let q = p .+~^ v :: S²
                        g = parallelTransport p v f :: Needle S²
                        fCart :@. pCart = embed (f :@. p) :: TangentBundle ℝ³
                        gCart :@. qCart = embed (g :@. q) :: TangentBundle ℝ³
                        infix 7 ×
                        (×) = cross3
                        pxq = pCart×qCart
                        fㄧg = fCart ^-^ gCart
                        ㄍ = magnitudeSq
                    in QC.counterexample
                           ("              𝑝 = "++SP.show p
                        ++"\n              𝑞 = "++SP.show q
                        ++"\n              𝑓 = "++SP.show f
                        ++"\n              𝑔 = "++SP.show g
                        ++"\n            𝑝×𝑞 = "++SP.show pxq  -- rotation axis
                        ++"\n          𝑓 − 𝑔 = "++SP.show fㄧg -- movement in the rot.-plane
                        ++"\n    (𝑝×𝑞)×(𝑓−𝑔) = "++SP.show (pxq × fㄧg)
                        ++"\n    (𝑝×𝑞)·(𝑓−𝑔) = "++SP.show (pxq <.> fㄧg)
                        ++"\n ‖(𝑝×𝑞)×(𝑓−𝑔)‖² = "++SP.show (ㄍ $ pxq × fㄧg)
                        ++"\n         ‖𝑝×𝑞‖² = "++SP.show (ㄍ pxq)
                        ++"\n         ‖𝑓−𝑔‖² = "++SP.show (ㄍ fㄧg)
                        ++"\n  ‖𝑝×𝑞‖²·‖𝑓−𝑔‖² = "++SP.show (ㄍ pxq*ㄍ fㄧg)
                             )
                       $ ㄍ (pxq × fㄧg)      -- Check that 𝑝×𝑞 and 𝑓−𝑔 are orthogonal.
                          ≈ ㄍ pxq * ㄍ fㄧg  -- (For orthogonal 𝐚 and 𝐛, we have
                                              -- ‖𝐚×𝐛‖ = ‖𝐚‖·‖𝐛‖.)
   ]
  ]
 , testGroup "Simplices"
  [ testGroup "Barycentric coordinates"
   [ QC.testProperty "In ℝ²"
      $ \p q r μ ν -> not (p≈q || q≈r || r≈p)
          ==> let λ = 1-μ-ν
              in toBarycentric (ℝ²Simplex p q r :: Simplex ℝ²)
                              (p^*λ ^+^ q^*μ ^+^ r^*ν)
                          ?≈! [   λ,       μ,       ν]
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
        $ map sort (toList $ directNeighbours (fromWebNodes euclideanMetric
                                       [(x, ()) | x<-[0, 0.1 .. 2]] :: PointsWeb ℝ () ))
          @?= [ [1,9], [0,2], [1,3], [2,4], [3], [6,12], [5,7], [6,8], [7,9], [0,8], [11,15]
              , [10,12],[5,11],[14,20],[13,15],[10,14],[17],[16,18],[17,19],[18,20],[13,19]
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
    , adjustOption (\(QC.QuickCheckTests n)
                        -> QC.QuickCheckTests (ceiling . sqrt $ fromIntegral n))
        $ testGroup "QuickCheck"
     [ QC.testProperty "Random 1D web should be strongly connected"
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
instance (SimpleSpace v, Needle v~v, Floating (Scalar v))
             => AEq (Shade' v) where
  fuzzyEq η (Shade' c₀ σ₀) (Shade' c₁ σ₁)
    = (σ₀|$|δ) < ε && (σ₀|$|δ) < ε
     && all (is1 . (σ₀|$|)) (normSpanningSystem' σ₁)
     && all (is1 . (σ₁|$|)) (normSpanningSystem' σ₀)
   where δ = c₁ ^-^ c₀
         ε = 1e-2 + realToFrac η
         is1 x = abs (x-1) < ε
instance ( SimpleSpace v, DualVector (Needle' v) ~ v
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
  fuzzyEq η (S¹Polar φ) (S¹Polar ϕ)
   | φ > pi/2, ϕ < -pi/2  = fuzzyEq η (S¹Polar $ φ - 2*pi) (S¹Polar ϕ)
   | ϕ > pi/2, φ < -pi/2  = fuzzyEq η (S¹Polar φ) (S¹Polar $ ϕ - 2*pi)
   | otherwise            = abs (φ - ϕ) < η
instance AEq S² where
  fuzzyEq η (S²Polar θ φ) (S²Polar ϑ ϕ)
   | φ > pi/2, ϕ < -pi/2  = fuzzyEq η (S²Polar θ $ φ - 2*pi) (S²Polar ϑ ϕ)
   | ϕ > pi/2, φ < -pi/2  = fuzzyEq η (S²Polar θ φ) (S²Polar ϑ $ ϕ - 2*pi)
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
  fuzzyEq η (HemisphereℝP¹Polar θ) (HemisphereℝP¹Polar ϑ)
   = fuzzyEq η (S¹Polar $ θ*2) (S¹Polar $ ϑ*2)
instance AEq ℝP² where
  fuzzyEq η (HemisphereℝP²Polar θ φ) (HemisphereℝP²Polar ϑ ϕ)
   | φ > pi/2, ϕ < -pi/2  = fuzzyEq η (HemisphereℝP²Polar θ $ φ - 2*pi) (HemisphereℝP²Polar ϑ ϕ)
   | ϕ > pi/2, φ < -pi/2  = fuzzyEq η (HemisphereℝP²Polar θ φ) (HemisphereℝP²Polar ϑ $ ϕ - 2*pi)
   | θ < pi/2             = abs (θ - ϑ) < η && abs (φ - ϕ) * θ < η
   | φ > pi/4, ϕ < -pi/4  = fuzzyEq η (HemisphereℝP²Polar (pi/2) $ φ - pi)
                                      (HemisphereℝP²Polar (pi/2) ϕ)
   | ϕ > pi/4, φ < -pi/4  = fuzzyEq η (HemisphereℝP²Polar (pi/2) φ)
                                      (HemisphereℝP²Polar (pi/2) $ ϕ - pi)
   | otherwise            = abs (φ - ϕ) < η

instance (AEq m, AEq f) => AEq (FibreBundle m f) where
  fuzzyEq η (FibreBundle p v) (FibreBundle q w) = fuzzyEq η p q && fuzzyEq η v w

instance (AEq a) => AEq [a] where
  fuzzyEq _ [] [] = True
  fuzzyEq η (x:xs) (y:ys) = fuzzyEq η x y && fuzzyEq η xs ys
  fuzzyEq _ _ _ = False
                                        
infix 1 @?≈       
(@?≈) :: (AEq e, Show e) => e -> e -> Assertion
a@?≈b
 | a≈b        = return ()
 | otherwise  = assertFailure $ "Expected "++show b++", but got "++show a

infix 4 ?≈!
(?≈!) :: (AEq e, SP.Show e) => e -> e -> QC.Property
a?≈!b = QC.counterexample ("Expected "++SP.show b++", but got "++SP.show a) $ a≈b

instance QC.Arbitrary ℝ² where
  arbitrary = (\(x,y)->V2 x y) <$> QC.arbitrary
  shrink (V2 x y) = V2 <$> ((/12)<$>QC.shrink (x*12))
                       <*> ((/12)<$>QC.shrink (y*12))
instance QC.Arbitrary ℝ³ where
  arbitrary = (\(x,y,z)->V3 x y z) <$> QC.arbitrary
  shrink (V3 x y z) = V3 <$> ((/12)<$>QC.shrink (x*12))
                         <*> ((/12)<$>QC.shrink (y*12))
                         <*> ((/12)<$>QC.shrink (z*12))

nearlyAssociative :: ∀ m . ( AEq m, Semimanifold m
                           , InnerSpace (Needle m), RealFloat (Scalar (Needle m)) )
                         => m -> Needle m -> Needle m -> QC.Property
nearlyAssociative p v w = maximum (map magnitude [v,w]) < 1e6
         ==> (p .+~^ v) .+~^ w ≈ (p .+~^ (v^+^w) :: m)

originCancellation :: ∀ m . (AEq m, PseudoAffine m, Show m, Show (Needle m))
                         => m -> m -> QC.Property
originCancellation p q = case p.-~.q of
      Just v
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
       => Scalar (Needle n) -> n -> Needle n -> QC.Property
embeddingTangentiality consistRadius p vub
         = QC.counterexample ("p+v = "++SP.show q++", coEmbed (embed p+v) = "++SP.show q')
            $ fuzzyEq (unitEpsilon @n * (1+rvub^2)) q q'
 where rvub = realToFrac $ magnitude vub
       v = vub ^* consistRadius
       q, q' :: n
       q = p .+~^ v
       q' = coEmbed $ (pEmbd .+~^ vEmbd :: m)
       TangentBundle pEmbd vEmbd = embed (TangentBundle p v)

nearbyTangentSpaceEmbedding :: ∀ m n
                     . ( Semimanifold m, Semimanifold n
                       , NaturallyEmbedded n m
                       , NaturallyEmbedded (TangentBundle n) (TangentBundle m)
                       , ParallelTransporting (->) n (Needle n)
                       , SP.Show n, SP.Show (Needle n), AEq (Needle n)
                       , InnerSpace (Needle n), RealFloat (Scalar (Needle n)) )
       => Scalar (Needle n) -> n -> Needle n -> Needle n -> QC.Property
nearbyTangentSpaceEmbedding consistRadius p vub f
         = QC.counterexample ("𝑓 embd. at 𝑝, then proj. at 𝑝+𝑣 = "++SP.show fReProj
                              ++", 𝑓 moved by 𝑣 = "++SP.show g)
            $ fuzzyEq (unitEpsilon @(Needle n) * (1+rvub^2)) g fReProj
 where rvub = realToFrac $ magnitude vub
       v = vub ^* consistRadius
       q :: n
       q = p .+~^ v :: n
       qEmbd = embed q :: m
       fReProj :@. _= coEmbed (fEmbd :@. qEmbd) :: TangentBundle n
       g = parallelTransport p v f
       fEmbd :@. pEmbd = embed (f:@.p) :: TangentBundle m

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
sphereParallelTransportTest p q [] [] = mempty
sphereParallelTransportTest p q (v:vs) (w:ws)
     = (parallelTransport p (q.-~!p) vSph @?≈ wSph)
        >> sphereParallelTransportTest p q vs ws
 where [vSph:@._, wSph:@._]
          = [ coEmbed (u :@. embed o :: TangentBundle ℝ³) :: TangentBundle S²
            | (o,u) <- [(p,v), (q,w)] ]


coordinateLensLaws :: ∀ m . ( Typeable m, HasCoordinates m
                            , Show m, Show (CoordinateIdentifier m)
                            , SP.Show m, AEq m
                            , QC.Arbitrary m, QC.Arbitrary (CoordinateIdentifier m) )
         => TestTree 
coordinateLensLaws = testGroup (show $ typeRep ([]::[m]))
           [ QC.testProperty "Retrieval" retrieval
           , QC.testProperty "Identity-pasting" idPasting
           , QC.testProperty "Putting twice" twicePutting
           ]
 where retrieval :: CoordinateIdentifier m -> m -> ℝ -> QC.Property
       retrieval c p a = (QC.counterexample ("Got back "++SP.show retrieved)
                      $ retrieved ≈ x)
        where retrieved = (coordinate c.~x) p ^. coordinate c
              x = constrainToRange (validCoordinateRange c p) a
       idPasting :: CoordinateIdentifier m -> m -> QC.Property
       idPasting c p = (QC.counterexample ("Putting the viewed coordinate back in gives "
                                           ++ SP.show backPasted)
                         $ backPasted ≈ p)
        where backPasted = coordinate c .~ (p^.coordinate c) $ p
       twicePutting :: CoordinateIdentifier m -> m -> ℝ -> QC.Property
       twicePutting c p a = (QC.counterexample ("Second putting made it "++SP.show dubPut)
                      $ dubPut ≈ singlyPut)
        where singlyPut = p & coordinate c .~ x
              dubPut = singlyPut & coordinate c .~ x
              x = constrainToRange (validCoordinateRange c p) a

constrainToRange :: (ℝ,ℝ) -> ℝ -> ℝ
constrainToRange (lul,uul) = \x -> sinh $ m + rd * tanh (asinh x / (4 + rd))
 where l = asinh $ max (-huge) lul
       u = asinh $ min   huge  uul
       rd = (u-l)/2
       m = l + rd
       huge = 1e9

-- | 'Prelude.asinh' is (as of GHC-8.2) unstable for negative arguments, see
--   <https://ghc.haskell.org/trac/ghc/ticket/14927>
asinh :: RealFloat a => a -> a
asinh x
 | x > 1e20   = log 2 + log x
 | x < 0      = -asinh (-x)
 | otherwise  = log $ x + sqrt (1 + x^2)



coordinateFiniteDifference :: ∀ m .
       ( Semimanifold m, HasCoordinates m
       , HasCoordinates (Needle m), CoordDifferential m
       , AEq (Needle m), InnerSpace (Needle m), Scalar (Needle m) ~ ℝ
       , SP.Show m )
     => ℝ    -- ^ Radius of consistency (within which we expect order-1 accuracy)
      -> ℝ   -- ^ Radius of stability (without we don't expect sensible results at all)
      -> ℝ   -- ^ Modularity
      -> m -> CoordinateIdentifier m -> Needle m -> QC.Property
coordinateFiniteDifference consistRadius stabilRadius modl p c vub
        = QC.counterexample ("Fin. diff: "++SP.show finitesimal
                             ++", tangential component: "++SP.show infinitesimal
                           ++"\n(q = "++SP.show q++")")
            $ rvub * consistRadius < stabilRadius
            ==> fuzzyEq (unitEpsilon @(Needle m) * (1+rvub^2))
                 (orthoCorrection + finitesimal) (orthoCorrection + infinitesimal)
 where rvub = realToFrac $ magnitude vub
       v = vub ^* consistRadius
       q = p .+~^ v
       infinitesimal = (FibreBundle p v ^. delta c)`mod'`modl
       finitesimal = (q^.coordinate c - p^.coordinate c)`mod'`modl
       orthoCorrection = signum infinitesimal


rotateAboutThenUndo :: Rotatable m => AxisSpace m -> S¹ -> m -> m
rotateAboutThenUndo ax g@(S¹Polar w) p
      = rotateAbout ax (S¹Polar $ -w) $ rotateAbout ax g p
