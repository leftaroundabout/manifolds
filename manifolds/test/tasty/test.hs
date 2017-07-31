-- |
-- Module      : Main
-- Copyright   : (c) Justus Sagemüller 2017
-- License     : GPL v3
-- 
-- Maintainer  : (@) sagemueller $ geo.uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 
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


main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests"
  [ testCase "Manually defining an empty web."
    $ toList (fst $ toGraph (PointsWeb (PlainLeaves []) :: PointsWeb ℝ⁰ ())) @?= []
  , testCase "Manually defining a single-point web."
    $ toList (fst $ toGraph (PointsWeb (
         PlainLeaves [ (zeroV, Neighbourhood () mempty euclideanNorm Nothing) ]
       ) :: PointsWeb ℝ⁰ ())) @?= [[]]
  ]



