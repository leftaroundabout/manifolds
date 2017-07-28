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

import Data.Manifold.Web

import Test.Tasty
import Test.Tasty.HUnit



main = defaultMain tests



tests :: TestTree
tests = testGroup "Tests"
  [
  ]



