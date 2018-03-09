-- |
-- Module      : Math.Manifold.Core.Types
-- Copyright   : (c) Justus Sagemüller 2016
-- License     : GPL v3
-- 
-- Maintainer  : (@) sagemueller $ geo.uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 
-- Several low-dimensional manifolds, represented in some simple way as Haskell
-- data types. All these are in the 'PseudoAffine' class.
-- 


{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE PatternSynonyms          #-}


module Math.Manifold.Core.Types
        ( ℝ⁰, ℝ
        , S⁰(..), otherHalfSphere, S¹(..), pattern S¹, S²(..), pattern S²
        , D¹(..), fromIntv0to1, D²(..), pattern D²
        , ℝP⁰(..), ℝP¹(..), pattern ℝP¹, ℝP²(..), pattern ℝP²
        , Cℝay(..), CD¹(..)
        ) where

import Math.Manifold.Core.Types.Internal

import Data.VectorSpace
import Math.Manifold.VectorSpace.ZeroDimensional
import Data.AffineSpace
import Data.Basis
import Data.Void
import Data.Monoid





otherHalfSphere :: S⁰ -> S⁰
otherHalfSphere PositiveHalfSphere = NegativeHalfSphere
otherHalfSphere NegativeHalfSphere = PositiveHalfSphere

pattern S¹ :: Double -> S¹
pattern S¹ φ = S¹Polar φ

pattern ℝP¹ :: Double -> ℝP¹
pattern ℝP¹ r = UnitDiskℝP¹ r

pattern S² :: Double -> Double -> S²
pattern S² ϑ φ = S²Polar ϑ φ

pattern ℝP² :: Double -> Double -> ℝP²
pattern ℝP² r φ = UnitDiskℝP²Polar r φ

pattern D² :: Double -> Double -> D²
pattern D² r φ = D²Polar r φ


fromIntv0to1 :: ℝ -> D¹
fromIntv0to1 x | x<0        = D¹ (-1)
               | x>1        = D¹ 1
               | otherwise  = D¹ $ x*2 - 1




instance VectorSpace () where
  type Scalar () = ℝ
  _ *^ () = ()

instance HasBasis () where
  type Basis () = Void
  basisValue = absurd
  decompose () = []
  decompose' () = absurd
instance InnerSpace () where
  () <.> () = 0


