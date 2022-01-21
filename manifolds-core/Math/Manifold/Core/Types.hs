-- |
-- Module      : Math.Manifold.Core.Types
-- Copyright   : (c) Justus Sagemüller 2016
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsag $ hvl.no
-- Stability   : experimental
-- Portability : portable
-- 
-- Several low-dimensional manifolds, represented in some simple way as Haskell
-- data types. All these are in the 'PseudoAffine' class.
-- 


{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE PatternSynonyms          #-}
{-# LANGUAGE ViewPatterns             #-}


module Math.Manifold.Core.Types
        ( EmptyMfd(..), ℝ⁰, ℝ
        , S⁰, S⁰_(..), otherHalfSphere, S¹, S¹_(..), pattern S¹, S², S²_(..), pattern S²
        , D¹, D¹_(..), fromIntv0to1, D², D²_(..), pattern D²
        , ℝP⁰, ℝP⁰_(..), ℝP¹, ℝP¹_(..), pattern ℝP¹, ℝP², ℝP²_(..), pattern ℝP²
        , Cℝay, Cℝay_(..), CD¹, CD¹_(..)
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

{-# DEPRECATED S¹ "Use Math.Manifold.Core.Types.S¹Polar" #-}
pattern S¹ :: Double -> S¹
pattern S¹ φ = S¹Polar φ

{-# DEPRECATED ℝP¹ "Use Math.Manifold.Core.Types.HemisphereℝP¹Polar (notice: different range)" #-}
pattern ℝP¹ :: Double -> ℝP¹
pattern ℝP¹ r <- (HemisphereℝP¹Polar ((2/pi*)->r))
 where ℝP¹ r = HemisphereℝP¹Polar $ r * pi/2

{-# DEPRECATED S² "Use Math.Manifold.Core.Types.S²Polar" #-}
pattern S² :: Double -> Double -> S²
pattern S² ϑ φ = S²Polar ϑ φ

{-# DEPRECATED ℝP² "Use Math.Manifold.Core.Types.HemisphereℝP²Polar (notice: different range)" #-}
pattern ℝP² :: Double -> Double -> ℝP²
pattern ℝP² r φ <- (HemisphereℝP²Polar ((2/pi*)->r) φ)
 where ℝP² r φ = HemisphereℝP²Polar (r * pi/2) φ

{-# DEPRECATED D² "Use Math.Manifold.Core.Types.D²Polar" #-}
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


