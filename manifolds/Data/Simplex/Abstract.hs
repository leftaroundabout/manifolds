-- |
-- Module      : Data.Simplex.Abstract
-- Copyright   : (c) Justus Sagemüller 2018
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsagemue $ uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 

{-# LANGUAGE TypeFamilies             #-}

module Data.Simplex.Abstract where

import Data.Manifold.Types.Primitive

data family AbstractSimplex v x

data instance AbstractSimplex ℝ⁰ x = ℝ⁰Simplex !x
data instance AbstractSimplex ℝ  x = ℝ¹Simplex !x !x
data instance AbstractSimplex ℝ² x = ℝ²Simplex !x !x !x
data instance AbstractSimplex ℝ³ x = ℝ³Simplex !x !x !x !x
data instance AbstractSimplex ℝ⁴ x = ℝ⁴Simplex !x !x !x !x !x
