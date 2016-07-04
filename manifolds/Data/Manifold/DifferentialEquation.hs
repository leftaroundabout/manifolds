-- |
-- Module      : Data.Manifold.DifferentialEquation
-- Copyright   : (c) Justus Sagemüller 2016
-- License     : GPL v3
-- 
-- Maintainer  : (@) sagemueller $ geo.uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE ParallelListComp           #-}
{-# LANGUAGE UnicodeSyntax              #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE PatternGuards              #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE LiberalTypeSynonyms        #-}


module Data.Manifold.DifferentialEquation (
            -- * Formulating simple differential eqns.
              DifferentialEqn
            , constLinearDEqn
            , filterDEqnSolution_static, iterateFilterDEqn_static
            -- * Cost functions for error bounds
            , maxDeviationsGoal
            , uncertaintyGoal
            , uncertaintyGoal'
            , euclideanVolGoal
            ) where


import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE
import Data.Semigroup

import Data.VectorSpace
import Data.LinearMap.HerMetric
import Data.LinearMap.Category
import Data.AffineSpace
import Data.Basis

import Data.Manifold.Types
import Data.Manifold.PseudoAffine
import Data.Function.Differentiable
import Data.Function.Differentiable.Data
import Data.Manifold.TreeCover
import Data.Manifold.Web

import qualified Numeric.LinearAlgebra.HMatrix as HMat
import qualified Data.List as List

import qualified Prelude as Hask hiding(foldl, sum, sequence)
import qualified Control.Applicative as Hask
import qualified Control.Monad       as Hask hiding(forM_, sequence)
import qualified Data.Foldable       as Hask
import qualified Data.Traversable as Hask

import Control.Category.Constrained.Prelude hiding
     ((^), all, elem, sum, forM, Foldable(..), foldr1, Traversable, traverse)
import Control.Arrow.Constrained
import Control.Monad.Constrained hiding (forM)
import Data.Foldable.Constrained
import Data.Traversable.Constrained (Traversable, traverse)


constLinearDEqn :: (WithField ℝ LinearManifold x, WithField ℝ LinearManifold y)
              => Linear ℝ (DualSpace y) (Linear ℝ y x) -> DifferentialEqn x y
constLinearDEqn bwt = factoriseShade
    >>> \(_x, Shade y δy) -> let j = bwt'm HMat.<\> (asPackedVector y)
                                 δj = bwt' `transformMetric` recipMetric δy
                             in Shade' (fromPackedVector j) δj
 where bwt'@(DenseLinear bwt'm) = adjoint bwt


-- | A function that variates, relatively speaking, most strongly
--   for arguments around 1. In the zero-limit it approaches a constant
--   (but with arbitrarily large derivative); for η → ∞ the derivative
--   approaches 0.
--   
--   The idea is that if you consider the ratio of two function values,
--   it will be close to 1 if both arguments on the same side of 1,
--   even if their ratio is large.
--   Only if both arguments are close to 1, or lie on opposite sides
--   of it, will the ratio of the function values will be significant.
goalSensitive :: ℝ -> ℝ
goalSensitive η =  0.3 + sqrt (η * (1 + η/(1+η)) / (3 + η))

euclideanVolGoal :: WithField ℝ EuclidSpace y => ℝ -> x -> Shade' y -> ℝ
euclideanVolGoal vTgt _ (Shade' _ shy) = goalSensitive η
 where η = euclideanRelativeMetricVolume shy / vTgt

maxDeviationsGoal :: WithField ℝ EuclidSpace y => [Needle y] -> x -> Shade' y -> ℝ
maxDeviationsGoal = uncertaintyGoal . projector's

uncertaintyGoal :: WithField ℝ EuclidSpace y => Metric' y -> x -> Shade' y -> ℝ
uncertaintyGoal = uncertaintyGoal' . const

uncertaintyGoal' :: WithField ℝ EuclidSpace y => (x -> Metric' y) -> x -> Shade' y -> ℝ
uncertaintyGoal' f x (Shade' _ shy)
         = List.sum [goalSensitive $ 1 / metricSq' m q | q <- shySpan]
 where shySpan = eigenSpan' shy
       m = f x
