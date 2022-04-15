-- |
-- Module      : Data.Manifold.DifferentialEquation
-- Copyright   : (c) Justus Sagemüller 2016
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsag $ hvl.no
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
              DifferentialEqn, ODE
            , constLinearDEqn
            , constLinearODE
            , iterateFilterDEqn_static
            -- * Cost functions for error bounds
            , maxDeviationsGoal
            , uncertaintyGoal
            , uncertaintyGoal'
            , euclideanVolGoal
            -- * Solver configuration
            , InconsistencyStrategy(..)
            ) where


import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE

import Data.VectorSpace
import Data.VectorSpace.Free
import Math.LinearMap.Category
import Data.AffineSpace
import Data.Basis

import Data.Manifold.Types
import Data.Manifold.PseudoAffine
import Data.Manifold.Shade
import Data.Manifold.Function.LocalModel
import Data.Function.Differentiable
import Data.Function.Differentiable.Data
import Data.Manifold.TreeCover
import Data.Manifold.Web
import Data.Manifold.Atlas

import Data.Embedding

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

import Control.Lens

-- | An ordinary differential equation is one that does not need any a-priori
--   partial derivatives to compute the derivative for integration in some
--   propagation direction. Classically, ODEs are usually understood as
--   @DifferentialEquation ℝ ℝ⁰ y@, but actually @x@ can at least
--   be an arbitrary one-dimensional space (i.e. basically real intervals or 'S¹').
--   In these cases, there is always only one partial derivative: that which we
--   integrate over, in the only possible direction for propagation.
type ODE x y = DifferentialEqn QuadraticModel x y

constLinearDEqn :: ∀ x y . ( SimpleSpace x
                           , SimpleSpace y, AffineManifold y
                           , Scalar x ~ ℝ, Scalar y ~ ℝ )
              => (y +> (x +> y)) -> ((x +> y) +> y) -> DifferentialEqn QuadraticModel x y
constLinearDEqn = case ( linearManifoldWitness :: LinearManifoldWitness x
                       , dualSpaceWitness :: DualSpaceWitness x
                       , linearManifoldWitness :: LinearManifoldWitness y
                       , dualSpaceWitness :: DualSpaceWitness y ) of
   ( LinearManifoldWitness, DualSpaceWitness
    ,LinearManifoldWitness, DualSpaceWitness ) -> \bwt'inv bwt' ->
        \(Shade (_x,y) δxy) -> LocalDifferentialEqn
         { _rescanDifferentialEqn
            = \(QuadraticModel shy' shj'Apriori _) ->
               let shy = dualShade shy'
                   shjApriori = dualShade shj'Apriori
                in ( mixShade's $ shy
                             :| [ projectShade
                                   (Embedding (arr bwt'inv)
                                              (arr bwt'))
                                   shjApriori ]
                   , return $ projectShade
                                   (Embedding (arr bwt')
                                              (arr bwt'inv))
                                   shy
                   )
         }

constLinearODE :: ∀ x y . ( SimpleSpace x, Scalar x ~ ℝ
                          , AffineManifold y, SimpleSpace y, Scalar y ~ ℝ )
              => ((x +> y) +> y) -> ODE x y
constLinearODE = case ( linearManifoldWitness :: LinearManifoldWitness x
                      , dualSpaceWitness :: DualSpaceWitness x
                      , linearManifoldWitness :: LinearManifoldWitness y
                      , dualSpaceWitness :: DualSpaceWitness y ) of
   ( LinearManifoldWitness, DualSpaceWitness
    ,LinearManifoldWitness, DualSpaceWitness ) -> \bwt' ->
    let bwt'inv = pseudoInverse bwt'
    in \(Shade (_x,y) δxy) -> LocalDifferentialEqn
            (\(QuadraticModel shy' _ _) ->
                    let shy = dualShade shy'
                    in ( return $ shy & shadeNarrowness %~ scaleNorm 0.01
                       , return $ projectShade (Embedding (arr bwt')
                                                          (arr bwt'inv)) shy )
            )


-- | A function that variates, relatively speaking, most strongly
--   for arguments around 1. In the zero-limit it approaches a constant
--   (but with arbitrarily large derivative); for η → ∞ the derivative
--   approaches 0.
--   
--   The idea is that if you consider the ratio of two function values,
--   it will be close to 1 if either both arguments are much smaller or both
--   much larger than 1, even if the ratio of these arguments is large.
--   Only if both arguments are close to 1, or lie on opposite sides
--   of it, will the ratio of the function values will be significant.
goalSensitive :: ℝ -> ℝ
goalSensitive η =  0.3 + sqrt (η * (1 + η/(1+η)) / (3 + η))

euclideanVolGoal :: (WithField ℝ EuclidSpace y, SimpleSpace (Needle y))
                          => ℝ -> x -> Shade' y -> ℝ
euclideanVolGoal vTgt _ (Shade' _ shy) = goalSensitive η
 where η = euclideanRelativeMetricVolume shy / vTgt

euclideanRelativeMetricVolume :: (SimpleSpace y, HilbertSpace y) => Norm y -> Scalar y
euclideanRelativeMetricVolume (Norm m) = recip . roughDet . arr $ ue . m
 where Norm ue = euclideanNorm

maxDeviationsGoal :: (WithField ℝ EuclidSpace y, SimpleSpace (Needle y))
                        => [Needle y] -> x -> Shade' y -> ℝ
maxDeviationsGoal = uncertaintyGoal . spanNorm

uncertaintyGoal :: (WithField ℝ EuclidSpace y, SimpleSpace (Needle y))
                      => Metric' y -> x -> Shade' y -> ℝ
uncertaintyGoal = uncertaintyGoal' . const

uncertaintyGoal' :: (WithField ℝ EuclidSpace y, SimpleSpace (Needle y))
                         => (x -> Metric' y) -> x -> Shade' y -> ℝ
uncertaintyGoal' f x (Shade' _ shy)
         = List.sum [goalSensitive $ 1 / normSq m q | q <- shySpan]
 where shySpan = normSpanningSystem shy
       m = f x
