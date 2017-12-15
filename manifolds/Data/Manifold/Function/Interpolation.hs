-- |
-- Module      : Data.Manifold.Function.Interpolation
-- Copyright   : (c) Justus Sagemüller 2017
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsagemue $ uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 

{-# LANGUAGE ScopedTypeVariables      #-}
{-# LANGUAGE UnicodeSyntax            #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE TupleSections            #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE UndecidableInstances     #-}
{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE StandaloneDeriving       #-}
{-# LANGUAGE TemplateHaskell          #-}
{-# LANGUAGE ConstraintKinds          #-}

module Data.Manifold.Function.Interpolation (
      InterpolationFunction
    ) where


import Data.Manifold.Types
import Data.Manifold.Types.Primitive ((^))
import Data.Manifold.Shade
import Data.Manifold.Web
import Data.Manifold.Web.Internal
import Data.Manifold.Function.LocalModel

import Data.VectorSpace
import Math.LinearMap.Category

import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.List.NonEmpty as NE

import qualified Prelude as Hask

import Control.Category.Constrained.Prelude
import Control.Arrow.Constrained

import Control.Lens
import Control.Lens.TH


newtype InterpolationFunction ㄇ x y = InterpolationFunction {
      _interpWeb :: PointsWeb x (ㄇ x y)
    }
makeLenses ''InterpolationFunction


fromPointsWeb :: (ModellableRelation x y, LocalModel ㄇ)
                 => PointsWeb x (Shade' y) -> InterpolationFunction ㄇ x y
fromPointsWeb = InterpolationFunction . localFmapWeb (
                 \locInfo -> case fitLocally $
                                    (zeroV, locInfo^.thisNodeData)
                                  : [ (ngbx, ngb^.thisNodeData)
                                    | (ngbx,ngb) <- concat $ localOnion locInfo []] of
                                 Just locModl -> locModl )
