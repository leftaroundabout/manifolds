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
import Data.Manifold.PseudoAffine
import Data.Manifold.Shade
import Data.Manifold.Web
import Data.Manifold.Web.Internal
import Data.Manifold.Function.LocalModel

import Data.VectorSpace
import Math.LinearMap.Category

import Data.Foldable (toList)
import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.List.NonEmpty as NE

import qualified Prelude as Hask

import Control.Category.Constrained.Prelude
import Control.Arrow.Constrained
import Control.Monad.Constrained

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


adjustMetricToModel :: ∀ x y ㄇ . (ModellableRelation x y, LocalModel ㄇ)
                 => InterpolationFunction ㄇ x y -> InterpolationFunction ㄇ x y
adjustMetricToModel = _interpWeb >>> webLocalInfo
    >>> \(PointsWeb w) -> InterpolationFunction . PointsWeb $ fmap remetricise w
 where remetricise :: Neighbourhood x (WebLocally x (ㄇ x y))
             -> Neighbourhood x (ㄇ x y)
       remetricise nd = nd & dataAtNode .~ localModel
                           & localScalarProduct .~ newNorm
        where localModel = nd^.dataAtNode.thisNodeData
              newNorm = spanNorm
                  [ dx ^/ ((0.1 + occlusion (ngb^.thisNodeData.tweakLocalOffset)
                                            (fromInterior ySynth))
                           * (dx<.>^δx))
                  | (δx,ngb) <- concat . take 2 $ localOnion (nd^.dataAtNode) []
                  , let dx = nd^.localScalarProduct<$|δx
                        Shade' ySynth _ = evalLocalModel localModel δx ]
                      :: Metric x


upsampleAtLargeDist :: (ModellableRelation x y, LocalModel ㄇ)
                 => ℝ -> InterpolationFunction ㄇ x y -> PointsWeb x (Shade' y)
upsampleAtLargeDist dmax (InterpolationFunction web)
     = fromWebNodes (\(Shade x _) -> case nearestNeighbour webI (fromInterior x) of
                         Just (_,nearest) -> nearest ^. nodeLocalScalarProduct) $ do
          local <- toList webI
          (local^.thisNodeCoord, evalLocalModel (local^.thisNodeData) zeroV) : do 
             (ngId, (δx, ngb)) <- local^.nodeNeighbours
             guard (ngId > local^.thisNodeId
                   && (local^.nodeLocalScalarProduct|$|δx) > dmax)
             return ( local^.thisNodeCoord !+~^ δx^/2
                    , evalLocalModel (local^.thisNodeData) $ δx^/2 )
 where webI = webLocalInfo web
