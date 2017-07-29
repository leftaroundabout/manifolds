-- |
-- Module      : Data.Manifold.Web.DataStructure
-- Copyright   : (c) Justus Sagemüller 2017
-- License     : GPL v3
-- 
-- Maintainer  : (@) sagemueller $ geo.uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE TemplateHaskell            #-}


module Data.Manifold.Web.DataStructure where


import qualified Data.Vector.Unboxed as UArr

import Data.Manifold.Types
import Data.Manifold.PseudoAffine
import Data.Manifold.Shade
import Data.Manifold.TreeCover
import Data.Function.Affine
import Data.VectorSpace (Scalar)
import Math.LinearMap.Category (SimpleSpace)
    
import qualified Data.Foldable       as Hask
import qualified Data.Traversable as Hask
import qualified Data.Foldable.Constrained as CCt

import Control.DeepSeq

import GHC.Generics (Generic)

import Control.Lens.TH



type WebNodeId = Int
type WebNodeIdOffset = Int

data Neighbourhood x y = Neighbourhood {
     _dataAtNode :: y
   , _neighbours :: UArr.Vector WebNodeIdOffset
   , _localScalarProduct :: Metric x
   , _webBoundaryAtNode :: Maybe (Needle' x)
   }
  deriving (Generic, Functor, Foldable, Traversable)
makeLenses ''Neighbourhood

deriving instance ( WithField ℝ PseudoAffine x
                  , SimpleSpace (Needle x), Show (Needle' x), Show y )
             => Show (Neighbourhood x y)

data WebLocally x y = LocalWebInfo {
      _thisNodeCoord :: x
    , _thisNodeData :: y
    , _thisNodeId :: WebNodeId
    , _nodeNeighbours :: [(WebNodeId, (Needle x, WebLocally x y))]
    , _nodeLocalScalarProduct :: Metric x
    , _webBoundingPlane :: Maybe (Needle' x)
    } deriving (Generic)
makeLenses ''WebLocally

data NeighbourhoodVector x = NeighbourhoodVector
          { _nvectId :: Int
          , _theNVect :: Needle x
          , _nvectNormal :: Needle' x
          , _nvectLength :: Scalar (Needle x)
          , _otherNeighboursOverlap :: Scalar (Needle x)
          }
makeLenses ''NeighbourhoodVector

data PropagationInconsistency x υ = PropagationInconsistency {
      _inconsistentPropagatedData :: [(x,υ)]
    , _inconsistentAPrioriData :: υ }
  | PropagationInconsistencies [PropagationInconsistency x υ]
 deriving (Show)
makeLenses ''PropagationInconsistency

instance Monoid (PropagationInconsistency x υ) where
  mempty = PropagationInconsistencies []
  mappend p q = mconcat [p,q]
  mconcat = PropagationInconsistencies

instance (NFData x, NFData (Metric x), NFData (Needle' x), NFData y)
           => NFData (Neighbourhood x y)

-- | A 'PointsWeb' is almost, but not quite a mesh. It is a stongly connected†
--   directed graph, backed by a tree for fast nearest-neighbour lookup of points.
-- 
--   †In general, there can be disconnected components, but every connected
--   component is strongly connected.
newtype PointsWeb :: * -> * -> * where
   PointsWeb :: {
       webNodeRsc :: x`Shaded`Neighbourhood x y
     } -> PointsWeb x y
  deriving (Generic, Functor, Foldable, Traversable)

instance (NFData x, NFData (Metric x), NFData (Needle' x), NFData y) => NFData (PointsWeb x y)

instance CCt.Foldable (PointsWeb x) (->) (->) where
  ffoldl = uncurry . Hask.foldl' . curry
  foldMap = Hask.foldMap


data WebChunk x y = WebChunk {
     _thisChunk :: PointsWeb x y
   , _layersAroundChunk :: [(x`Shaded`Neighbourhood x y, WebNodeId)]
   }

makeLenses ''WebChunk

data NodeInWeb x y = NodeInWeb {
     _thisNodeOnly :: (x, Neighbourhood x y)
   , _layersAroundNode :: [(x`Shaded`Neighbourhood x y, WebNodeId)]
   }
makeLenses ''NodeInWeb

type MetricChoice x = Shade x -> Metric x


