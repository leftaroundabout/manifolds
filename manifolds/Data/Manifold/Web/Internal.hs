-- |
-- Module      : Data.Manifold.Web.Internal
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
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE UnicodeSyntax              #-}


module Data.Manifold.Web.Internal where


import qualified Data.Vector.Unboxed as UArr

import Data.Manifold.Types
import Data.Manifold.PseudoAffine
import Data.Manifold.Shade
import Data.Manifold.TreeCover
import Data.Function.Affine
import Data.VectorSpace (Scalar)
import Math.LinearMap.Category (SimpleSpace, LSpace)
    
import qualified Data.Foldable       as Hask
import qualified Data.Traversable as Hask
import qualified Data.List.NonEmpty as NE
import Data.List.NonEmpty (NonEmpty((:|)))
import qualified Data.Foldable.Constrained as CCt
import Data.Functor.Identity
import Data.Function ((&))
import Control.Arrow
import Control.Comonad

import Control.DeepSeq

import GHC.Generics (Generic)

import Control.Lens
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


traverseInnermostChunks :: ∀ f x y z . ( Applicative f
                                       , WithField ℝ Manifold x, LSpace (Needle x) )
          => (WebChunk x y -> f (PointsWeb x z)) -> PointsWeb x y -> f (PointsWeb x z)
traverseInnermostChunks f = go []
 where go :: [(x`Shaded`Neighbourhood x y, WebNodeId)] -> PointsWeb x y -> f (PointsWeb x z)
       go outlayers (w@(PointsWeb (PlainLeaves _)))
         = f (WebChunk w outlayers) 
       go outlayers (PointsWeb w) = PointsWeb <$> traverseTrunkBranchChoices travel w
        where travel :: (Int, (Shaded x (Neighbourhood x y)))
                 -> Shaded x (Neighbourhood x y)
                 -> f (Shaded x (Neighbourhood x z))
              travel (i₀, br) obrs
                  = webNodeRsc <$> go ((obrs,i₀) : outlayers) (PointsWeb br)

traverseNodesInEnvi :: ∀ f x y z . ( Applicative f
                                   , WithField ℝ Manifold x, LSpace (Needle x) )
           => (NodeInWeb x y -> f (Neighbourhood x z))
             -> PointsWeb x y -> f (PointsWeb x z)
traverseNodesInEnvi f = traverseInnermostChunks fc
 where fc :: WebChunk x y -> f (PointsWeb x z)
       fc (WebChunk (PointsWeb (PlainLeaves lvs)) outlayers)
            = PointsWeb . PlainLeaves <$> Hask.traverse fn (ixedFoci lvs)
        where fn ((i, (x, ngbh)), nearbyLeaves)
               = (x,) <$> f (NodeInWeb (x,ngbh)
                                     $ (PlainLeaves nearbyLeaves, i) : outlayers)

fmapNodesInEnvi :: ( WithField ℝ Manifold x, LSpace (Needle x) )
           => (NodeInWeb x y -> Neighbourhood x z) -> PointsWeb x y -> (PointsWeb x z)
fmapNodesInEnvi f = runIdentity . traverseNodesInEnvi (Identity . f)


ixedFoci :: [a] -> [((Int, a), [a])]
ixedFoci = go 0
 where go _ [] = []
       go i (x:xs) = ((i,x), xs) : map (second (x:)) (go (i+1) xs)
 


jumpNodeOffset :: WebNodeIdOffset -> NodeInWeb x y -> NodeInWeb x y
jumpNodeOffset 0 node = node
jumpNodeOffset δi (NodeInWeb x environment)
   = case zoomoutWebChunk δie $ WebChunk (PointsWeb $ PlainLeaves [x]) environment of
       (WebChunk bigChunk envi', δi')
           -> case pickNodeInWeb bigChunk δi' of
              NodeInWeb x' envi'' -> NodeInWeb x' $ envi'' ++ envi'
 where δie | δi < 0     = δi
           | otherwise  = δi - 1

webAroundChunk :: WebChunk x y -> PointsWeb x y
webAroundChunk (WebChunk chunk []) = chunk
webAroundChunk (WebChunk (PointsWeb (PlainLeaves lvs))
                         ((PlainLeaves lvsAround, i) : envi))
   = webAroundChunk $ WebChunk (PointsWeb . PlainLeaves $ lvsBefore++lvs++lvsAfter) envi
 where (lvsBefore, lvsAfter) = splitAt i lvsAround
webAroundChunk (WebChunk (PointsWeb chunk)
                         ((OverlappingBranches nw ew (DBranch dir
                            (Hourglass (PlainLeaves[]) d) :| brs), 0) : envi))
   = webAroundChunk $ WebChunk (PointsWeb $ OverlappingBranches nw ew
                                          (DBranch dir (Hourglass chunk d) :| brs))
                               envi
webAroundChunk (WebChunk (PointsWeb chunk)
                         ((OverlappingBranches nw ew (DBranch dir
                            (Hourglass u (PlainLeaves[])) :| brs), i) : envi))
 | i==nLeaves u
   = webAroundChunk $ WebChunk (PointsWeb $ OverlappingBranches nw ew
                                          (DBranch dir (Hourglass u chunk) :| brs))
                               envi
webAroundChunk (WebChunk chunk
                         (( OverlappingBranches nw ew (br₀@(DBranch _ (Hourglass u d))
                                                          :|br₁:brs)
                          , i) : envi))
  = case webAroundChunk (WebChunk chunk [(OverlappingBranches nw ew (br₁:|brs), i')])
      of PointsWeb (OverlappingBranches nw' ew' (br₁':|brs'))
           -> webAroundChunk $ WebChunk
                    (PointsWeb $ OverlappingBranches nw' ew' (br₀:|br₁':brs'))
                    envi
 where i' = i - nLeaves u - nLeaves d
webAroundChunk (WebChunk _ ((OverlappingBranches nw ew branches, i):_))
    = error $ "Environment with branch sizes "++show (fmap nLeaves . Hask.toList<$>(Hask.toList branches))
                ++" does not have a gap at #"++show i
webAroundChunk (WebChunk _ ((PlainLeaves _, _):_))
    = error "Encountered non-PlainLeaves chunk in a PlainLeaves environment."


zoomoutWebChunk :: WebNodeIdOffset -> WebChunk x y -> (WebChunk x y, WebNodeId)
zoomoutWebChunk δi (WebChunk chunk ((outlayer, olp) : outlayers))
  | δi < -olp || δi >= nLeaves outlayer - olp
      = zoomoutWebChunk δiOut $ WebChunk widerChunk outlayers
  | otherwise  = (WebChunk widerChunk outlayers, δiIn)
 where δiOut | δi < 0     = δi + olp
             | otherwise  = δi + olp - nLeaves outlayer
       δiIn | δi < 0     = δi + olp
            | otherwise  = δi + olp + nLeaves (webNodeRsc chunk)
       widerChunk = webAroundChunk $ WebChunk chunk [(outlayer,olp)]

pickNodeInWeb :: PointsWeb x y -> WebNodeId -> NodeInWeb x y
pickNodeInWeb (PointsWeb w) i
  | i<0 || i>=n  = error
     $ "Trying to pick node #"++show i++" in web with "++show n++" nodes."
 where n = nLeaves w
pickNodeInWeb (PointsWeb (PlainLeaves lvs)) i
  | (preds, node:succs)<-splitAt i lvs
                   = NodeInWeb node [(PlainLeaves $ preds++succs, i)]
pickNodeInWeb (PointsWeb (OverlappingBranches nw ew (DBranch dir (Hourglass u d):|brs))) i
  | i < nu     = pickNodeInWeb (PointsWeb u) i
                      & layersAroundNode %~ ((OverlappingBranches (nw-nu) ew
                                               (DBranch dir (Hourglass gap d):|brs) ,0):)
  | i < nu+nd  = pickNodeInWeb (PointsWeb d) (i-nu)
                      & layersAroundNode %~ ((OverlappingBranches (nw-nd) ew
                                               (DBranch dir (Hourglass u gap):|brs) ,nu):)
  | (b:rs)<-brs
    = pickNodeInWeb (PointsWeb $ OverlappingBranches (nw-nu-nd) ew (b:|rs)) (i-nu-nd)
                      & layersAroundNode . ix 0
                           %~ \(OverlappingBranches nwe ewe brse, ne)
                                 -> ( OverlappingBranches (nwe+nu+nd) ewe
                                       $ NE.cons (DBranch dir (Hourglass u d)) brse
                                    , ne+nu+nd )
 where gap = PlainLeaves []
       [nu,nd] = nLeaves<$>[u,d]


webLocalInfo :: ∀ x y . WithField ℝ Manifold x
            => PointsWeb x y -> PointsWeb x (WebLocally x y)
webLocalInfo = runIdentity . traverseNodesInEnvi (Identity . linkln)
 where linkln :: NodeInWeb x y -> Neighbourhood x (WebLocally x y)
       linkln node@(NodeInWeb (x, locloc@(Neighbourhood y ngbs metric nBoundary)) envis)
           = locloc & dataAtNode .~ LocalWebInfo {
                  _thisNodeCoord = x
                , _thisNodeData = y
                , _thisNodeId = i
                , _nodeNeighbours = [ (i + δi, (δx, ngb))
                                    | δi <- UArr.toList ngbs
                                    , let ngbNode@(NodeInWeb (xn, _) _)
                                              = jumpNodeOffset δi node
                                          Just δx = xn .-~. x
                                          Neighbourhood ngb _ _ _ = linkln ngbNode ]
                , _nodeLocalScalarProduct = metric
                , _webBoundingPlane = nBoundary
                }
        where i = foldr ((+) . snd) 0 envis


instance Functor (WebLocally x) where
  fmap f (LocalWebInfo co dt id ng sp bn)
       = LocalWebInfo co (f dt) id (map (second . second $ fmap f) ng) sp bn
instance WithField ℝ Manifold x => Comonad (WebLocally x) where
  extract = _thisNodeData
  extend f this@(LocalWebInfo co _ id ng sp bn)
      = LocalWebInfo co (f this) id (map (second . second $ extend f) ng) sp bn
  duplicate this@(LocalWebInfo co _ id ng sp bn)
      = LocalWebInfo co this id (map (second $ second duplicate) ng) sp bn

-- ^ 'fmap' from the co-Kleisli category of 'WebLocally'.
localFmapWeb :: WithField ℝ Manifold x
                => (WebLocally x y -> z) -> PointsWeb x y -> PointsWeb x z
localFmapWeb f = webLocalInfo >>> fmap f

