-- |
-- Module      : Data.Manifold.Web
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
{-# LANGUAGE TemplateHaskell            #-}


module Data.Manifold.Web (
              -- * The web data type
              PointsWeb
              -- ** Construction
            , fromWebNodes, fromShadeTree_auto, fromShadeTree, fromShaded
              -- ** Lookup
            , nearestNeighbour, indexWeb, toGraph, webBoundary
              -- ** Decomposition
            , sliceWeb_lin -- , sampleWebAlongLine_lin
            , sampleWeb_2Dcartesian_lin, sampleEntireWeb_2Dcartesian_lin
              -- ** Local environments
            , localFocusWeb
              -- * Uncertain functions
            , differentiateUncertainWebFunction, differentiate²UncertainWebFunction
            , localModels_CGrid
              -- * Differential equations
              -- ** Fixed resolution
            , iterateFilterDEqn_static, iterateFilterDEqn_static_selective
              -- ** Automatic resolution
            , filterDEqnSolutions_adaptive, iterateFilterDEqn_adaptive
              -- ** Configuration
            , InconsistencyStrategy(..)
            , InformationMergeStrategy(..)
            , naïve, inconsistencyAware, indicateInconsistencies, postponeInconsistencies
            , PropagationInconsistency(..)
              -- * Misc
            , ConvexSet(..), ellipsoid, ellipsoidSet, coerceWebDomain
            , rescanPDELocally, webOnions
            ) where


import Data.List hiding (filter, all, foldr1)
import Data.Maybe
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Vector as Arr
import qualified Data.Vector.Mutable as MArr
import qualified Data.Vector.Unboxed as UArr
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE
import Data.List.FastNub (fastNub,fastNubBy)
import Data.Ord (comparing)
import Data.Semigroup
import Control.DeepSeq

import Data.VectorSpace
import Math.LinearMap.Category

import Data.Tagged
import Data.Function (on)
import Data.Fixed (mod')

import Data.Manifold.Types
import Data.Manifold.Types.Primitive
import Data.Manifold.PseudoAffine
import Data.Manifold.Shade
import Data.Manifold.TreeCover
import Data.SetLike.Intersection
import Data.Manifold.Riemannian
import Data.Manifold.Atlas
import Data.Manifold.Function.Quadratic
import Data.Function.Affine
import Data.Embedding
    
import qualified Prelude as Hask hiding(foldl, sum, sequence)
import qualified Control.Applicative as Hask
import qualified Control.Monad       as Hask hiding(forM_, sequence)
import Control.Monad.ST (runST)
import Data.STRef (newSTRef, modifySTRef, readSTRef)
import Control.Monad.Trans.State
import Control.Monad.Trans.List
import Control.Monad.Trans.Except
import Control.Monad.Trans.Writer hiding (censor)
import Data.Functor.Identity (Identity(..))
import qualified Data.Foldable       as Hask
import Data.Foldable (all, toList)
import qualified Data.Traversable as Hask
import Data.Traversable (forM)
import Data.Graph

import Control.Category.Constrained.Prelude hiding
     ((^), all, elem, sum, forM, Foldable(..), foldr1, Traversable, traverse)
import Control.Arrow.Constrained
import Control.Monad.Constrained hiding (forM)
import Data.Foldable.Constrained
import Data.Traversable.Constrained (Traversable, traverse)

import Control.Comonad (Comonad(..))
import Control.Comonad.Cofree
import Control.Lens ((&), (%~), (^.), (.~), (+~))
import Control.Lens.TH

import GHC.Generics (Generic)

import Development.Placeholders

type WebNodeId = Int
type WebNodeIdOffset = Int

data Neighbourhood x y = Neighbourhood {
     _dataAtNode :: y
   , _neighbours :: UArr.Vector WebNodeIdOffset
   , _localScalarProduct :: Metric x
   , _webBoundaryAtNode :: Maybe (Needle' x)
   }
  deriving (Generic, Hask.Functor, Hask.Foldable, Hask.Traversable)
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
    , _nodeIsOnBoundary :: Bool
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
  deriving (Generic, Hask.Functor, Hask.Foldable, Hask.Traversable)

instance (NFData x, NFData (Metric x), NFData (Needle' x), NFData y) => NFData (PointsWeb x y)

instance Foldable (PointsWeb x) (->) (->) where
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

pumpHalfspace :: ∀ v . (SimpleSpace v, Scalar v ~ ℝ, Scalar (DualVector v) ~ ℝ)
                => Norm v -> v -> (DualVector v, [v]) -> Maybe (DualVector v)
pumpHalfspace rieM v (prevPlane, ws)
   = if δϑ <= pi then Just $ let ϑbest = ϑmin + δϑ/2
                             in prevPlane^*cos ϑbest ^+^ thisPlane^*sin ϑbest
                 else Nothing
   where ϑs = fmap (\u -> let x = prevPlane<.>^u
                              y = thisPlane<.>^u in atan2 x y) $ v:ws
         [ϑmin, ϑmax] = [minimum, maximum] <*> [ϑs]
         δϑ = ϑmax - ϑmin
         dv = rieM<$|v
         thisPlane = dv ^/ (dv<.>^v)

fromWebNodes :: ∀ x y . (WithField ℝ Manifold x, SimpleSpace (Needle x))
                    => (MetricChoice x) -> [(x,y)] -> PointsWeb x y
fromWebNodes = case boundarylessWitness :: BoundarylessWitness x of
   BoundarylessWitness ->
       \mf -> fromShaded mf . fromLeafPoints_

fromTopWebNodes :: ∀ x y . (WithField ℝ Manifold x, SimpleSpace (Needle x))
                    => (MetricChoice x) -> [((x,[Int+Needle x]),y)] -> PointsWeb x y
fromTopWebNodes = case boundarylessWitness :: BoundarylessWitness x of
   BoundarylessWitness ->
       \mf -> fromTopShaded mf . fromLeafPoints_ . map regroup'

fromShadeTree_auto :: ∀ x . (WithField ℝ Manifold x, SimpleSpace (Needle x)) => ShadeTree x -> PointsWeb x ()
fromShadeTree_auto = fromShaded (dualNorm' . _shadeExpanse) . constShaded ()

fromShadeTree :: ∀ x . (WithField ℝ Manifold x, SimpleSpace (Needle x))
     => (Shade x -> Metric x) -> ShadeTree x -> PointsWeb x ()
fromShadeTree mf = fromShaded mf . constShaded ()

fromShaded :: ∀ x y . (WithField ℝ Manifold x, SimpleSpace (Needle x))
     => (MetricChoice x) -- ^ Local scalar-product generator. You can always
                              --   use @'recipMetric' . '_shadeExpanse'@ (but this
                              --   may give distortions compared to an actual
                              --   Riemannian metric).
     -> (x`Shaded`y)          -- ^ Source tree.
     -> PointsWeb x y
fromShaded metricf = smoothenWebTopology metricf
                   . fromTopShaded metricf . fmapShaded (first (map Left) . swap)
                       . seekPotentialNeighbours

toShaded :: WithField ℝ PseudoAffine x => PointsWeb x y -> (x`Shaded`y)
toShaded (PointsWeb shd) = fmap _dataAtNode shd

fromTopShaded :: ∀ x y . (WithField ℝ Manifold x, SimpleSpace (Needle x))
     => (MetricChoice x)
     -> (x`Shaded`([Int+Needle x], y))
                      -- ^ Source tree, with topology information
                      --   (IDs of neighbour-candidates, or needles pointing to them)
     -> PointsWeb x y
fromTopShaded metricf shd = $notImplemented

cullNeighbours :: ∀ x y . (WithField ℝ PseudoAffine x, SimpleSpace (Needle x))
      => Metric x -> (Int, (x,[(Int,Needle x)])) -> Neighbourhood x y
cullNeighbours = $notImplemented
              

-- | Re-calculate the links in a web, so as to give each point a satisfyingly
--   “complete-spanning” environment.
smoothenWebTopology :: (WithField ℝ Manifold x, SimpleSpace (Needle x))
             => MetricChoice x -> PointsWeb x y -> PointsWeb x y
smoothenWebTopology mc = $notImplemented

makeIndexLinksSymmetric
       :: Arr.Vector (y, Neighbourhood x y)
       -> (Arr.Vector (y, Neighbourhood x y), Set.Set (WebNodeId,WebNodeId))
makeIndexLinksSymmetric orig = $notImplemented

indexWeb :: PointsWeb x y -> WebNodeId -> Maybe (x,y)
indexWeb (PointsWeb rsc) i = case indexShadeTree rsc i of
       Right (_, (x, Neighbourhood y _ _ _)) -> Just (x, y)
       _ -> Nothing

unsafeIndexWebData :: PointsWeb x y -> WebNodeId -> y
unsafeIndexWebData web i = case indexWeb web i of
              Just (x,y) -> y


webBoundary :: WithField ℝ Manifold x => PointsWeb x y -> [(x,y)]
webBoundary = webLocalInfo >>> Hask.toList >>> Hask.concatMap`id`
        \info -> [ (info^.thisNodeCoord, info^.thisNodeData)
                 | info^.nodeIsOnBoundary ]


coerceWebDomain :: ∀ a b y
     . (Manifold a, Manifold b, LocallyCoercible a b, SimpleSpace (Needle b))
                                 => PointsWeb a y -> PointsWeb b y
coerceWebDomain = $notImplemented


data InterpolationIv y = InterpolationIv {
          _interpolationSegRange :: (ℝ,ℝ)
        , _interpolationFunction :: ℝ -> y
        }

type InterpolationSeq y = [InterpolationIv y]

mkInterpolationSeq_lin :: (x~ℝ, Geodesic y)
           => [(x,y)] -> InterpolationSeq y
mkInterpolationSeq_lin [(xψ,yψ), (xω,yω)]
       = return $ InterpolationIv
           (xψ,xω)
           (\x -> let drel = fromIntv0to1 $ (x-xψ)/(xω-xψ)
                  in yio drel )
 where Just yio = geodesicBetween yψ yω
mkInterpolationSeq_lin (p₀:p₁:ps)
    = mkInterpolationSeq_lin [p₀,p₁] <> mkInterpolationSeq_lin (p₁:ps)
mkInterpolationSeq_lin _ = []


-- | Fetch a point between any two neighbouring web nodes on opposite
--   sides of the plane, and linearly interpolate the values onto the
--   cut plane.
sliceWeb_lin :: ∀ x y . ( WithField ℝ Manifold x, SimpleSpace (Needle x)
                        , Geodesic x, Geodesic y )
               => PointsWeb x y -> Cutplane x -> [(x,y)]
sliceWeb_lin web = sliceEdgs
 where edgs = $notImplemented :: [((x,y),(x,y))]
       sliceEdgs cp = [ (xi d, yi d)  -- Brute-force search through all edges
                      | ((x₀,y₀), (x₁,y₁)) <- edgs
                      , Just d <- [cutPosBetween cp (x₀,x₁)]
                      , Just xi <- [geodesicBetween x₀ x₁]
                      , Just yi <- [geodesicBetween y₀ y₁]
                      ]



data GridPlanes x = GridPlanes {
        _gridPlaneNormal :: Needle' x
      , _gridPlaneSpacing :: Needle x
      , _gridPlanesCount :: Int
      }
deriving instance (Show x, Show (Needle x), Show (Needle' x)) => Show (GridPlanes x)
data GridSetup x = GridSetup {
        _gridStartCorner :: x
      , _gridSplitDirs :: [GridPlanes x]
      }
deriving instance (Show x, Show (Needle x), Show (Needle' x)) => Show (GridSetup x)

cartesianGrid2D :: (x~ℝ, y~ℝ) => ((x,x), Int) -> ((y,y), Int) -> GridSetup (x,y)
cartesianGrid2D ((x₀,x₁), nx) ((y₀,y₁), ny)
    = GridSetup (x₀+dx/2, y₀+dy/2)
                [ GridPlanes (0,1) (0, dy) ny, GridPlanes (1,0) (dx, 0) nx ]
 where dx = (x₁-x₀)/fromIntegral nx
       dy = (y₁-y₀)/fromIntegral ny

splitToGridLines :: ( WithField ℝ Manifold x, SimpleSpace (Needle x)
                    , Geodesic x, Geodesic y )
          => PointsWeb x y -> GridSetup x -> [((x, GridPlanes x), [(x,y)])]
splitToGridLines web (GridSetup x₀ [GridPlanes dirΩ spcΩ nΩ, linePln])
    = [ ((x₀', linePln), sliceWeb_lin web $ Cutplane x₀' (Stiefel1 dirΩ))
      | k <- [0 .. nΩ-1]
      , let x₀' = x₀i.+~^(fromIntegral k *^ spcΩ) ]
 where Just x₀i = toInterior x₀

sampleWebAlongGrid_lin :: ∀ x y . ( WithField ℝ Manifold x, SimpleSpace (Needle x)
                                  , Geodesic x, Geodesic y )
               => PointsWeb x y -> GridSetup x -> [(x,Maybe y)]
sampleWebAlongGrid_lin web grid = finalLine boundarylessWitness
                                      =<< splitToGridLines web grid
 where finalLine :: BoundarylessWitness x -> ((x, GridPlanes x), [(x,y)]) -> [(x,Maybe y)]
       finalLine BoundarylessWitness ((x₀, GridPlanes _ dir nSpl), verts)
          | length verts < 2  = take nSpl $ (,empty)<$>iterate (.+~^dir) x₀
       finalLine BoundarylessWitness ((x₀, GridPlanes dx dir nSpl), verts)
                     = take nSpl $ go (x₀,0) intpseq 
        where intpseq = mkInterpolationSeq_lin $ sortBy (comparing fst)
                         [ (dx <.>^ (x.-~!x₀), y) | (x,y) <- verts ]
              go (x,_) [] = (,empty)<$>iterate (.+~^dir) x
              go xt (InterpolationIv (tb,te) f:fs)
                        = case span ((<te) . snd) $ iterate ((.+~^dir)***(+δt)) xt of
                             (thisRange, xtn:_)
                                 -> [ (x, if t<tb then empty else return $ f t)
                                    | (x,t) <- thisRange ]
                                     ++ go xtn fs
              δt = dx<.>^dir
       
sampleWeb_2Dcartesian_lin :: (x~ℝ, y~ℝ, Geodesic z)
             => PointsWeb (x,y) z -> ((x,x),Int) -> ((y,y),Int) -> [(y,[(x,Maybe z)])]
sampleWeb_2Dcartesian_lin web (xspec@(_,nx)) yspec
       = go . sampleWebAlongGrid_lin web $ cartesianGrid2D xspec yspec
 where go [] = []
       go l@(((_,y),_):_) = let (ln,l') = splitAt nx l
                             in (y, map (\((x,_),z) -> (x,z)) ln) : go l'
       
sampleEntireWeb_2Dcartesian_lin :: (x~ℝ, y~ℝ, Geodesic z)
             => PointsWeb (x,y) z -> Int -> Int -> [(y,[(x,Maybe z)])]
sampleEntireWeb_2Dcartesian_lin web nx ny
       = sampleWeb_2Dcartesian_lin web ((x₀,x₁),nx) ((y₀,y₁),ny)
 where x₀ = minimum (fst<$>pts)
       x₁ = maximum (fst<$>pts)
       y₀ = minimum (snd<$>pts)
       y₁ = maximum (snd<$>pts)
       pts = fst . fst <$> toList (localFocusWeb web)


traverseInnermostChunks :: ∀ f x y z . ( Hask.Applicative f
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

traverseNodesInEnvi :: ∀ f x y z . ( Hask.Applicative f
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

ixedFoci :: [a] -> [((Int, a), [a])]
ixedFoci = go 0
 where go _ [] = []
       go i (x:xs) = ((i,x), xs) : map (second (x:)) (go (i+1) xs)
 

jumpNodeOffset :: WebNodeIdOffset -> NodeInWeb x y -> NodeInWeb x y
jumpNodeOffset 0 node = node
jumpNodeOffset δi (NodeInWeb x environment)
   = case zoomoutWebChunk δi $ WebChunk (PointsWeb $ PlainLeaves [x]) environment of
       (WebChunk bigChunk envi', δi') -> case pickNodeInWeb bigChunk δi' of
              NodeInWeb x' envi'' -> NodeInWeb x' $ envi'' ++ envi'

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
                         ((OverlappingBranches nw ew (br₀@(DBranch _ (Hourglass u d))
                                                         :|br₁:brs), i) : envi))
  = case webAroundChunk (WebChunk chunk [(OverlappingBranches nw ew (br₁:|brs), i')])
      of PointsWeb (OverlappingBranches nw' ew' (br₁':|brs'))
           -> webAroundChunk $ WebChunk
                    (PointsWeb $ OverlappingBranches nw' ew' (br₀:|br₁':brs'))
                    envi
 where i' = i + nLeaves u + nLeaves d


zoomoutWebChunk :: WebNodeIdOffset -> WebChunk x y -> (WebChunk x y, WebNodeId)
zoomoutWebChunk δi (WebChunk chunk ((outlayer, olp) : outlayers))
  | δi < 0 || δi >= nLeaves outlayer
      = zoomoutWebChunk δi' (WebChunk (webAroundChunk $ WebChunk chunk [(outlayer,olp)])
                                      outlayers)
 where δi' | δi < 0     = δi + olp
           | otherwise  = δi + olp - nLeaves outlayer
zoomoutWebChunk δi ch = (ch, δi)

pickNodeInWeb :: PointsWeb x y -> WebNodeId -> NodeInWeb x y
pickNodeInWeb (PointsWeb (PlainLeaves lvs)) i
  | i>0, (preds, node:succs)<-splitAt i lvs
                   = NodeInWeb node [(PlainLeaves $ preds++succs, i)]
pickNodeInWeb (PointsWeb (OverlappingBranches nw ew (DBranch dir (Hourglass u d):|[]))) i
  | i < nu     = pickNodeInWeb (PointsWeb u) i
                      & layersAroundNode %~ ((OverlappingBranches nw ew
                                               (DBranch dir (Hourglass gap d):|[]),0):)
  | otherwise  = pickNodeInWeb (PointsWeb d) (i-nu)
                      & layersAroundNode %~ ((OverlappingBranches nw ew
                                               (DBranch dir (Hourglass u gap):|[]),0):)
 where gap = PlainLeaves []
       nu = nLeaves u

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
                , _nodeIsOnBoundary = isJust nBoundary
                }
        where i = foldr ((+) . snd) 0 envis


hardbakeChunk :: WebChunk x y -> PointsWeb x y
hardbakeChunk = _thisChunk

aroundChunk :: (PointsWeb x y -> PointsWeb x z) -> WebChunk x y -> WebChunk x z
aroundChunk f (WebChunk origWeb outlayers) = case f origWeb of
         newWeb -> $notImplemented

entireWeb :: PointsWeb x y -> WebChunk x y
entireWeb web = WebChunk web []

localFocusWeb :: WithField ℝ Manifold x
                   => PointsWeb x y -> PointsWeb x ((x,y), [(Needle x, y)])
localFocusWeb (PointsWeb rsc) = PointsWeb $notImplemented



treewiseTraverseLocalWeb :: ∀ f x y . (WithField ℝ Manifold x, Hask.Applicative f)
     => (WebLocally x y -> f y)
       -> (∀ t i w . (Hask.Traversable t, Ord i) => (w -> f w) -> t (i, w) -> f (t w) )
       -> PointsWeb x y -> f (PointsWeb x y)
treewiseTraverseLocalWeb fl ct = fmap hardbakeChunk . twt . entireWeb
 where twt = treewiseTraverseLocalWeb' fl $ ct twt

treewiseTraverseLocalWeb' :: ∀ f x y . (WithField ℝ Manifold x, Hask.Applicative f)
     => (WebLocally x y -> f y)
       -> (NonEmpty (Int, WebChunk x y) -> f (NonEmpty (WebChunk x y)))
       -> WebChunk x y -> f (WebChunk x y)
treewiseTraverseLocalWeb' fl ct domain
                  = $notImplemented{-
 where rezoomed (PlainLeaves _) _ = localTraverseWebChunk fl domain
       rezoomed tree pos
         | pos == i₀, nLeaves tree == lDomain
             = fmap reassemble $ ct (NE.zipWith
                       (\jb (i₀b,t')
                         -> (jb, domain & overrideStart .~ i₀+i₀b
                                        & overriddenData
                                            .~ Arr.slice i₀b (nLeaves t') domainData ))
                       (0:|[1..]) branches)
         | otherwise                     = go branches
        where branches = trunkBranches tree
              go (_:|((i₀nb,nb):brs))
                | pos+i₀nb <= i₀  = go $ (i₀nb,nb):|brs
              go ((i₀b,t):|_) = rezoomed t (pos+i₀b)
              reassemble :: NonEmpty (WebChunk x y) -> WebChunk x y
              reassemble brs = domain & overriddenData
                                  .~ Hask.foldMap _overriddenData brs
       lDomain = Arr.length domainData
   -}



localOnion :: ∀ x y . WithField ℝ Manifold x
            => WebLocally x y -> [WebNodeId] -> [[(Needle x, WebLocally x y)]]
localOnion origin directCandidates = map sortBCDistance . go Map.empty . Map.fromList
                      $ (origin^.thisNodeId, (1, origin)) : seeds
 where seeds :: [(WebNodeId, (Int, WebLocally x y))]
       seeds = [ (nid, (1, ninfo))
               | nid <- directCandidates
               , (_,(_,ninfo)) <- origin^.nodeNeighbours
               , ninfo^.thisNodeId == nid ]
       go previous next
        | Map.null next = []
        | otherwise  = ( computeOffset . snd
                                    <$> sortBy (comparing $ negate . fst)
                                                 (Hask.toList next) )
                     : go (Map.union previous next)
                          (Map.fromListWith (\(n,ninfo) (n',_) -> (n+n'::Int, ninfo))
                             [ (nnid,(1,nneigh))
                             | (nid,(_,ninfo))<-Map.toList next
                             , (nnid,(_,nneigh))<-ninfo^.nodeNeighbours
                             , Map.notMember nnid previous && Map.notMember nnid next ])
       computeOffset p = case p^.thisNodeCoord .-~. origin^.thisNodeCoord of
                Just v -> (v,p)
       sortBCDistance = map snd . sortBy (comparing fst) . map (bcDist&&&id)
        where bcDist (v,_)
                = normSq (origin^.nodeLocalScalarProduct) $ v^-^seedBarycenterOffs
       seedBarycenterOffs = sumV ngbOffs ^/ fromIntegral (length directCandidates + 1)
        where ngbOffs = [ v | (_, (_, n)) <- seeds
                            , let Just v = n^.thisNodeCoord .-~. origin^.thisNodeCoord ]

webOnions :: ∀ x y . WithField ℝ Manifold x
            => PointsWeb x y -> PointsWeb x [[(x,y)]]
webOnions = localFmapWeb (map (map $ _thisNodeCoord&&&_thisNodeData <<< snd)
                                . (`localOnion`[]))

nearestNeighbour :: (WithField ℝ Manifold x, SimpleSpace (Needle x))
                      => PointsWeb x y -> x -> Maybe (x,y)
nearestNeighbour (PointsWeb rsc) x = fmap $notImplemented (positionIndex empty rsc x)



instance Hask.Functor (WebLocally x) where
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

-- ^ 'fmap' from the co-Kleisli category of 'WebLocally'.
localTraverseWeb :: (WithField ℝ Manifold x, Hask.Applicative m)
                => (WebLocally x y -> m z) -> PointsWeb x y -> m (PointsWeb x z)
localTraverseWeb f = webLocalInfo >>> Hask.traverse f

-- ^ 'fmap' from the co-Kleisli category of 'WebLocally', restricted to some
--   contiguous part of a web.
localTraverseWebChunk :: (WithField ℝ Manifold x, Hask.Applicative m)
                => (WebLocally x y -> m y) -> WebChunk x y -> m (WebChunk x y)
localTraverseWebChunk f (WebChunk this outlayers)
      = fmap (\c -> WebChunk c outlayers) $ localTraverseWeb f this

differentiateUncertainWebLocally :: ∀ x y
   . ( WithField ℝ Manifold x, SimpleSpace (Needle x)
     , WithField ℝ Refinable y, SimpleSpace (Needle y) )
            => WebLocally x (Shade' y)
             -> Shade' (LocalLinear x y)
differentiateUncertainWebLocally info
          = case estimateLocalJacobian
                          (info^.nodeLocalScalarProduct)
                          [ ( Local δx :: Local x, ngb^.thisNodeData )
                          | (δx,ngb) <- (zeroV, info)
                                      : (snd<$>info^.nodeNeighbours)
                          ] of
               Just j -> j
               _      -> Shade' zeroV mempty


-- | Dimension of the space of quadratic functions on @v@.
p²Dimension :: ∀ v p . FiniteDimensional v => p v -> Int
p²Dimension _ = 1 + d + (d*(d+1))`div`2
 where d = subbasisDimension (entireBasis :: SubBasis v)

differentiateUncertainWebFunction :: ∀ x y
   . ( WithField ℝ Manifold x, SimpleSpace (Needle x)
     , WithField ℝ Manifold y, SimpleSpace (Needle y), Refinable y )
            => PointsWeb x (Shade' y)
             -> PointsWeb x (Shade' (LocalLinear x y))
differentiateUncertainWebFunction = localFmapWeb differentiateUncertainWebLocally

differentiate²UncertainWebLocally :: ∀ x y
   . ( WithField ℝ Manifold x, FlatSpace (Needle x)
     , WithField ℝ Refinable y, Geodesic y, FlatSpace (Needle y) )
            => WebLocally x (Shade' y)
             -> Shade' (Needle x ⊗〃+> Needle y)
differentiate²UncertainWebLocally = d²uwl
                ( pseudoAffineWitness :: PseudoAffineWitness x
                , pseudoAffineWitness :: PseudoAffineWitness y
                , dualSpaceWitness :: DualSpaceWitness (Needle x)
                , dualSpaceWitness :: DualSpaceWitness (Needle y) )
 where d²uwl ( PseudoAffineWitness (SemimanifoldWitness _)
             , PseudoAffineWitness (SemimanifoldWitness _)
             , DualSpaceWitness, DualSpaceWitness ) info
          = case estimateLocalHessian $
                          (\(δx,ngb) -> (Local δx :: Local x, ngb^.thisNodeData) )
                          <$> (zeroV,info) :| envi
                          of
               QuadraticModel _ _ h -> linIsoTransformShade (2*^id) $ dualShade h
        where xVol :: SymmetricTensor ℝ (Needle x)
              xVol = squareVs $ fst.snd<$>info^.nodeNeighbours
              _:directEnvi:remoteEnvi = localOnion info []
              envi = directEnvi ++ take (nMinNeighbours - length directEnvi)
                                        (concat remoteEnvi)
       nMinNeighbours = p²Dimension ([] :: [Needle x])


selectQuadraticFittableEnvironment :: ∀ x y
           . (WithField ℝ Manifold x, SimpleSpace (Needle x))
                => WebLocally x y -> [WebNodeId] -> [(Needle x, WebLocally x y)]
selectQuadraticFittableEnvironment me
       = take (p²Dimension ([] :: [Needle x]) + 1) . concat . localOnion me

-- | Calculate a quadratic fit with uncertainty margin centered around the connection
--   between any two adjacent nodes. In case of a regular grid (which we by no means
--   require here!) this corresponds to the vector quantities of an Arakawa type C/D
--   grid (cf. A. Arakawa, V.R. Lamb (1977):
--   Computational design of the basic dynamical processes of the UCLA general circulation model)
localModels_CGrid :: ∀ x y . ( WithField ℝ Manifold x, FlatSpace (Needle x)
                             , Refinable y, Geodesic y, FlatSpace (Needle y) )
          => PointsWeb x (Shade' y) -> [(x, QuadraticModel x y)]
localModels_CGrid = Hask.concatMap theCGrid . Hask.toList . webLocalInfo
 where theCGrid :: WebLocally x (Shade' y) -> [(x, QuadraticModel x y)]
       theCGrid node = [ ( pn .-~^ δx^/2
                         , propagationCenteredQuadraticModel
                             ( LocalDataPropPlan
                                    pn
                                    (negateV δx)
                                    (ngbNode^.thisNodeData)
                                    (node^.thisNodeData)
                                    (fmap (second _thisNodeData)
                                      $ selectQuadraticFittableEnvironment
                                                    ngbNode [node^.thisNodeId] )
                                          ) )
                       | (nid, (δx, ngbNode)) <- node^.nodeNeighbours
                       , nid > node^.thisNodeId
                       , Just pn <- [toInterior $ ngbNode^.thisNodeCoord]
                       ]


acoSnd :: ∀ s v y . ( Object (Affine s) y, Object (Affine s) v
                    , LinearSpace v, Scalar v ~ s ) => Affine s y (v,y)
acoSnd = case ( linearManifoldWitness :: LinearManifoldWitness v
              , dualSpaceWitness :: DualSpaceWitness (Needle v)
              , dualSpaceWitness :: DualSpaceWitness (Needle y) ) of
   (LinearManifoldWitness BoundarylessWitness, DualSpaceWitness, DualSpaceWitness)
       -> const zeroV &&& id


differentiate²UncertainWebFunction :: ∀ x y
   . ( WithField ℝ Manifold x, FlatSpace (Needle x)
     , WithField ℝ Refinable y, Geodesic y, FlatSpace (Needle y) )
         => PointsWeb x (Shade' y)
          -> PointsWeb x (Shade' (Needle x ⊗〃+> Needle y)) 
differentiate²UncertainWebFunction = localFmapWeb differentiate²UncertainWebLocally

rescanPDELocally :: ∀ x y .
     ( WithField ℝ Manifold x, FlatSpace (Needle x)
     , WithField ℝ Refinable y, Geodesic y, FlatSpace (Needle y) )
         => DifferentialEqn x y -> WebLocally x (Shade' y) -> Maybe (Shade' y)
rescanPDELocally = case ( dualSpaceWitness :: DualNeedleWitness x
                        , dualSpaceWitness :: DualNeedleWitness y
                        , boundarylessWitness :: BoundarylessWitness x
                        , pseudoAffineWitness :: PseudoAffineWitness y ) of
   ( DualSpaceWitness,DualSpaceWitness,BoundarylessWitness
    , PseudoAffineWitness (SemimanifoldWitness BoundarylessWitness) )
     -> \f info
          -> if info^.nodeIsOnBoundary
              then return $ info^.thisNodeData
              else let xc = info^.thisNodeCoord
                       yc = info^.thisNodeData.shadeCtr
                   in case f $ coverAllAround (xc, yc)
                                     [ (δx, (ngb^.thisNodeData.shadeCtr.-~!yc) ^+^ v)
                                     | (_,(δx,ngb))<-info^.nodeNeighbours
                                     , v <- normSpanningSystem'
                                              (ngb^.thisNodeData.shadeNarrowness)] of
                        LocalDifferentialEqn rescan -> fst
                             ( rescan (info^.thisNodeData)
                                      (differentiateUncertainWebLocally info)
                                      (differentiate²UncertainWebLocally info) )

toGraph :: (WithField ℝ Manifold x, SimpleSpace (Needle x))
              => PointsWeb x y -> (Graph, Vertex -> (x, y))
toGraph wb = second (>>> \(i,_,_) -> case indexWeb wb i of {Just xy -> xy})
                (graphFromEdges' edgs)
 where edgs :: [(Int, Int, [Int])]
       edgs = Arr.toList
            . Arr.imap (\i (Neighbourhood _ ngbs _ _) -> (i, i, UArr.toList ngbs))
            . Arr.fromList . Hask.toList $ webNodeRsc wb




data ConvexSet x
    = EmptyConvex
    | ConvexSet {
      convexSetHull :: Shade' x
      -- ^ If @p@ is in all intersectors, it must also be in the hull.
    , convexSetIntersectors :: [Shade' x]
    }
deriving instance LtdErrorShow x => Show (ConvexSet x)

ellipsoid :: Shade' x -> ConvexSet x
ellipsoid s = ConvexSet s [s]

ellipsoidSet :: Embedding (->) (Maybe (Shade' x)) (ConvexSet x)
ellipsoidSet = Embedding (\case {Just s -> ConvexSet s [s]; Nothing -> EmptyConvex})
                         (\case {ConvexSet h _ -> Just h; EmptyConvex -> Nothing})

intersectors :: ConvexSet x -> Maybe (NonEmpty (Shade' x))
intersectors (ConvexSet h []) = pure (h:|[])
intersectors (ConvexSet _ (i:sts)) = pure (i:|sts)
intersectors _ = empty

-- | Under intersection.
instance Refinable x => Semigroup (ConvexSet x) where
  a<>b = sconcat (a:|[b])
  sconcat csets
    | Just allIntersectors <- sconcat <$> Hask.traverse intersectors csets
    , IntersectT ists <- rmTautologyIntersect perfectRefine $ IntersectT allIntersectors
    , Just hull' <- intersectShade's ists
                 = ConvexSet hull' (NE.toList ists)
    | otherwise  = EmptyConvex
   where perfectRefine sh₁ sh₂
           | sh₁`subShade'`sh₂   = pure sh₁
           | sh₂`subShade'`sh₁   = pure sh₂
           | otherwise           = empty



itWhileJust :: InconsistencyStrategy m x y -> (a -> m a) -> a -> [a]
itWhileJust AbortOnInconsistency f x
 | Just y <- f x  = x : itWhileJust AbortOnInconsistency f y
itWhileJust IgnoreInconsistencies f x
 | Identity y <- f x  = x : itWhileJust IgnoreInconsistencies f y
itWhileJust (HighlightInconsistencies yh) f x
 | Identity y <- f x  = x : itWhileJust (HighlightInconsistencies yh) f y
itWhileJust _ _ x = [x]

dupHead :: NonEmpty a -> NonEmpty a
dupHead (x:|xs) = x:|x:xs


newtype InformationMergeStrategy n m y' y = InformationMergeStrategy
    { mergeInformation :: y -> n y' -> m y }

naïve :: (NonEmpty y -> y) -> InformationMergeStrategy [] Identity (x,y) y
naïve merge = InformationMergeStrategy (\o n -> Identity . merge $ o :| fmap snd n)

inconsistencyAware :: (NonEmpty y -> m y) -> InformationMergeStrategy [] m (x,y) y
inconsistencyAware merge = InformationMergeStrategy (\o n -> merge $ o :| fmap snd n)

indicateInconsistencies :: (NonEmpty υ -> Maybe υ)
         -> InformationMergeStrategy [] (Except (PropagationInconsistency x υ)) (x,υ) υ
indicateInconsistencies merge = InformationMergeStrategy
           (\o n -> case merge $ o :| fmap snd n of
               Just r  -> pure r
               Nothing -> throwE $ PropagationInconsistency n o )

postponeInconsistencies :: Hask.Monad m => (NonEmpty υ -> Maybe υ)
   -> InformationMergeStrategy [] (WriterT [PropagationInconsistency x υ] m)
                                  (x,υ) υ
postponeInconsistencies merge = InformationMergeStrategy
           (\o n -> case merge $ o :| fmap snd n of
               Just r  -> pure r
               Nothing -> writer (o,[PropagationInconsistency n o]) )

maybeAlt :: Hask.Alternative f => Maybe a -> f a
maybeAlt (Just x) = pure x
maybeAlt Nothing = Hask.empty

data InconsistencyStrategy m x y where
    AbortOnInconsistency :: InconsistencyStrategy Maybe x y
    IgnoreInconsistencies :: InconsistencyStrategy Identity x y
    HighlightInconsistencies :: y -> InconsistencyStrategy Identity x y
deriving instance Hask.Functor (InconsistencyStrategy m x)


iterateFilterDEqn_static :: ( WithField ℝ Manifold x, FlatSpace (Needle x)
                            , Refinable y, Geodesic y, FlatSpace (Needle y)
                            , Hask.MonadPlus m )
       => InformationMergeStrategy [] m (x,Shade' y) iy
           -> Embedding (->) (Shade' y) iy
           -> DifferentialEqn x y
                 -> PointsWeb x (Shade' y) -> Cofree m (PointsWeb x (Shade' y))
iterateFilterDEqn_static strategy shading f
                           = fmap (fmap (shading >-$))
                           . coiter (filterDEqnSolutions_static strategy shading f)
                           . fmap (shading $->)


iterateFilterDEqn_static_selective :: ( WithField ℝ Manifold x, FlatSpace (Needle x)
                                      , Refinable y, Geodesic y, FlatSpace (Needle y)
                                      , Hask.MonadPlus m, badness ~ ℝ )
       => InformationMergeStrategy [] m (x,Shade' y) iy
           -> Embedding (->) (Shade' y) iy
           -> (x -> iy -> badness)
           -> DifferentialEqn x y
                 -> PointsWeb x (Shade' y) -> Cofree m (PointsWeb x (Shade' y))
iterateFilterDEqn_static_selective strategy shading badness f
      = fmap (fmap (shading >-$))
      . coiter (filterDEqnSolutions_static_selective strategy shading badness f)
      . fmap (shading $->)


filterDEqnSolutions_static :: ∀ x y iy m .
                              ( WithField ℝ Manifold x, FlatSpace (Needle x)
                              , Refinable y, Geodesic y, FlatSpace (Needle y)
                              , Hask.MonadPlus m )
       => InformationMergeStrategy [] m  (x,Shade' y) iy -> Embedding (->) (Shade' y) iy
          -> DifferentialEqn x y -> PointsWeb x iy -> m (PointsWeb x iy)
filterDEqnSolutions_static = case geodesicWitness :: GeodesicWitness y of
   GeodesicWitness _ -> \strategy shading f
       -> webLocalInfo
           >>> fmap (id &&& rescanPDELocally f . fmap (shading>-$))
           >>> localFocusWeb >>> Hask.traverse ( \((_,(me,updShy)), ngbs)
          -> let oldValue = me^.thisNodeData :: iy
             in if me ^. nodeIsOnBoundary
                 then return oldValue
                 else case updShy of
              Just shy -> case ngbs of
                  []  -> pure oldValue
                  _:_ | BoundarylessWitness <- (boundarylessWitness::BoundarylessWitness x)
                    -> sequenceA [ maybeAlt sj
                                >>= \ngbShyð -> fmap ((me^.thisNodeCoord .+~^ δx,)
                                                   . (shading>-$))
                                  . mergeInformation strategy oldValue . Hask.toList
                                  $ (ngbInfo^.thisNodeCoord,)<$>
                                     propagateDEqnSolution_loc
                                       f (LocalDataPropPlan
                                             (ngbInfo^.thisNodeCoord)
                                             (negateV δx)
                                             ngbShyð
                                             shy
                                             (fmap (second ((shading>-$) . _thisNodeData))
                                               $ selectQuadraticFittableEnvironment
                                                          ngbInfo [me^.thisNodeId])
                                          )
                                  | (δx, (ngbInfo,sj)) <- ngbs
                                  ]
                            >>= mergeInformation strategy (shading$->shy)
              _ -> mergeInformation strategy oldValue empty
        )



data Average a = Average { weight :: Int
                         , averageAcc :: a
                         } deriving (Hask.Functor)
instance Num a => Monoid (Average a) where
  mempty = Average 0 0
  mappend (Average w₀ a₀) (Average w₁ a₁) = Average (w₀+w₁) (a₀+a₁)
instance Hask.Applicative Average where
  pure = Average 1
  Average w₀ a₀ <*> Average w₁ a₁ = Average (w₀*w₁) (a₀ a₁)

average :: Fractional a => Average a -> a
average (Average w a) = a / fromIntegral w

averaging :: VectorSpace a => [a] -> Average a
averaging l = Average (length l) (sumV l)

filterDEqnSolutions_static_selective :: ∀ x y iy m badness .
                              ( WithField ℝ Manifold x, FlatSpace (Needle x)
                              , Refinable y, Geodesic y, FlatSpace (Needle y)
                              , Hask.MonadPlus m, badness ~ ℝ )
       => InformationMergeStrategy [] m  (x,Shade' y) iy -> Embedding (->) (Shade' y) iy
          -> (x -> iy -> badness)
          -> DifferentialEqn x y
          -> PointsWeb x iy -> m (PointsWeb x iy)
filterDEqnSolutions_static_selective = case geodesicWitness :: GeodesicWitness y of
   GeodesicWitness _ -> \strategy shading badness f
       ->  -- Integration step: determine at each point from the function values
           -- what the derivatives should be, and use them to propagate the solution
           -- in all directions. We only spend a single computation step on regions
           -- where nothing much changes (indicating the a-priori information is
           -- too weak yet to make any predictions anyway), but multiple steps in
           -- regions where good progress is noticed.
         fmap fst . (runWriterT :: WriterT (Average badness) m (PointsWeb x iy)
                                        -> m (PointsWeb x iy, Average badness))
         . treewiseTraverseLocalWeb ( \me
          -> let oldValue = me^.thisNodeData :: iy
                 badHere = badness $ me^.thisNodeCoord
                 oldBadness = badHere oldValue
             in if me ^. nodeIsOnBoundary
                 then return oldValue
                 else case me^.nodeNeighbours of
                  [] -> pure oldValue
                  _:_ | BoundarylessWitness <- (boundarylessWitness::BoundarylessWitness x)
                    -> WriterT . fmap (\updated
                                    -> (updated, pure (oldBadness / badHere updated)))
                       $ sequenceA [ fmap ((me^.thisNodeCoord .+~^ δx,)
                                                   . (shading>-$))
                                  . mergeInformation strategy oldValue . Hask.toList
                                  $ (ngbInfo^.thisNodeCoord,)<$>
                                     propagateDEqnSolution_loc
                                       f (LocalDataPropPlan
                                             (ngbInfo^.thisNodeCoord)
                                             (negateV δx)
                                             (shading >-$ ngbInfo^.thisNodeData)
                                             (shading >-$ oldValue)
                                             (fmap (second ((shading>-$) . _thisNodeData))
                                               $ selectQuadraticFittableEnvironment
                                                        ngbInfo [me^.thisNodeId] )
                                          )
                                  | (_, (δx, ngbInfo)) <- me^.nodeNeighbours
                                  ]
                            >>= mergeInformation strategy oldValue )
                 (\combiner branchData -> WriterT $ do
                       (branchResults,improvements)
                         <- runWriterT $ Hask.traverse
                                          (\(i,branch) -> fmap (i,)
                                                          . censor (pure . (i,) . average)
                                                          $ combiner branch)
                                          branchData
                       let (best, _) = maximumBy (comparing snd) improvements
                       (branchResults',improvements')
                         <- runWriterT $ Hask.traverse
                                          (\(i,branch) -> if i==best
                                             then censor (pure . (i,) . average)
                                                              $ combiner branch
                                             else WriterT $ return (branch, pure (i,1)) )
                                          branchResults
                       return ( branchResults'
                              , liftA2 (*) (averaging $ snd<$>improvements)
                                           (averaging $ snd<$>improvements') )
                 )
          >=> -- Boundary-condition / differentiation step: update the local values
              -- based on a-priori boundary conditions, possibly dependent on
              -- numerical derivatives of the current solution estimate.
              localTraverseWeb (\me -> fmap (shading$->)
                                         . maybeAlt $ rescanPDELocally f me)
            . fmap (shading>-$)

-- | The <http://hackage.haskell.org/package/transformers-0.5.4.0/docs/Control-Monad-Trans-Writer-Lazy.html#v:censor transformers version of this>
--   is insufficiently polymorphic, requiring @w ~ w'@.
censor :: Functor m (->) (->) => (w -> w') -> WriterT w m a -> WriterT w' m a
censor = mapWriterT . fmap . second



handleInconsistency :: InconsistencyStrategy m x a -> a -> Maybe a -> m a
handleInconsistency AbortOnInconsistency _ i = i
handleInconsistency IgnoreInconsistencies _ (Just v) = Identity v
handleInconsistency IgnoreInconsistencies b _ = Identity b
handleInconsistency (HighlightInconsistencies _) _ (Just v) = Identity v
handleInconsistency (HighlightInconsistencies b) _ _ = Identity b

data SolverNodeState x y = SolverNodeInfo {
      _solverNodeStatus :: ConvexSet y
    , _solverNodeJacobian :: Shade' (LocalLinear x y)
    , _solverNodeBadness :: ℝ
    , _solverNodeAge :: Int
    }
makeLenses ''SolverNodeState


type OldAndNew d = (Maybe d, [d])

oldAndNew :: OldAndNew d -> [d]
oldAndNew (Just x, l) = x : l
oldAndNew (_, l) = l

oldAndNew' :: OldAndNew d -> [(Bool, d)]
oldAndNew' (Just x, l) = (True, x) : fmap (False,) l
oldAndNew' (_, l) = (False,) <$> l


filterDEqnSolutions_adaptive :: ∀ x y ð badness m
        . ( WithField ℝ Manifold x, FlatSpace (Needle x)
          , WithField ℝ AffineManifold y, Refinable y, Geodesic y, FlatSpace (Needle y)
          , badness ~ ℝ, Hask.Monad m )
       => MetricChoice x      -- ^ Scalar product on the domain, for regularising the web.
       -> InconsistencyStrategy m x (Shade' y)
       -> DifferentialEqn x y
       -> (x -> Shade' y -> badness)
             -> PointsWeb x (SolverNodeState x y)
                        -> m (PointsWeb x (SolverNodeState x y))
filterDEqnSolutions_adaptive mf strategy f badness' oldState
            = fmap recomputeJacobian $ filterGo boundarylessWitness geodesicWitness
                                         =<< tryPreproc boundarylessWitness geodesicWitness
 where tryPreproc :: BoundarylessWitness x -> GeodesicWitness y
                      -> m (PointsWeb x ( (WebLocally x (SolverNodeState x y)
                                        , [(Shade' y, badness)]) ))
       tryPreproc BoundarylessWitness (GeodesicWitness _)
               = Hask.traverse addPropagation $ webLocalInfo oldState
        where addPropagation wl
                 | null neighbourInfo = pure (wl, [])
                 | otherwise           = (wl,) . map (id&&&badness undefined)
                                           <$> propFromNgbs
               where propFromNgbs :: m [Shade' y]
                     propFromNgbs = mapM (handleInconsistency strategy thisShy) [
                                       propagateDEqnSolution_loc f
                                        (LocalDataPropPlan
                                           (neigh^.thisNodeCoord)
                                           (negateV δx)
                                           (convexSetHull $ neigh^.thisNodeData
                                                                  .solverNodeStatus)
                                           thisShy
                                           [ second (convexSetHull
                                                     . _solverNodeStatus . _thisNodeData) nn
                                           | (_,nn)<-neigh^.nodeNeighbours ] )
                                     | (δx, neigh) <- neighbourInfo ]  -- ( (thisPos, thisShy), NE.fromList neighbourHulls )
                     thisPos = _thisNodeCoord wl :: x
                     thisShy = convexSetHull . _solverNodeStatus $ _thisNodeData wl
                     neighbourInfo = snd <$> _nodeNeighbours wl

       totalAge = maximum $ _solverNodeAge <$> oldState
       errTgtModulation = (1-) . (`mod'`1) . negate . sqrt $ fromIntegral totalAge
       badness x = badness' x . (shadeNarrowness %~ (scaleNorm errTgtModulation))
              
       filterGo :: BoundarylessWitness x -> GeodesicWitness y
                   -> (PointsWeb x ( (WebLocally x (SolverNodeState x y)
                                   , [(Shade' y, badness)]) ))
                   -> m (PointsWeb x (SolverNodeState x y))
       filterGo BoundarylessWitness (GeodesicWitness _) preproc'd
             = fmap (smoothenWebTopology mf
                                     . fromTopWebNodes mf . concat . fmap retraceBonds
                                        . Hask.toList . webLocalInfo . webLocalInfo)
             $ Hask.traverse (uncurry localChange) preproc'd
        where smallBadnessGradient, largeBadnessGradient :: ℝ
              (smallBadnessGradient, largeBadnessGradient)
                  = ( badnessGradRated!!(n`div`4), badnessGradRated!!(n*3`div`4) )
               where n = case length badnessGradRated of
                           0 -> error "No statistics available for badness-grading."
                           l -> l
                     badnessGradRated :: [badness]
                     badnessGradRated = sort [ ngBad / bad
                                             | ( LocalWebInfo {
                                                   _thisNodeData
                                                     = SolverNodeInfo _ _ bad _
                                                 , _nodeNeighbours=ngbs        }
                                               , ngbProps) <- Hask.toList preproc'd
                                             , (_, ngBad) <- ngbProps
                                             , ngBad>bad ]
              localChange :: WebLocally x (SolverNodeState x y) -> [(Shade' y, badness)]
                                    -> m (OldAndNew (x, SolverNodeState x y))
              localChange localInfo@LocalWebInfo{
                                _thisNodeCoord = x
                              , _thisNodeData = SolverNodeInfo
                                                   shy@(ConvexSet hull _) prevJacobi
                                                   prevBadness age
                              , _nodeNeighbours = ngbs
                              }
                          ngbProps
               | null ngbs  = return ( pure (x, SolverNodeInfo shy prevJacobi
                                                           prevBadness (age+1))
                                     , [] )
               | otherwise  = do
                      let (environAge, unfreshness)
                             = maximum&&&minimum $ age : (_solverNodeAge . _thisNodeData
                                                               . snd . snd <$> ngbs)
                      case find (\(_, badnessN)
                                      -> badnessN / prevBadness > smallBadnessGradient)
                                     $ ngbProps of
                        Nothing | age < environAge   -- point is an obsolete step-stone;
                          -> return (empty,empty)    -- do not further use it.
                        _otherwise -> do
                          shy' <- handleInconsistency (ellipsoid<$>strategy) shy
                                  $ ((shy<>) . ellipsoid)
                                   <$> intersectShade's (fst <$> NE.fromList ngbProps)
                          newBadness
                               <- handleInconsistency (badness x<$>strategy) prevBadness
                                      $ case shy' of
                             EmptyConvex        -> empty
                             ConvexSet hull' _  -> return $ badness x hull'
                          let updatedNode = SolverNodeInfo shy' prevJacobi
                                                     newBadness (age+1)
                          stepStones <-
                            if unfreshness < 3
                             then return []
                             else fmap concat . forM (zip (second _thisNodeData.snd<$>ngbs)
                                                          ngbProps)
                                          $ \( (vN, SolverNodeInfo (ConvexSet hullN _)
                                                               _ _ ageN)
                                               , (_, nBadnessProp'd) ) -> do
                              case ageN of
                               _  | ageN > 0
                                  , badnessGrad <- nBadnessProp'd / prevBadness
                                  , badnessGrad > largeBadnessGradient -> do
                                        let stepV = vN^/2
                                            xStep = x .+~^ stepV
                                            aprioriInterpolate :: Shade' y
                                            Just aprioriInterpolate
                                               = middleBetween hull hullN
                                        case intersectShade's =<<
                                               (sequenceA $ NE.fromList
                                               [ propagateDEqnSolution_loc f
                                                   (LocalDataPropPlan
                                                      (n^.thisNodeCoord)
                                                      (stepV ^-^ δx)
                                                      (convexSetHull $
                                                        n^.thisNodeData.solverNodeStatus)
                                                      aprioriInterpolate
                                                      (second (convexSetHull
                                                               ._solverNodeStatus
                                                               ._thisNodeData)
                                                              . snd
                                                              <$> n^.nodeNeighbours) )
                                                -- ( (xStep, hull)
                                                -- , NE.cons (negateV stepV, hull)
                                                --     $ fmap (\(vN',hullN')
                                                --              -> (vN'^-^stepV, hullN') ) )
                                                | (_, (δx, n)) <- ngbs ]) of
                                         Just shyStep -> return
                                               [( xStep
                                                , SolverNodeInfo (ellipsoid shyStep)
                                                       prevJacobi (badness xStep shyStep) 1
                                                )]
                                         _ -> return []
                               _otherwise -> return []
                          let updated = (x, updatedNode)
                          return $ (pure updated, stepStones)
              
              retraceBonds :: WebLocally x (WebLocally x (OldAndNew (x, SolverNodeState x y)))
                              -> [((x, [Int+Needle x]), SolverNodeState x y)]
              retraceBonds locWeb@LocalWebInfo{ _thisNodeId = myId
                                              , _thisNodeCoord = xOld
                                              , _nodeLocalScalarProduct = locMetr }
                   = [ ( (x, Right . fst<$>neighbourCandidates), snsy)
                     | (isOld, (x, snsy)) <- focused
                     , let neighbourCandidates
                            = [ (v,nnId)
                              | (_,ngb) <- knownNgbs
                              , (Just v, nnId)
                                 <- case oldAndNew $ ngb^.thisNodeData of
                                          [] -> [ (xN.-~.x, nnId)
                                                | (nnId, (_,nnWeb)) <- ngb^.nodeNeighbours
                                                , nnId /= myId
                                                , (xN,_) <- oldAndNew $ nnWeb^.thisNodeData ]
                                          l -> [(xN.-~.x, ngb^.thisNodeId) | (xN,_) <- l]
                              ]
                           possibleConflicts = [ normSq locMetr v
                                               | (v,nnId)<-neighbourCandidates
                                               , nnId > myId ]
                     , isOld || null possibleConflicts
                         || minimum possibleConflicts > oldMinDistSq / 4
                     ]
               where focused = oldAndNew' $ locWeb^.thisNodeData^.thisNodeData
                     knownNgbs = second _thisNodeData . snd <$> locWeb^.nodeNeighbours
                     oldMinDistSq = minimum [ normSq locMetr vOld
                                            | (_,ngb) <- knownNgbs
                                            , let Just vOld = ngb^.thisNodeCoord .-~. xOld
                                            ]
                              
recomputeJacobian :: ( WithField ℝ Manifold x, SimpleSpace (Needle x)
                     , WithField ℝ Manifold y, SimpleSpace (Needle y), Refinable y )
             => PointsWeb x (SolverNodeState x y)
             -> PointsWeb x (SolverNodeState x y)
recomputeJacobian = webLocalInfo
                >>> fmap ((_thisNodeData
                           &&& differentiateUncertainWebLocally
                                   . fmap (convexSetHull . _solverNodeStatus))
                          >>> \(nst, shj) -> nst & solverNodeJacobian .~ shj )


iterateFilterDEqn_adaptive
     :: ( WithField ℝ Manifold x, FlatSpace (Needle x)
        , WithField ℝ AffineManifold y, Refinable y, Geodesic y, FlatSpace (Needle y)
        , Hask.Monad m )
       => MetricChoice x      -- ^ Scalar product on the domain, for regularising the web.
       -> InconsistencyStrategy m x (Shade' y)
       -> DifferentialEqn x y
       -> (x -> Shade' y -> ℝ) -- ^ Badness function for local results.
             -> PointsWeb x (Shade' y) -> [PointsWeb x (Shade' y)]
iterateFilterDEqn_adaptive mf strategy f badness
    = map (fmap (convexSetHull . _solverNodeStatus))
    . itWhileJust strategy (filterDEqnSolutions_adaptive mf strategy f badness)
    . recomputeJacobian
    . fmap (\((x,shy),_) -> SolverNodeInfo (ellipsoid shy)
                                           (Shade' zeroV mempty)
                                           (badness x shy)
                                           1
           )
    . localFocusWeb




