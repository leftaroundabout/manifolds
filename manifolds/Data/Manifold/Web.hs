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
            , nearestNeighbour, indexWeb, webEdges, toGraph
              -- ** Decomposition
            , sliceWeb_lin -- , sampleWebAlongLine_lin
            , sampleWeb_2Dcartesian_lin, sampleEntireWeb_2Dcartesian_lin
              -- ** Local environments
            , localFocusWeb
              -- * Differential equations
              -- ** Fixed resolution
            , filterDEqnSolution_static, iterateFilterDEqn_static
--               -- ** Automatic resolution
--             , filterDEqnSolutions_adaptive, iterateFilterDEqn_adaptive
              -- ** Configuration
            , InconsistencyStrategy(..)
              -- * Misc
            , ConvexSet(..), ellipsoid, coerceWebDomain
            ) where


import Data.List hiding (filter, all, elem, sum, foldr1)
import Data.Maybe
import qualified Data.Set as Set
import qualified Data.Vector as Arr
import qualified Data.Vector.Unboxed as UArr
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE
import Data.List.FastNub (fastNubBy)
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
import Data.Manifold.TreeCover
import Data.SetLike.Intersection
import Data.Manifold.Riemannian
    
import qualified Prelude as Hask hiding(foldl, sum, sequence)
import qualified Control.Applicative as Hask
import qualified Control.Monad       as Hask hiding(forM_, sequence)
import Control.Monad.Trans.State
import Control.Monad.Trans.List
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
import Control.Lens ((&), (%~), (^.), (.~))
import Control.Lens.TH

import GHC.Generics (Generic)


type WebNodeId = Int

data Neighbourhood x = Neighbourhood {
     _neighbours :: UArr.Vector WebNodeId
   , _localScalarProduct :: Metric x
   }
  deriving (Generic)
makeLenses ''Neighbourhood

instance (NFData x, NFData (Metric x)) => NFData (Neighbourhood x)

-- | A 'PointsWeb' is almost, but not quite a mesh. It is a stongly connected†
--   directed graph, backed by a tree for fast nearest-neighbour lookup of points.
-- 
--   †In general, there can be disconnected components, but every connected
--   component is strongly connected.
data PointsWeb :: * -> * -> * where
   PointsWeb :: {
       webNodeRsc :: ShadeTree x
     , webNodeAssocData :: Arr.Vector (y, Neighbourhood x)
     } -> PointsWeb x y
  deriving (Generic, Hask.Functor, Hask.Foldable, Hask.Traversable)

instance (NFData x, NFData (Metric x), NFData (Needle' x), NFData y) => NFData (PointsWeb x y)

instance Foldable (PointsWeb x) (->) (->) where
  ffoldl = uncurry . Hask.foldl' . curry
  foldMap = Hask.foldMap
instance Traversable (PointsWeb x) (PointsWeb x) (->) (->) where
  traverse f (PointsWeb rsc asd)
           = fmap (PointsWeb rsc . (`Arr.zip`ngss) . Arr.fromList)
              . traverse f $ Arr.toList ys
   where (ys,ngss) = Arr.unzip asd



type MetricChoice x = Shade x -> Metric x


fromWebNodes :: ∀ x y . (WithField ℝ Manifold x, SimpleSpace (Needle x))
                    => (MetricChoice x) -> [(x,y)] -> PointsWeb x y
fromWebNodes mf = fromShaded mf . fromLeafPoints . map (uncurry WithAny . swap)

fromTopWebNodes :: ∀ x y . (WithField ℝ Manifold x, SimpleSpace (Needle x))
                    => (MetricChoice x) -> [((x,[Needle x]),y)] -> PointsWeb x y
fromTopWebNodes mf = fromTopShaded mf . fromLeafPoints
                   . map (uncurry WithAny . swap . regroup')

fromShadeTree_auto :: ∀ x . (WithField ℝ Manifold x, SimpleSpace (Needle x)) => ShadeTree x -> PointsWeb x ()
fromShadeTree_auto = fromShaded (dualNorm . _shadeExpanse) . constShaded ()

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
fromShaded metricf = fromTopShaded metricf . fmapShaded ([],)

fromTopShaded :: ∀ x y . (WithField ℝ Manifold x, SimpleSpace (Needle x))
     => (MetricChoice x)
     -> (x`Shaded`([Needle x], y))  -- ^ Source tree, with a priori topology information
                                    --   (needles pointing to already-known neighbour candidates)
     -> PointsWeb x y
fromTopShaded metricf shd = PointsWeb shd' assocData 
 where shd' = stripShadedUntopological shd
       assocData = Hask.foldMap locMesh $ twigsWithEnvirons shd
       
       locMesh :: ( (Int, ShadeTree (x`WithAny`([Needle x], y)))
                  , [(Int, ShadeTree (x`WithAny`([Needle x], y)))])
                   -> Arr.Vector (y, Neighbourhood x)
       locMesh ((i₀, locT), neighRegions) = Arr.map findNeighbours $ Arr.fromList locLeaves
        where locLeaves :: [ (Int, x`WithAny`([Needle x], y)) ]
              locLeaves = map (first (+i₀)) . zip [0..] $ onlyLeaves locT
              vicinityLeaves :: [(Int, x)]
              vicinityLeaves = Hask.foldMap
                                (\(i₀n, ngbR) -> map ((+i₀n) *** _topological)
                                               . zip [0..]
                                               $ onlyLeaves ngbR
                                ) neighRegions
              findNeighbours :: (Int, x`WithAny`([Needle x], y)) -> (y, Neighbourhood x)
              findNeighbours (i, WithAny (vns,y) x)
                         = (y, Neighbourhood
                                 (UArr.fromList $ fst<$>execState seek mempty)
                                 locRieM )
               where seek :: State [(Int, (Needle x, Needle' x))] ()
                     seek = do
                        Hask.forM_ ( fastNubBy (comparing fst)
                                      $ map (second _topological) locLeaves
                                           ++ vicinityLeaves ++ aprioriNgbs )
                                  $ \(iNgb, xNgb) ->
                           when (iNgb/=i) `id`do
                              let (Option (Just v)) = xNgb.-~.x
                              oldNgbs <- get
                              when (all (\(_,(_,nw)) -> visibleOverlap nw v) oldNgbs) `id`do
                                 let w = w₀ ^/ (w₀<.>^v)
                                      where w₀ = locRieM<$|v
                                 put $ (iNgb, (v,w))
                                       : [ neighbour
                                         | neighbour@(_,(nv,_))<-oldNgbs
                                         , visibleOverlap w nv
                                         ]
                     aprioriNgbs :: [(Int, x)]
                     aprioriNgbs = catMaybes
                                    [ getOption $ (second $ const xN) <$>
                                          positionIndex (pure locRieM) shd' xN
                                    | v <- vns
                                    , let xN = x.+~^v :: x ]
              
              visibleOverlap :: Needle' x -> Needle x -> Bool
              visibleOverlap w v = o < 1
               where o = w<.>^v
              
              locRieM :: Metric x
              locRieM = case pointsCovers . map _topological
                                  $ onlyLeaves locT
                                   ++ Hask.foldMap (onlyLeaves . snd) neighRegions of
                          [sh₀] -> metricf sh₀

indexWeb :: (WithField ℝ Manifold x, SimpleSpace (Needle x))
                => PointsWeb x y -> WebNodeId -> Option (x,y)
indexWeb (PointsWeb rsc assocD) i
  | i>=0, i<Arr.length assocD
  , Right (_,x) <- indexShadeTree rsc i  = pure (x, fst (assocD Arr.! i))
  | otherwise                            = empty

unsafeIndexWebData :: PointsWeb x y -> WebNodeId -> y
unsafeIndexWebData (PointsWeb _ asd) i = fst (asd Arr.! i)

webEdges :: ∀ x y . (WithField ℝ Manifold x, SimpleSpace (Needle x))
            => PointsWeb x y -> [((x,y), (x,y))]
webEdges web@(PointsWeb rsc assoc) = (lookId***lookId) <$> toList allEdges
 where allEdges :: Set.Set (WebNodeId,WebNodeId)
       allEdges = Hask.foldMap (\(i,(_, Neighbourhood ngbs _))
                    -> Set.fromList [(min i i', max i i')
                                    | i'<-UArr.toList ngbs ]
                               ) $ Arr.indexed assoc
       lookId i | Option (Just xy) <- indexWeb web i  = xy


coerceWebDomain :: ∀ a b y . (Manifold a, Manifold b, LocallyCoercible a b)
                                 => PointsWeb a y -> PointsWeb b y
coerceWebDomain (PointsWeb rsc assoc)
         = case oppositeLocalCoercion :: CanonicalDiffeomorphism b a of
   CanonicalDiffeomorphism
       -> PointsWeb ( coerceShadeTree rsc )
                    ( fmap (second $ localScalarProduct
                              %~transformNorm (arr $ coerceNeedle ([]::[(b,a)])))
                         assoc )


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
 where Option (Just yio) = geodesicBetween yψ yω
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
 where edgs = webEdges web
       sliceEdgs cp = [ (xi d, yi d)  -- Brute-force search through all edges
                      | ((x₀,y₀), (x₁,y₁)) <- edgs
                      , Option (Just d) <- [cutPosBetween cp (x₀,x₁)]
                      , Option (Just xi) <- [geodesicBetween x₀ x₁]
                      , Option (Just yi) <- [geodesicBetween y₀ y₁]
                      ]

-- sampleWebAlongLine_lin :: ∀ x y . (WithField ℝ Manifold x, Geodesic x, Geodesic y)
--                => PointsWeb x y -> x -> Needle x -> [(x,y)]
-- sampleWebAlongLine_lin web x₀ dir = sampleWebAlongLines_lin web x₀ [(dir, maxBound)]


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
      , let x₀' = x₀.+~^(fromIntegral k *^ spcΩ) ]

sampleWebAlongGrid_lin :: ∀ x y . ( WithField ℝ Manifold x, SimpleSpace (Needle x)
                                  , Geodesic x, Geodesic y )
               => PointsWeb x y -> GridSetup x -> [(x,Option y)]
sampleWebAlongGrid_lin web grid = finalLine =<< splitToGridLines web grid
 where finalLine :: ((x, GridPlanes x), [(x,y)]) -> [(x,Option y)]
       finalLine ((x₀, GridPlanes _ dir nSpl), verts)
          | length verts < 2  = take nSpl $ (,empty)<$>iterate (.+~^dir) x₀
       finalLine ((x₀, GridPlanes dx dir nSpl), verts)  = take nSpl $ go (x₀,0) intpseq 
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
             => PointsWeb (x,y) z -> ((x,x),Int) -> ((y,y),Int) -> [(y,[(x,Option z)])]
sampleWeb_2Dcartesian_lin web (xspec@(_,nx)) yspec
       = go . sampleWebAlongGrid_lin web $ cartesianGrid2D xspec yspec
 where go [] = []
       go l@(((_,y),_):_) = let (ln,l') = splitAt nx l
                             in (y, map (\((x,_),z) -> (x,z)) ln) : go l'
       
sampleEntireWeb_2Dcartesian_lin :: (x~ℝ, y~ℝ, Geodesic z)
             => PointsWeb (x,y) z -> Int -> Int -> [(y,[(x,Option z)])]
sampleEntireWeb_2Dcartesian_lin web nx ny
       = sampleWeb_2Dcartesian_lin web ((x₀,x₁),nx) ((y₀,y₁),ny)
 where x₀ = minimum (fst<$>pts)
       x₁ = maximum (fst<$>pts)
       y₀ = minimum (snd<$>pts)
       y₁ = maximum (snd<$>pts)
       pts = fst . fst <$> toList (localFocusWeb web)

webLocalInfo :: ∀ x y . WithField ℝ Manifold x
            => PointsWeb x y -> PointsWeb x (WebLocally x y)
webLocalInfo origWeb = result
 where result = wli $ localFocusWeb origWeb
       wli (PointsWeb rsc asd) = PointsWeb rsc asd'
        where asd' = Arr.imap localInfo asd
       localInfo i (((x,y), ngbCo), ngbH)
            = ( LocalWebInfo {
                  _thisNodeCoord = x
                , _thisNodeData = y
                , _thisNodeId = i
                , _nodeNeighbours = [ (iNgb, (δx, neighbour))
                                    | iNgb <- UArr.toList $ ngbH^.neighbours
                                    , let neighbour = unsafeIndexWebData result iNgb
                                          Option (Just δx) = _thisNodeCoord neighbour.-~.x
                                    ]
                , _nodeLocalScalarProduct = ngbH^.localScalarProduct
                , _nodeIsOnBoundary = anyUnopposed (ngbH^.localScalarProduct) ngbCo
                }, ngbH )
       anyUnopposed rieM ngbCo = (`any`ngbCo) $ \(v,_)
                         -> not $ (`any`ngbCo) $ \(v',_)
                              -> (rieM<$|v) <.>^ v' < 0

localFocusWeb :: WithField ℝ Manifold x
                   => PointsWeb x y -> PointsWeb x ((x,y), [(Needle x, y)])
localFocusWeb (PointsWeb rsc asd) = PointsWeb rsc asd''
 where asd' = Arr.imap (\i (y,n) -> case indexShadeTree rsc i of
                                         Right (_,x) -> ((x,y),n) ) asd
       asd''= Arr.map (\((x,y),n) ->
                       (((x,y), [ ( case x'.-~.x of
                                     Option (Just v) -> v
                                  , y')
                                | j<-UArr.toList (n^.neighbours)
                                , let ((x',y'),_) = asd' Arr.! j
                                ]), n)
                 ) asd'


nearestNeighbour :: (WithField ℝ Manifold x, SimpleSpace (Needle x))
                      => PointsWeb x y -> x -> Option (x,y)
nearestNeighbour (PointsWeb rsc asd) x = fmap lkBest $ positionIndex empty rsc x
 where lkBest (iEst, (_, xEst)) = (xProx, yProx)
        where (iProx, (xProx, _)) = minimumBy (comparing $ snd . snd)
                                     $ (iEst, (xEst, normSq locMetr vEst))
                                         : neighbours
              (yProx, _) = asd Arr.! iProx
              (_, Neighbourhood neighbourIds locMetr) = asd Arr.! iEst
              neighbours = [ (i, (xNgb, normSq locMetr v))
                           | i <- UArr.toList neighbourIds
                           , let Right (_, xNgb) = indexShadeTree rsc i
                                 Option (Just v) = xNgb.-~.x
                           ]
              Option (Just vEst) = xEst.-~.x



data WebLocally x y = LocalWebInfo {
      _thisNodeCoord :: x
    , _thisNodeData :: y
    , _thisNodeId :: WebNodeId
    , _nodeNeighbours :: [(WebNodeId, (Needle x, WebLocally x y))]
    , _nodeLocalScalarProduct :: Metric x
    , _nodeIsOnBoundary :: Bool
    } deriving (Generic)
makeLenses ''WebLocally

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

differentiateUncertainWebLocally :: ∀ x y
   . ( WithField ℝ Manifold x, SimpleSpace (Needle x)
     , WithField ℝ Manifold y, SimpleSpace (Needle y), Refinable y )
            => WebLocally x (Shade' y)
             -> Shade' (LocalLinear x y)
differentiateUncertainWebLocally info = j
 where Option (Just j) = estimateLocalJacobian
                          (info^.nodeLocalScalarProduct)
                          [ ( Local δx :: Local x, ngb^.thisNodeData )
                          | (_,(δx,ngb))<-info^.nodeNeighbours
                          ]



toGraph :: (WithField ℝ Manifold x, SimpleSpace (Needle x))
              => PointsWeb x y -> (Graph, Vertex -> (x, y))
toGraph wb = second (>>> \(i,_,_) -> case indexWeb wb i of {Option (Just xy) -> xy})
                (graphFromEdges' edgs)
 where edgs :: [(Int, Int, [Int])]
       edgs = Arr.toList
            . Arr.imap (\i (_, Neighbourhood ngbs _) -> (i, i, UArr.toList ngbs))
                    $ webNodeAssocData wb




data ConvexSet x
    = EmptyConvex
    | ConvexSet {
      convexSetHull :: Shade' x
      -- ^ If @p@ is in all intersectors, it must also be in the hull.
    , convexSetIntersectors :: [Shade' x]
    }
deriving instance ( WithField ℝ Manifold x, SimpleSpace (Needle x)
                  , Show x, Show (Needle' x) ) => Show (ConvexSet x)

ellipsoid :: Shade' x -> ConvexSet x
ellipsoid s = ConvexSet s [s]

intersectors :: ConvexSet x -> Option (NonEmpty (Shade' x))
intersectors (ConvexSet h []) = pure (h:|[])
intersectors (ConvexSet _ (i:sts)) = pure (i:|sts)
intersectors _ = empty

-- | Under intersection.
instance Refinable x => Semigroup (ConvexSet x) where
  a<>b = sconcat (a:|[b])
  sconcat csets
    | Option (Just allIntersectors) <- sconcat <$> Hask.traverse intersectors csets
    , IntersectT ists <- rmTautologyIntersect perfectRefine $ IntersectT allIntersectors
    , Option (Just hull') <- intersectShade's ists
                 = ConvexSet hull' (NE.toList ists)
    | otherwise  = EmptyConvex
   where perfectRefine sh₁ sh₂
           | sh₁`subShade'`sh₂   = pure sh₁
           | sh₂`subShade'`sh₁   = pure sh₂
           | otherwise           = empty



itWhileJust :: InconsistencyStrategy m -> (a -> m a) -> a -> [a]
itWhileJust AbortOnInconsistency f x
 | Option (Just y) <- f x  = x : itWhileJust AbortOnInconsistency f y
itWhileJust IgnoreInconsistencies f x
 | Identity y <- f x  = x : itWhileJust IgnoreInconsistencies f y
itWhileJust _ _ x = [x]

dupHead :: NonEmpty a -> NonEmpty a
dupHead (x:|xs) = x:|x:xs



data InconsistencyStrategy m where
    AbortOnInconsistency :: InconsistencyStrategy Option
    IgnoreInconsistencies :: InconsistencyStrategy Identity


iterateFilterDEqn_static :: ( WithField ℝ Manifold x, SimpleSpace (Needle x)
                            , Refinable y, Geodesic y
                            , Hask.Applicative m )
       => InconsistencyStrategy m -> DifferentialEqn x y
                 -> PointsWeb x (Shade' y) -> [PointsWeb x (Shade' y)]
iterateFilterDEqn_static strategy f
                           = map (fmap convexSetHull)
                           . itWhileJust strategy (filterDEqnSolutions_static strategy f)
                           . fmap (`ConvexSet`[])

filterDEqnSolution_static :: ( WithField ℝ Manifold x, SimpleSpace (Needle x)
                             , Refinable y, Geodesic y )
       => InconsistencyStrategy m -> DifferentialEqn x y
            -> PointsWeb x (Shade' y) -> m (PointsWeb x (Shade' y))
filterDEqnSolution_static AbortOnInconsistency f
       = webLocalInfo >>> fmap (id &&& differentiateUncertainWebLocally) >>> localFocusWeb
           >>> Hask.traverse `id`\((_,(me,_)), ngbs) -> case ngbs of
                  []  -> return $ me^.thisNodeData
                  _:_ -> refineShade' (me^.thisNodeData)
                            =<< intersectShade's
                            =<< Option ( sequenceA $ NE.fromList
                                  [ propagateDEqnSolution_loc
                                       f (LocalDataPropPlan
                                             (ngbInfo^.thisNodeCoord)
                                             (negateV δx)
                                             (ngbInfo^.thisNodeData)
                                             (me^.thisNodeData)
                                             (fmap (second _thisNodeData . snd)
                                                       $ ngbInfo^.nodeNeighbours)
                                          ) sj
                                  | (δx, (ngbInfo,sj)) <- ngbs
                                  ] )

filterDEqnSolutions_static :: ∀ x y m .
                              ( WithField ℝ Manifold x, SimpleSpace (Needle x)
                              , Refinable y, Geodesic y
                              , Hask.Applicative m )
       => InconsistencyStrategy m -> DifferentialEqn x y
            -> PointsWeb x (ConvexSet y) -> m (PointsWeb x (ConvexSet y))
filterDEqnSolutions_static strategy f
       = webLocalInfo
           >>> fmap (id &&& differentiateUncertainWebLocally . fmap convexSetHull)
           >>> localFocusWeb >>> Hask.traverse `id`\((_,(me,_)), ngbs)
             -> let oldValue = me^.thisNodeData :: ConvexSet y
                in case ngbs of
                  []  -> pure oldValue
                  _:_ -> handleInconsistency strategy oldValue
                          $ Option ( sequenceA $ NE.fromList
                                  [ propagateDEqnSolution_loc
                                       f (LocalDataPropPlan
                                             (ngbInfo^.thisNodeCoord)
                                             (negateV δx)
                                             (convexSetHull $ ngbInfo^.thisNodeData)
                                             (convexSetHull $ me^.thisNodeData)
                                             (fmap (second (convexSetHull . _thisNodeData)
                                                             . snd)
                                                       $ ngbInfo^.nodeNeighbours)
                                          ) sj
                                  | (δx, (ngbInfo,sj)) <- ngbs
                                  ] )
                            >>= intersectShade's
                            >>= pure . ((oldValue<>) . ellipsoid)
                            >>= \case EmptyConvex -> empty
                                      c           -> pure c

handleInconsistency :: InconsistencyStrategy m -> a -> Option a -> m a
handleInconsistency AbortOnInconsistency _ i = i
handleInconsistency IgnoreInconsistencies _ (Option (Just v)) = Identity v
handleInconsistency IgnoreInconsistencies b _ = Identity b

data SolverNodeState x y = SolverNodeInfo {
      _solverNodeStatus :: ConvexSet y
    , _solverNodeJacobian :: Shade' (LocalLinear x y)
    , _solverNodeBadness :: ℝ
    , _solverNodeAge :: Int
    }
makeLenses ''SolverNodeState


type OldAndNew d = (Option d, [d])

oldAndNew :: OldAndNew d -> [d]
oldAndNew (Option (Just x), l) = x : l
oldAndNew (_, l) = l

oldAndNew' :: OldAndNew d -> [(Bool, d)]
oldAndNew' (Option (Just x), l) = (True, x) : fmap (False,) l
oldAndNew' (_, l) = (False,) <$> l


filterDEqnSolutions_adaptive :: ∀ x y badness m
        . ( WithField ℝ Manifold x, SimpleSpace (Needle x), Refinable y, Geodesic y
          , badness ~ ℝ, Hask.Monad m )
       => MetricChoice x      -- ^ Scalar product on the domain, for regularising the web.
       -> InconsistencyStrategy m
       -> DifferentialEqn x y 
       -> (x -> Shade' y -> badness)
             -> PointsWeb x (SolverNodeState x y)
                        -> m (PointsWeb x (SolverNodeState x y))
filterDEqnSolutions_adaptive mf strategy f badness' oldState
            = fmap recomputeJacobian $ filterGo =<< tryPreproc
 where tryPreproc :: m (PointsWeb x ( (WebLocally x (SolverNodeState x y)
                                    , [(Shade' y, badness)]) ))
       tryPreproc = traverse addPropagation $ webLocalInfo oldState
        where addPropagation wl
                 | null neighbourInfo = pure (wl, [])
                 | otherwise           = (wl,) . map (id&&&badness undefined)
                                           <$> propFromNgbs
               where propFromNgbs :: m [Shade' y]
                     propFromNgbs = mapM (handleInconsistency strategy thisShy . Option) [
                                       propagateDEqnSolution_loc f
                                        (LocalDataPropPlan
                                           (neigh^.thisNodeCoord)
                                           (negateV δx)
                                           (convexSetHull $ neigh^.thisNodeData
                                                                  .solverNodeStatus)
                                           (thisShy)
                                           [ second (convexSetHull
                                                     . _solverNodeStatus . _thisNodeData) nn
                                           | (_,nn)<-neigh^.nodeNeighbours ] )
                                        (wl^.thisNodeData.solverNodeJacobian)
                                     | (δx, neigh) <- neighbourInfo ]  -- ( (thisPos, thisShy), NE.fromList neighbourHulls )
                     thisPos = _thisNodeCoord wl :: x
                     thisShy = convexSetHull . _solverNodeStatus $ _thisNodeData wl
                     neighbourInfo = snd <$> _nodeNeighbours wl

       totalAge = maximum $ _solverNodeAge <$> oldState
       errTgtModulation = (1-) . (`mod'`1) . negate . sqrt $ fromIntegral totalAge
       badness x = badness' x . (shadeNarrowness %~ (scaleNorm errTgtModulation))
              
       filterGo :: (PointsWeb x ( (WebLocally x (SolverNodeState x y)
                                   , [(Shade' y, badness)]) ))
                      -> m (PointsWeb x (SolverNodeState x y))
       filterGo preproc'd   = fmap (fromTopWebNodes mf . concat . fmap retraceBonds
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
                          shy' <- handleInconsistency strategy shy
                                  $ ((shy<>) . ellipsoid)
                                   <$> intersectShade's (fst <$> NE.fromList ngbProps)
                          newBadness <- handleInconsistency strategy prevBadness $ case shy' of
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
                                            aprioriInterpolate = undefined
                                        case intersectShade's =<<
                                               (Option . sequenceA $ NE.fromList
                                               [ propagateDEqnSolution_loc f
                                                   (LocalDataPropPlan
                                                      (n^.thisNodeCoord)
                                                      (stepV ^-^ δx)
                                                      (convexSetHull $
                                                        n^.thisNodeData.solverNodeStatus)
                                                      (aprioriInterpolate)
                                                      (second (convexSetHull
                                                               ._solverNodeStatus
                                                               ._thisNodeData)
                                                              . snd
                                                              <$> n^.nodeNeighbours) )
                                                   (n^.thisNodeData.solverNodeJacobian)
                                                -- ( (xStep, hull)
                                                -- , NE.cons (negateV stepV, hull)
                                                --     $ fmap (\(vN',hullN')
                                                --              -> (vN'^-^stepV, hullN') ) )
                                                | (_, (δx, n)) <- ngbs ]) of
                                         Option (Just shyStep) -> return
                                               [( xStep
                                                , SolverNodeInfo (ellipsoid shyStep)
                                                       prevJacobi (badness xStep shyStep) 1
                                                )]
                                         _ -> return []
                               _otherwise -> return []
                          let updated = (x, updatedNode)
                          return $ (pure updated, stepStones)
              
              retraceBonds :: WebLocally x (WebLocally x (OldAndNew (x, SolverNodeState x y)))
                              -> [((x, [Needle x]), SolverNodeState x y)]
              retraceBonds locWeb@LocalWebInfo{ _thisNodeId = myId
                                              , _thisNodeCoord = xOld
                                              , _nodeLocalScalarProduct = locMetr }
                   = [ ( (x, fst<$>neighbourCandidates), snsy)
                     | (isOld, (x, snsy)) <- focused
                     , let neighbourCandidates
                            = [ (v,nnId)
                              | (_,ngb) <- knownNgbs
                              , (Option (Just v), nnId)
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
                                            , let Option (Just vOld) = ngb^.thisNodeCoord .-~. xOld
                                            ]
                              
recomputeJacobian :: ( WithField ℝ Manifold x, SimpleSpace (Needle x)
                     , WithField ℝ Manifold y, SimpleSpace (Needle y), Refinable y )
             => PointsWeb x (SolverNodeState x y)
             -> PointsWeb x (SolverNodeState x y)
recomputeJacobian = undefined


iterateFilterDEqn_adaptive
     :: ( WithField ℝ Manifold x, SimpleSpace (Needle x)
        , Refinable y, Geodesic y, Hask.Monad m )
       => MetricChoice x      -- ^ Scalar product on the domain, for regularising the web.
       -> InconsistencyStrategy m
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




