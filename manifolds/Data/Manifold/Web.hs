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


module Data.Manifold.Web (
              -- * The web data type
              PointsWeb
              -- ** Construction
            , fromWebNodes, fromShadeTree_auto, fromShadeTree, fromShaded
              -- ** Lookup
            , indexWeb, webEdges
              -- ** Local environments
            , localFocusWeb
              -- * Differential equations
              -- ** Fixed resolution
            , filterDEqnSolution_static, iterateFilterDEqn_static
              -- ** Automatic resolution
            , filterDEqnSolutions_adaptive, iterateFilterDEqn_adaptive
              -- * Misc
            , ConvexSet(..), ellipsoid
            ) where


import Data.List hiding (filter, all, elem, sum, foldr1)
import Data.Maybe
import qualified Data.Set as Set
import qualified Data.Vector as Arr
import qualified Data.Vector.Unboxed as UArr
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE
import Data.Semigroup
import Control.DeepSeq

import Data.VectorSpace
import Data.LinearMap.HerMetric
import Data.Tagged
import Data.Function (on)

import Data.Manifold.Types
import Data.Manifold.Types.Primitive (empty)
import Data.Manifold.PseudoAffine
import Data.Manifold.TreeCover
import Data.SetLike.Intersection
    
import qualified Prelude as Hask hiding(foldl, sum, sequence)
import qualified Control.Applicative as Hask
import qualified Control.Monad       as Hask hiding(forM_, sequence)
import Control.Monad.Trans.State
import Control.Monad.Trans.List
import qualified Data.Foldable       as Hask
import Data.Foldable (all, toList)
import qualified Data.Traversable as Hask
import Data.Traversable (forM)

import Control.Category.Constrained.Prelude hiding
     ((^), all, elem, sum, forM, Foldable(..), foldr1, Traversable, traverse)
import Control.Arrow.Constrained
import Control.Monad.Constrained hiding (forM)
import Data.Foldable.Constrained
import Data.Traversable.Constrained (Traversable, traverse)

import Control.Comonad (Comonad(..))

import GHC.Generics (Generic)


type WebNodeId = Int

data Neighbourhood x = Neighbourhood {
     neighbours :: UArr.Vector WebNodeId
   , localScalarProduct :: Metric x
   }
  deriving (Generic)

instance (NFData x, NFData (HerMetric (Needle x))) => NFData (Neighbourhood x)

data PointsWeb :: * -> * -> * where
   PointsWeb :: {
       webNodeRsc :: ShadeTree x
     , webNodeAssocData :: Arr.Vector (y, Neighbourhood x)
     } -> PointsWeb x y
  deriving (Generic, Hask.Functor, Hask.Foldable, Hask.Traversable)

instance (NFData x, NFData (HerMetric (Needle x)), NFData (Needle' x), NFData y) => NFData (PointsWeb x y)

instance Foldable (PointsWeb x) (->) (->) where
  ffoldl = uncurry . Hask.foldl' . curry
  foldMap = Hask.foldMap
instance Traversable (PointsWeb x) (PointsWeb x) (->) (->) where
  traverse f (PointsWeb rsc asd)
           = fmap (PointsWeb rsc . (`Arr.zip`ngss) . Arr.fromList)
              . traverse f $ Arr.toList ys
   where (ys,ngss) = Arr.unzip asd



fromWebNodes :: ∀ x y . WithField ℝ Manifold x
                    => (MetricChoice x) -> [(x,y)] -> PointsWeb x y
fromWebNodes mf = fromShaded mf . fromLeafPoints . map (uncurry WithAny . swap)

fromShadeTree_auto :: ∀ x . WithField ℝ Manifold x => ShadeTree x -> PointsWeb x ()
fromShadeTree_auto = fromShaded (recipMetric . _shadeExpanse) . constShaded ()

fromShadeTree :: ∀ x . WithField ℝ Manifold x
     => (Shade x -> Metric x) -> ShadeTree x -> PointsWeb x ()
fromShadeTree mf = fromShaded mf . constShaded ()

fromShaded :: ∀ x y . WithField ℝ Manifold x
     => (MetricChoice x) -- ^ Local scalar-product generator. You can always
                              --   use @'recipMetric' . '_shadeExpanse'@ (but this
                              --   may give distortions compared to an actual
                              --   Riemannian metric).
     -> (x`Shaded`y)          -- ^ Source tree.
     -> PointsWeb x y
fromShaded metricf shd = PointsWeb shd' assocData 
 where shd' = stripShadedUntopological shd
       assocData = Hask.foldMap locMesh $ twigsWithEnvirons shd
       
       locMesh :: ((Int, ShadeTree (x`WithAny`y)), [(Int, ShadeTree (x`WithAny`y))])
                   -> Arr.Vector (y, Neighbourhood x)
       locMesh ((i₀, locT), neighRegions) = Arr.map findNeighbours locLeaves
        where locLeaves = Arr.map (first (+i₀)) . Arr.indexed . Arr.fromList
                                          $ onlyLeaves locT
              vicinityLeaves = Hask.foldMap
                                (\(i₀n, ngbR) -> Arr.map (first (+i₀n))
                                               . Arr.indexed
                                               . Arr.fromList
                                               $ onlyLeaves ngbR
                                ) neighRegions
              findNeighbours :: (Int, x`WithAny`y) -> (y, Neighbourhood x)
              findNeighbours (i, WithAny y x)
                         = (y, Neighbourhood
                                 (UArr.fromList $ fst<$>execState seek mempty)
                                 locRieM )
               where seek = do
                        Hask.forM_ (locLeaves Arr.++ vicinityLeaves)
                                  $ \(iNgb, WithAny _ xNgb) ->
                           when (iNgb/=i) `id`do
                              let (Option (Just v)) = xNgb.-~.x
                              oldNgbs <- get
                              when (all (\(_,(_,nw)) -> visibleOverlap nw v) oldNgbs) `id`do
                                 let w = w₀ ^/ (w₀<.>^v)
                                      where w₀ = toDualWith locRieM v
                                 put $ (iNgb, (v,w))
                                       : [ neighbour
                                         | neighbour@(_,(nv,_))<-oldNgbs
                                         , visibleOverlap w nv
                                         ]
              
              visibleOverlap :: Needle' x -> Needle x -> Bool
              visibleOverlap w v = o < 1
               where o = w<.>^v
              
              locRieM :: Metric x
              locRieM = case pointsCovers . map _topological
                                  $ onlyLeaves locT
                                   ++ Hask.foldMap (onlyLeaves . snd) neighRegions of
                          [sh₀] -> metricf sh₀

indexWeb :: WithField ℝ Manifold x => PointsWeb x y -> WebNodeId -> Option (x,y)
indexWeb (PointsWeb rsc assocD) i
  | i>=0, i<Arr.length assocD
  , Right (_,x) <- indexShadeTree rsc i  = pure (x, fst (assocD Arr.! i))
  | otherwise                            = empty

unsafeIndexWebData :: PointsWeb x y -> WebNodeId -> y
unsafeIndexWebData (PointsWeb _ asd) i = fst (asd Arr.! i)

webEdges :: ∀ x y . WithField ℝ Manifold x
            => PointsWeb x y -> [((x,y), (x,y))]
webEdges web@(PointsWeb rsc assoc) = (lookId***lookId) <$> toList allEdges
 where allEdges :: Set.Set (WebNodeId,WebNodeId)
       allEdges = Hask.foldMap (\(i,(_, Neighbourhood ngbs _))
                    -> Set.fromList [(min i i', max i i')
                                    | i'<-UArr.toList ngbs ]
                               ) $ Arr.indexed assoc
       lookId i | Option (Just xy) <- indexWeb web i  = xy


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
                , _containingWeb = result
                , _thisNodeId = i
                , _nodeNeighbours = ngbCo
                , _nodeLocalScalarProduct = localScalarProduct ngbH
                , _nodeIsOnBoundary = anyUnopposed (localScalarProduct ngbH) ngbCo
                }, ngbH )
       anyUnopposed rieM ngbCo = (`any`ngbCo) $ \(v,_)
                         -> not $ (`any`ngbCo) $ \(v',_)
                              -> toDualWith rieM v <.>^ v' < 0

localFocusWeb :: WithField ℝ Manifold x
                   => PointsWeb x y -> PointsWeb x ((x,y), [(Needle x, y)])
localFocusWeb (PointsWeb rsc asd) = PointsWeb rsc asd''
 where asd' = Arr.imap (\i (y,n) -> case indexShadeTree rsc i of
                                         Right (_,x) -> ((x,y),n) ) asd
       asd''= Arr.map (\((x,y),n) ->
                       (((x,y), [ ( case x'.-~.x of
                                     Option (Just v) -> v
                                  , y')
                                | j<-UArr.toList (neighbours n)
                                , let ((x',y'),_) = asd' Arr.! j
                                ]), n)
                 ) asd'


data WebLocally x y = LocalWebInfo {
      _thisNodeCoord :: x
    , _thisNodeData :: y
    , _containingWeb :: PointsWeb x (WebLocally x y)
    , _thisNodeId :: WebNodeId
    , _nodeNeighbours :: [(Needle x, y)]
    , _nodeLocalScalarProduct :: Metric x
    , _nodeIsOnBoundary :: Bool
    } deriving (Generic)

instance Hask.Functor (WebLocally x) where
  fmap f (LocalWebInfo co dt wb id ng sp bn)
       = LocalWebInfo co (f dt) (fmap (fmap f) wb) id (map (second f) ng) sp bn
instance WithField ℝ Manifold x => Comonad (WebLocally x) where
  extract = _thisNodeData
  duplicate lweb = unsafeIndexWebData deepened $ _thisNodeId lweb
   where deepened = webLocalInfo $ _containingWeb lweb

data ConvexSet x
    = EmptyConvex
    | ConvexSet {
      convexSetHull :: Shade' x
      -- ^ If @p@ is in all intersectors, it must also be in the hull.
    , convexSetIntersectors :: [Shade' x]
    }

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

iterateFilterDEqn_static :: (WithField ℝ Manifold x, Refinable y)
       => DifferentialEqn x y -> PointsWeb x (Shade' y) -> [PointsWeb x (Shade' y)]
iterateFilterDEqn_static f = map (fmap convexSetHull)
                           . itWhileJust (filterDEqnSolutions_static f)
                           . fmap (`ConvexSet`[])

filterDEqnSolution_static :: (WithField ℝ Manifold x, Refinable y)
       => DifferentialEqn x y -> PointsWeb x (Shade' y) -> Option (PointsWeb x (Shade' y))
filterDEqnSolution_static f = localFocusWeb >>> Hask.traverse `id`
                   \((x,shy), ngbs) -> if null ngbs
                     then pure shy
                     else refineShade' shy
                            =<< filterDEqnSolution_loc f ((x,shy), NE.fromList ngbs)

filterDEqnSolutions_static :: (WithField ℝ Manifold x, Refinable y)
       => DifferentialEqn x y -> PointsWeb x (ConvexSet y) -> Option (PointsWeb x (ConvexSet y))
filterDEqnSolutions_static f = localFocusWeb >>> Hask.traverse `id`
            \((x, shy@(ConvexSet hull _)), ngbs) -> if null ngbs
              then pure shy
              else ((shy<>) . ellipsoid)
                      <$> filterDEqnSolution_loc f
                               ((x,hull), second convexSetHull<$>NE.fromList ngbs)
                     >>= \case EmptyConvex -> empty
                               c           -> pure c

iterateFilterDEqn_adaptive :: (WithField ℝ Manifold x, Refinable y)
       => MetricChoice x      -- ^ Scalar product on the domain, for regularising the web.
       -> DifferentialEqn x y
       -> (x -> Shade' y -> ℝ) -- ^ Badness function for local results.
             -> PointsWeb x (Shade' y) -> [PointsWeb x (Shade' y)]
iterateFilterDEqn_adaptive mf f badness
    = map (fmap (convexSetHull . fst))
    . itWhileJust (filterDEqnSolutions_adaptive mf f badness)
    . fmap (\((x,shy),_) -> (ellipsoid shy, pure (badness x shy)))
    . localFocusWeb

filterDEqnSolutions_adaptive :: ∀ x y . (WithField ℝ Manifold x, Refinable y)
       => MetricChoice x      -- ^ Scalar product on the domain, for regularising the web.
       -> DifferentialEqn x y 
       -> (x -> Shade' y -> ℝ) -- ^ Badness function for local results.
             -> PointsWeb x (ConvexSet y, NonEmpty ℝ)
                        -> Option (PointsWeb x (ConvexSet y, NonEmpty ℝ))
filterDEqnSolutions_adaptive mf f badness
         = fmap (fromWebNodes mf . concat)
             . Hask.traverse localChange . Hask.toList . webLocalInfo
 where localChange :: WebLocally x (ConvexSet y, NonEmpty ℝ)
                             -> Option [(x, (ConvexSet y, NonEmpty ℝ))]
       localChange localInfo@LocalWebInfo{
                         _thisNodeCoord = x
                       , _thisNodeData = (shy@(ConvexSet hull _), badnessHist)
                       , _nodeNeighbours = ngbs
                       }
        | null ngbs  = return [(x, (shy, dupHead badnessHist))]
        | otherwise  = do
               let neighbourHulls = second (convexSetHull . fst) <$> NE.fromList ngbs
               shy' <- ((shy<>) . ellipsoid)
                        <$> filterDEqnSolution_loc f
                               ( (x,hull), neighbourHulls )
               newBadness <- case shy' of
                  EmptyConvex        -> empty
                  ConvexSet hull' _  -> return $ badness x hull'
               let age = length badnessHist
                   (environAge, unfreshness)
                     = (maximum &&& fromIntegral . minimum)
                         $ age : (length . snd . snd <$> ngbs)
                   updated = (x, (shy', NE.cons newBadness badnessHist))
               if isRefinement newBadness
                then return [updated]
                else if newBadness < 1 && age < environAge
                 then return []
                 else do
                   stepStones <- fmap concat . forM ngbs
                                   $ \(vN, (ConvexSet hullN _, badnessHistN)) -> do
                      case badnessHistN of
                        (prevBadnessN:|(_:_))
                            | prevBadnessN < newBadness
                            , prevBadnessN / unfreshness < 1 -> do
                                 let xStep = x .+~^ vN^/2
                                 shyStep <- filterDEqnSolution_loc f
                                            ( (xStep, hull), neighbourHulls )
                                 return [(xStep, ( ellipsoid shyStep
                                                 , pure (badness xStep shyStep) ))]
                        _otherwise -> return []
                   if length stepStones > 0
                    then return $ updated : stepStones
                    else if age < environAge
                          then return []
                          else return [updated]
       
              -- | Decide whether a change in the error bound is significant enough to
              --   be useful for further propagation.
           where isRefinement newBadness = case badnessHist of
                     oldBad :| _ -> newBadness < NE.head badnessHist
                         -- at the moment, accept any change towards more precision.
                              



type MetricChoice x = Shade x -> Metric x


itWhileJust :: (a -> Option a) -> a -> [a]
itWhileJust f x | Option (Just y) <- f x  = x : itWhileJust f y
itWhileJust _ x = [x]

dupHead :: NonEmpty a -> NonEmpty a
dupHead (x:|xs) = x:|x:xs

