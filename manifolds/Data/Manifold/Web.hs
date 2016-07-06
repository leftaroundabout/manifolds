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
import Data.Fixed (mod')

import Data.Manifold.Types
import Data.Manifold.Types.Primitive (empty, (^))
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
import Lens.Micro ((%~))
import Lens.Micro.TH

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



type MetricChoice x = Shade x -> Metric x


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
makeLenses ''WebLocally

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



itWhileJust :: (a -> Option a) -> a -> [a]
itWhileJust f x | Option (Just y) <- f x  = x : itWhileJust f y
itWhileJust _ x = [x]

dupHead :: NonEmpty a -> NonEmpty a
dupHead (x:|xs) = x:|x:xs


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


data SolverNodeState y = SolverNodeInfo {
      _solverNodeStatus :: ConvexSet y
    , _solverNodeBadness :: ℝ
    , _solverNodeAge :: Int
    }
makeLenses ''SolverNodeState

filterDEqnSolutions_adaptive :: ∀ x y . (WithField ℝ Manifold x, Refinable y)
       => MetricChoice x      -- ^ Scalar product on the domain, for regularising the web.
       -> DifferentialEqn x y 
       -> (x -> Shade' y -> ℝ) -- ^ Badness function for local results.
             -> PointsWeb x (SolverNodeState y)
                        -> Option (PointsWeb x (SolverNodeState y))
filterDEqnSolutions_adaptive mf f badness' oldState
         = fmap (fromWebNodes mf . concat) $ Hask.traverse localChange preproc'd
 where preproc'd = Hask.toList $ webLocalInfo oldState
       smallBadnessGradient, largeBadnessGradient :: ℝ
       (smallBadnessGradient, largeBadnessGradient)
           = ( badnessGradRated!!(n`div`4), badnessGradRated!!(n*3`div`4) )
        where n = length badnessGradRated
              badnessGradRated = sort [ bad / ngBad
                                      | LocalWebInfo {
                                            _thisNodeData=SolverNodeInfo _ bad _
                                          , _nodeNeighbours=ngbs
                                          } <- preproc'd
                                      , (_, SolverNodeInfo _ ngBad _) <- ngbs
                                      , ngBad<bad ]
       localChange :: WebLocally x (SolverNodeState y)
                             -> Option [(x, (SolverNodeState y))]
       localChange localInfo@LocalWebInfo{
                         _thisNodeCoord = x
                       , _thisNodeData = SolverNodeInfo
                                           shy@(ConvexSet hull _) prevBadness age
                       , _nodeNeighbours = ngbs
                       }
        | null ngbs  = return [(x, SolverNodeInfo shy prevBadness (age+1))]
        | otherwise  = do
               let neighbourHulls = second (convexSetHull . _solverNodeStatus)
                                       <$> NE.fromList ngbs
                   (environAge, unfreshness)
                      = maximum&&&minimum $ age : (_solverNodeAge . snd <$> ngbs)
               case find (\(_, SolverNodeInfo _ prevBadnessN _)
                               -> prevBadnessN / prevBadness > smallBadnessGradient)
                              ngbs of
                 Nothing | age < environAge   -- point is an obsolete step-stone;
                   -> return []               -- do not further use it.
                 _otherwise -> do
                   shy' <- ((shy<>) . ellipsoid)
                            <$> filterDEqnSolution_loc f
                                   ( (x,hull), neighbourHulls )
                   newBadness <- case shy' of
                      EmptyConvex        -> empty
                      ConvexSet hull' _  -> return $ badness x hull'
                   let updated = (x, SolverNodeInfo shy' newBadness (age+1))
                   stepStones <-
                     if unfreshness < 3
                      then return []
                      else fmap concat . forM ngbs
                                   $ \(vN, SolverNodeInfo (ConvexSet hullN _)
                                                          prevBadnessN ageN   ) -> do
                       case ageN of
                        _  | ageN > 0
                           , badnessGrad <- prevBadnessN / prevBadness
                           , badnessGrad > largeBadnessGradient -> do
                                 let stepV = vN^/2
                                     xStep = x .+~^ stepV
                                 shyStep <- filterDEqnSolution_loc f
                                            ( (xStep, hull)
                                            , NE.cons (negateV stepV, hull)
                                                $ fmap (\(vN',hullN')
                                                         -> (vN'^-^stepV, hullN') )
                                                    neighbourHulls )
                                 return [(xStep, SolverNodeInfo (ellipsoid shyStep)
                                                 (badness xStep shyStep) 1 )]
                        _otherwise -> return []
                   return $ updated : stepStones
       
       totalAge = maximum $ _solverNodeAge . _thisNodeData <$> preproc'd
       errTgtModulation = (1-) . (`mod'`1) . negate . sqrt $ fromIntegral totalAge
       badness x = badness' x . (shadeNarrowness %~ (^* errTgtModulation))
                              


iterateFilterDEqn_adaptive :: (WithField ℝ Manifold x, Refinable y)
       => MetricChoice x      -- ^ Scalar product on the domain, for regularising the web.
       -> DifferentialEqn x y
       -> (x -> Shade' y -> ℝ) -- ^ Badness function for local results.
             -> PointsWeb x (Shade' y) -> [PointsWeb x (Shade' y)]
iterateFilterDEqn_adaptive mf f badness
    = map (fmap (convexSetHull . _solverNodeStatus))
    . itWhileJust (filterDEqnSolutions_adaptive mf f badness)
    . fmap (\((x,shy),_) -> SolverNodeInfo (ellipsoid shy)
                                           (badness x shy)
                                           1
           )
    . localFocusWeb




