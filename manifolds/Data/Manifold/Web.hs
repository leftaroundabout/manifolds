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
              -- * Uncertain functions
            , differentiateUncertainWebFunction, differentiate²UncertainWebFunction
              -- * Differential equations
              -- ** Fixed resolution
            , iterateFilterDEqn_static
              -- ** Automatic resolution
            , filterDEqnSolutions_adaptive, iterateFilterDEqn_adaptive
              -- ** Configuration
            , InconsistencyStrategy(..)
            , InformationMergeStrategy(..)
            , naïve, inconsistencyAware, indicateInconsistencies
            , PropagationInconsistency(..)
              -- * Misc
            , ConvexSet(..), ellipsoid, ellipsoidSet, coerceWebDomain
            , rescanPDEOnWeb, rescanPDELocally, webOnions
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
import Data.Embedding
    
import qualified Prelude as Hask hiding(foldl, sum, sequence)
import qualified Control.Applicative as Hask
import qualified Control.Monad       as Hask hiding(forM_, sequence)
import Control.Monad.ST (runST)
import Data.STRef (newSTRef, modifySTRef, readSTRef)
import Control.Monad.Trans.State
import Control.Monad.Trans.List
import Control.Monad.Trans.Except
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


type WebNodeId = Int

data Neighbourhood x = Neighbourhood {
     _neighbours :: UArr.Vector WebNodeId
   , _localScalarProduct :: Metric x
   }
  deriving (Generic)
makeLenses ''Neighbourhood

deriving instance ( WithField ℝ PseudoAffine x
                  , SimpleSpace (Needle x), Show (Needle' x) )
             => Show (Neighbourhood x)

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
fromWebNodes = case boundarylessWitness :: BoundarylessWitness x of
   BoundarylessWitness ->
       \mf -> fromShaded mf . fromLeafPoints . map (uncurry WithAny . swap)

fromTopWebNodes :: ∀ x y . (WithField ℝ Manifold x, SimpleSpace (Needle x))
                    => (MetricChoice x) -> [((x,[Int+Needle x]),y)] -> PointsWeb x y
fromTopWebNodes = case boundarylessWitness :: BoundarylessWitness x of
   BoundarylessWitness ->
       \mf -> fromTopShaded mf . fromLeafPoints
                   . map (uncurry WithAny . swap . regroup')

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
                       . joinShaded . seekPotentialNeighbours

toShaded :: WithField ℝ PseudoAffine x => PointsWeb x y -> (x`Shaded`y)
toShaded (PointsWeb shd asd) = zipTreeWithList shd $ Arr.toList (fst<$>asd)

fromTopShaded :: ∀ x y . (WithField ℝ Manifold x, SimpleSpace (Needle x))
     => (MetricChoice x)
     -> (x`Shaded`([Int+Needle x], y))
                      -- ^ Source tree, with topology information
                      --   (IDs of neighbour-candidates, or needles pointing to them)
     -> PointsWeb x y
fromTopShaded metricf shd = PointsWeb shd' assocData 
 where shd' = stripShadedUntopological shd
       assocData = Hask.foldMap locMesh $ allTwigs shd
       
       locMesh :: (Int, ShadeTree (x`WithAny`([Int+Needle x], y)))
                   -> Arr.Vector (y, Neighbourhood x)
       locMesh (i₀, locT) = Arr.map findNeighbours $ Arr.fromList locLeaves
        where locLeaves :: [ (Int, x`WithAny`([Int+Needle x], y)) ]
              locLeaves = map (first (+i₀)) . zip [0..] $ onlyLeaves locT
              findNeighbours :: (Int, x`WithAny`([Int+Needle x], y)) -> (y, Neighbourhood x)
              findNeighbours (i, WithAny (vns,y) x)
                         = (y, cullNeighbours locRieM
                                 (i, WithAny([ (i,v)
                                             | (i,WithAny _ xN) <- locLeaves
                                             , Just v <- [xN.-~.x] ]
                                                ++ aprioriNgbs)
                                             x))
               where aprioriNgbs :: [(Int, Needle x)]
                     aprioriNgbs = catMaybes
                                    [ (second $ const v) <$>
                                          positionIndex (pure locRieM) shd' xN
                                    | Right v <- vns
                                    , let xN = xi.+~^v :: x ]
                                 ++ [ (i,v) | Left i <- vns
                                            , Right (_,xN) <- [indexShadeTree shd' i]
                                            , Just v <- [xN.-~.x] ]
                     Just xi = toInterior x
              
              locRieM :: Metric x
              locRieM = case pointsCovers . catMaybes . map (toInterior . _topological)
                                  $ onlyLeaves locT of
                          [sh₀] -> metricf sh₀

cullNeighbours :: ∀ x . (WithField ℝ PseudoAffine x, SimpleSpace (Needle x))
      => Metric x -> (Int, x`WithAny`[(Int,Needle x)]) -> Neighbourhood x
cullNeighbours locRieM (i, WithAny vns x)
           = Neighbourhood (UArr.fromList . sort $ _nvectId<$>execState seek mempty)
                           locRieM
 where seek :: State [NeighbourhoodVector x] ()
       seek = do
          Hask.forM_ ( fastNubBy (comparing fst) $ vns )
                    $ \(iNgb, v) ->
             when (iNgb/=i) `id`do
                oldNgbs <- get
                let w₀ = locRieM<$|v
                    l = sqrt $ w₀<.>^v
                    onOverlap = sum [ o^2 | nw<-oldNgbs
                                          , let o = (nw^.nvectNormal)<.>^v
                                          , o > 0 ]
                when (l > onOverlap) `id`do
                   let w = w₀^/sqrt l^3
                       newCandidates
                          = NeighbourhoodVector iNgb v w l 0
                          : [ ongb & otherNeighboursOverlap .~ 0
                            | ongb <- oldNgbs
                            , let o = w<.>^(ongb^.theNVect)
                                  newOverlap = (if o > 0 then (o^2+) else id)
                                                $ ongb^.otherNeighboursOverlap
                            , newOverlap < ongb^.nvectLength ]
                   put $ recalcOverlaps newCandidates
       recalcOverlaps [] = []
       recalcOverlaps (ngb:ngbs)
             = (ngb & otherNeighboursOverlap +~ furtherOvl)
             : recalcOverlaps [ ngb' & otherNeighboursOverlap +~ max 0 o ^ 2
                              | ngb' <- ngbs
                              , let o = (ngb^.nvectNormal)<.>^(ngb'^.theNVect) ]
        where furtherOvl = sum [ o^2 | nw<-ngbs
                                     , let o = (nw^.nvectNormal)<.>^(ngb^.theNVect)
                                     , o > 0 ]
              

-- | Re-calculate the links in a web, so as to give each point a satisfyingly
--   “complete-spanning” environment.
smoothenWebTopology :: (WithField ℝ Manifold x, SimpleSpace (Needle x))
             => MetricChoice x -> PointsWeb x y -> PointsWeb x y
smoothenWebTopology mc = swt
 where swt (PointsWeb shd net) = PointsWeb shd . go allNodes Set.empty
                                                   . fst $ makeIndexLinksSymmetric net
        where allNodes = Set.fromList . Arr.toList $ fst <$> Arr.indexed net
              go activeSet pastLinks asd
                 | all (isNothing.fst) refined
                 , Set.null (Set.difference symmetryTouched pastLinks)
                               = Arr.imap finalise asd'
                 | otherwise   = go (Set.fromList
                                         [ j | (Just i, (_,Neighbourhood ngbs' _))
                                               <-refined
                                         , j <- i : UArr.toList ngbs' ]
                                      `Set.union` (Set.map fst symmetryTouched))
                                    updtLinks
                                    asd'
               where refined = reseek<$>Set.toList activeSet
                      where reseek i = ( guard isNews >> pure i
                                       , (y, Neighbourhood newNgbs locRieM) )
                             where isNews = newNgbs /= oldNgbs
                                             && or [ not $ Set.member (i,j) pastLinks
                                                   | j <- UArr.toList newNgbs ]
                                   (y,Neighbourhood oldNgbs locRieM) = asd Arr.! i
                                   nextNeighbours = fastNub
                                     $ UArr.toList oldNgbs
                                     ++ (UArr.toList._neighbours.snd.(asd Arr.!)
                                             =<< UArr.toList oldNgbs)
                                   x = xLookup Arr.! i
                                   Neighbourhood newNgbs _
                                     = cullNeighbours locRieM
                                        ( i, WithAny [ (j,v)
                                                     | j <- nextNeighbours
                                                     , Just v
                                                         <- [x .-~. xLookup Arr.! j] ]
                                                     x )
                     (asd', symmetryTouched) = makeIndexLinksSymmetric
                              $ asd Arr.// [(i,n) | (Just i,n) <- refined]
                     updtLinks = Set.unions
                                   [ pastLinks
                                   , Set.fromList
                                      [ (i,j) | (Just i,(_,Neighbourhood n _)) <- refined
                                              , j<-UArr.toList n ]
                                   , symmetryTouched ]
              finalise i (y, Neighbourhood n em)
                  = (y, cullNeighbours em (i, WithAny [ (j,v)
                                                      | j<-UArr.toList n
                                                      , let xN = xLookup Arr.! j
                                                      , Just v <- [xN.-~.x] ]
                                                      x ))
               where x = xLookup Arr.! i
              xLookup = Arr.fromList $ onlyLeaves shd

makeIndexLinksSymmetric
       :: Arr.Vector (y, Neighbourhood x)
       -> (Arr.Vector (y, Neighbourhood x), Set.Set (WebNodeId,WebNodeId))
makeIndexLinksSymmetric orig = runST (do
    result <- Arr.thaw orig
    touched <- newSTRef $ Set.empty
    (`Arr.imapM_`orig) $ \i (_,Neighbourhood ngbs _) -> do
       UArr.forM_ ngbs $ \j -> do
          (yn, Neighbourhood nngbs lsc) <- MArr.read result j
          when (not $ i`UArr.elem`nngbs) `id`do
             MArr.write result j (yn, Neighbourhood (UArr.snoc nngbs i) lsc)
             modifySTRef touched $ Set.insert (j,i)
    final <- Arr.freeze result
    allTouched <- readSTRef touched
    return (final, allTouched)
  )

indexWeb :: (WithField ℝ Manifold x, SimpleSpace (Needle x))
                => PointsWeb x y -> WebNodeId -> Maybe (x,y)
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
       lookId i | Just xy <- indexWeb web i  = xy


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
 where edgs = webEdges web
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
                                          Just δx = _thisNodeCoord neighbour.-~.x
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
                                     Just v -> v
                                  , y')
                                | j<-UArr.toList (n^.neighbours)
                                , let ((x',y'),_) = asd' Arr.! j
                                ]), n)
                 ) asd'

localOnion :: ∀ x y . WithField ℝ Manifold x
            => WebLocally x y -> [[WebLocally x y]]
localOnion origin = go Map.empty $ Map.singleton (origin^.thisNodeId) (1, origin)
 where go previous next
        | Map.null next = []
        | otherwise  = ( snd <$> sortBy (comparing $ negate . fst)
                                                 (Hask.toList next) )
                     : go (Map.union previous next)
                          (Map.fromListWith (\(n,ninfo) (n',_) -> (n+n'::Int, ninfo))
                                [ (nnid,(1,nneigh))
                                | (nid,(_,ninfo))<-Map.toList next
                                , (nnid,(_,nneigh))<-ninfo^.nodeNeighbours
                                , Map.notMember nnid previous ])

webOnions :: ∀ x y . WithField ℝ Manifold x
            => PointsWeb x y -> PointsWeb x [[(x,y)]]
webOnions = localFmapWeb (map (map $ _thisNodeCoord&&&_thisNodeData) . localOnion)

nearestNeighbour :: (WithField ℝ Manifold x, SimpleSpace (Needle x))
                      => PointsWeb x y -> x -> Maybe (x,y)
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
                                 Just v = xNgb.-~.x
                           ]
              Just vEst = xEst.-~.x



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

traverseWebWithStrategy :: ( WithField ℝ Manifold x, Hask.Applicative m )
               => InconsistencyStrategy m x y -> (WebLocally x y -> Maybe y)
                     -> PointsWeb x y -> m (PointsWeb x y)
traverseWebWithStrategy strat f = webLocalInfo
               >>> traverse (\info -> handleInconsistency strat
                                       (info^.thisNodeData) (f info))

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

differentiateUncertainWebFunction :: ∀ x y
   . ( WithField ℝ Manifold x, SimpleSpace (Needle x)
     , WithField ℝ Manifold y, SimpleSpace (Needle y), Refinable y )
            => PointsWeb x (Shade' y)
             -> PointsWeb x (Shade' (LocalLinear x y))
differentiateUncertainWebFunction = localFmapWeb differentiateUncertainWebLocally

differentiate²UncertainWebLocally :: ∀ x y
   . ( WithField ℝ Manifold x, FlatSpace (Needle x)
     , WithField ℝ Refinable y, FlatSpace (Needle y) )
            => WebLocally x (Shade' y)
             -> Shade' (Needle x ⊗〃+> Needle y)
differentiate²UncertainWebLocally = d²uwl
                ( pseudoAffineWitness :: PseudoAffineWitness x
                , pseudoAffineWitness :: PseudoAffineWitness y )
 where d²uwl ( PseudoAffineWitness (SemimanifoldWitness _)
             , PseudoAffineWitness (SemimanifoldWitness _) ) info
          = case estimateLocalHessian $
                          (\ngb -> case (ngb^.thisNodeCoord .-~. info^.thisNodeCoord) of
                             Just δx -> (Local δx :: Local x, ngb^.thisNodeData) )
                          <$> info :| envi
                          of
               QuadraticModel _ h e -> Shade' (((^*2) . snd . snd) (evalQuadratic h zeroV))
                                         (transformNorm (lfun $ ($ xVol)) e)
        where xVol :: SymmetricTensor ℝ (Needle x)
              xVol = squareVs $ fst.snd<$>info^.nodeNeighbours
              _:directEnvi:remoteEnvi = localOnion info
              envi = directEnvi ++ take (nMinData - length directEnvi) (concat remoteEnvi)
       nMinData = 1 + regular_neighboursCount
                         (subbasisDimension (entireBasis :: SubBasis (Needle x)))

-- | Heuristic formula, matches the number of neighbours each vertex has in a one-
--   and two-dimensional count
regular_neighboursCount :: Int -> Int
regular_neighboursCount d
 | d>0        = (regular_neighboursCount (d-1) + 1)*2
 | otherwise  = 0


differentiate²UncertainWebFunction :: ∀ x y
   . ( WithField ℝ Manifold x, FlatSpace (Needle x)
     , WithField ℝ Refinable y, FlatSpace (Needle y) )
         => PointsWeb x (Shade' y)
          -> PointsWeb x (Shade' (Needle x ⊗〃+> Needle y)) 
differentiate²UncertainWebFunction = localFmapWeb differentiate²UncertainWebLocally

rescanPDELocally :: ∀ x y ð .
     ( WithField ℝ Manifold x, SimpleSpace (Needle x)
     , WithField ℝ Refinable y, SimpleSpace (Needle y) )
         => DifferentialEqn x ð y -> WebLocally x (Shade' y)
                                -> (Maybe (Shade' y), Maybe (Shade' ð))
rescanPDELocally = case ( dualSpaceWitness :: DualNeedleWitness x
                        , dualSpaceWitness :: DualNeedleWitness y
                        , boundarylessWitness :: BoundarylessWitness x
                        , pseudoAffineWitness :: PseudoAffineWitness y ) of
   ( DualSpaceWitness,DualSpaceWitness,BoundarylessWitness
    , PseudoAffineWitness (SemimanifoldWitness BoundarylessWitness) )
     -> \f info -> let xc = info^.thisNodeCoord
                       yc = info^.thisNodeData.shadeCtr
                   in case f $ coverAllAround (xc, yc)
                                     [ (δx, (ngb^.thisNodeData.shadeCtr.-~!yc) ^+^ v)
                                     | (_,(δx,ngb))<-info^.nodeNeighbours
                                     , v <- normSpanningSystem'
                                              (ngb^.thisNodeData.shadeNarrowness)] of
                        LocalDifferentialEqn _ rescan
                            -> rescan (differentiateUncertainWebLocally info)
                                      (info^.thisNodeData)

rescanPDEOnWeb :: ( WithField ℝ Manifold x, SimpleSpace (Needle x)
                  , WithField ℝ Refinable y, SimpleSpace (Needle y)
                  , Hask.Applicative m )
                => InconsistencyStrategy m x (Shade' y)
                  -> DifferentialEqn x ð y -> PointsWeb x (Shade' y)
                                   -> m (PointsWeb x (Shade' y))
rescanPDEOnWeb strat deq = traverseWebWithStrategy strat $ fst . rescanPDELocally deq

toGraph :: (WithField ℝ Manifold x, SimpleSpace (Needle x))
              => PointsWeb x y -> (Graph, Vertex -> (x, y))
toGraph wb = second (>>> \(i,_,_) -> case indexWeb wb i of {Just xy -> xy})
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

maybeAlt :: Hask.Alternative f => Maybe a -> f a
maybeAlt (Just x) = pure x
maybeAlt Nothing = Hask.empty

data InconsistencyStrategy m x y where
    AbortOnInconsistency :: InconsistencyStrategy Maybe x y
    IgnoreInconsistencies :: InconsistencyStrategy Identity x y
    HighlightInconsistencies :: y -> InconsistencyStrategy Identity x y
deriving instance Hask.Functor (InconsistencyStrategy m x)


iterateFilterDEqn_static :: ( WithField ℝ Manifold x, SimpleSpace (Needle x)
                            , Refinable y, Geodesic (Interior y)
                            , WithField ℝ AffineManifold ð, Geodesic ð
                            , SimpleSpace (Needle ð)
                            , Hask.MonadPlus m )
       => InformationMergeStrategy [] m (x,Shade' y) iy
           -> Embedding (->) (Shade' y) iy
           -> DifferentialEqn x ð y
                 -> PointsWeb x (Shade' y) -> Cofree m (PointsWeb x (Shade' y))
iterateFilterDEqn_static strategy shading f
                           = fmap (fmap (shading >-$))
                           . coiter (filterDEqnSolutions_static strategy shading f)
                           . fmap (shading $->)


filterDEqnSolutions_static :: ∀ x y iy ð m .
                              ( WithField ℝ Manifold x, SimpleSpace (Needle x)
                              , Refinable y, Geodesic (Interior y)
                              , WithField ℝ AffineManifold ð, Geodesic ð
                              , SimpleSpace (Needle ð)
                              , Hask.MonadPlus m )
       => InformationMergeStrategy [] m  (x,Shade' y) iy -> Embedding (->) (Shade' y) iy
          -> DifferentialEqn x ð y -> PointsWeb x iy -> m (PointsWeb x iy)
filterDEqnSolutions_static strategy shading f
       = webLocalInfo
           >>> fmap (id &&& rescanPDELocally f . fmap (shading>-$))
           >>> localFocusWeb >>> Hask.traverse ( \((_,(me,updShy)), ngbs)
          -> let oldValue = me^.thisNodeData :: iy
             in  case updShy of
              (Just shy, Just shð) -> case ngbs of
                  []  -> pure oldValue
                  _:_ | BoundarylessWitness <- (boundarylessWitness::BoundarylessWitness x)
                    -> maybeAlt
                          ( sequenceA [ fzip sj
                                >>= \ngbShyð -> (ngbInfo^.thisNodeCoord,)<$>
                                     propagateDEqnSolution_loc
                                       f (LocalDataPropPlan
                                             (ngbInfo^.thisNodeCoord)
                                             (negateV δx)
                                             ngbShyð
                                             (shy, shð)
                                             (fmap (second ((shading>-$) . _thisNodeData)
                                                    . snd) $ ngbInfo^.nodeNeighbours)
                                          )
                                  | (δx, (ngbInfo,sj)) <- ngbs
                                  ] )
                            >>= mergeInformation strategy (shading$->shy)
              _ -> mergeInformation strategy oldValue empty
        )

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
        . ( WithField ℝ Manifold x, SimpleSpace (Needle x)
          , WithField ℝ AffineManifold y, Refinable y, Geodesic y
          , WithField ℝ AffineManifold ð, Geodesic ð, SimpleSpace (Needle ð)
          , badness ~ ℝ, Hask.Monad m )
       => MetricChoice x      -- ^ Scalar product on the domain, for regularising the web.
       -> InconsistencyStrategy m x (Shade' y)
       -> DifferentialEqn x ð y
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
               = traverse addPropagation $ webLocalInfo oldState
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
                                                                  .solverNodeStatus
                                           , undefined)
                                           (thisShy, undefined)
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
                                                        n^.thisNodeData.solverNodeStatus
                                                      , undefined)
                                                      (aprioriInterpolate, undefined)
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
     :: ( WithField ℝ Manifold x, SimpleSpace (Needle x)
        , WithField ℝ AffineManifold y, Refinable y, Geodesic y, Hask.Monad m
        , WithField ℝ AffineManifold ð, Geodesic ð, SimpleSpace (Needle ð) )
       => MetricChoice x      -- ^ Scalar product on the domain, for regularising the web.
       -> InconsistencyStrategy m x (Shade' y)
       -> DifferentialEqn x ð y
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




