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
import Data.VectorSpace (Scalar, (^+^), (^/), (^*), sumV)
import Math.LinearMap.Category ( SimpleSpace, LSpace, DualVector, Norm, Variance
                               , (<.>^), dualNorm, (<$|), (|$|), normSq
                               , dualSpaceWitness, DualSpaceWitness(..) )
    
import qualified Data.Foldable       as Hask
import qualified Data.Traversable as Hask
import Data.List (sortBy)
import qualified Data.List.NonEmpty as NE
import Data.List.NonEmpty (NonEmpty((:|)))
import qualified Data.Map as Map
import qualified Data.Foldable.Constrained as CCt
import Data.Functor.Identity
import Data.Function ((&))
import Data.Ord (comparing)
import Data.List.FastNub (fastNub)
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


traverseInnermostChunks :: ∀ f x y z . Applicative f
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

traverseNodesInEnvi :: ∀ f x y z . Applicative f
           => (NodeInWeb x y -> f (Neighbourhood x z))
             -> PointsWeb x y -> f (PointsWeb x z)
traverseNodesInEnvi f = traverseInnermostChunks fc
 where fc :: WebChunk x y -> f (PointsWeb x z)
       fc (WebChunk (PointsWeb (PlainLeaves lvs)) outlayers)
            = PointsWeb . PlainLeaves <$> Hask.traverse fn (ixedFoci lvs)
        where fn ((i, (x, ngbh)), nearbyLeaves)
               = (x,) <$> f (NodeInWeb (x,ngbh)
                                     $ (PlainLeaves nearbyLeaves, i) : outlayers)

fmapNodesInEnvi :: (NodeInWeb x y -> Neighbourhood x z) -> PointsWeb x y -> PointsWeb x z
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
   = webAroundChunk $ WebChunk (PointsWeb $ OverlappingBranches (nw+nLeaves chunk) ew
                                          (DBranch dir (Hourglass chunk d) :| brs))
                               envi
webAroundChunk (WebChunk (PointsWeb chunk)
                         ((OverlappingBranches nw ew (DBranch dir
                            (Hourglass u (PlainLeaves[])) :| brs), i) : envi))
 | i==nLeaves u
   = webAroundChunk $ WebChunk (PointsWeb $ OverlappingBranches (nw+nLeaves chunk) ew
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
zoomoutWebChunk δi (WebChunk _ e)
    = error $ "Can't zoom out δ"++show δi
       ++" from a chunk with "++show (length e)++" environment layers."

pickNodeInWeb :: PointsWeb x y -> WebNodeId -> NodeInWeb x y
pickNodeInWeb = go [] id
 where go _ _ (PointsWeb w) i
        | i<0 || i>=n  = error
           $ "Trying to pick node #"++show i++" in web with "++show n++" nodes."
        where n = nLeaves w
       go lyrsAcc lMod (PointsWeb (PlainLeaves lvs)) i
        | (preds, node:succs)<-splitAt i lvs
                   = NodeInWeb node $ lMod (PlainLeaves $ preds++succs, i) : lyrsAcc
       go lyrsAcc lMod
            (PointsWeb (OverlappingBranches nw ew (DBranch dir (Hourglass u d):|brs))) i
        | i < nu     = go (lMod (OverlappingBranches (nw-nu) ew
                                      (DBranch dir (Hourglass gap d):|brs), 0) : lyrsAcc)
                          id (PointsWeb u) i
        | i < nu+nd  = go (lMod (OverlappingBranches (nw-nd) ew
                                      (DBranch dir (Hourglass u gap):|brs), nu) : lyrsAcc)
                          id (PointsWeb d) (i-nu)
        | (b:rs)<-brs  = go
                          lyrsAcc
                          (lMod . \(OverlappingBranches nwe ewe brse, ne)
                                   -> ( OverlappingBranches (nwe+nu+nd) ewe
                                         $ NE.cons (DBranch dir (Hourglass u d)) brse
                                      , ne+nu+nd ) )
                          (PointsWeb $ OverlappingBranches (nw-nu-nd) ew (b:|rs))
                          (i-nu-nd)
        where gap = PlainLeaves []
              [nu,nd] = nLeaves<$>[u,d]


webLocalInfo :: ∀ x y . WithField ℝ Manifold x
            => PointsWeb x y -> PointsWeb x (WebLocally x y)
webLocalInfo = fmapNodesInEnvi linkln
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


tweakWebGeometry :: (WithField ℝ Manifold x, SimpleSpace (Needle x))
         => MetricChoice x -> (WebLocally x y -> [WebNodeId])
                        -> PointsWeb x y -> PointsWeb x y
tweakWebGeometry metricf reknit = webLocalInfo >>> fmapNodesInEnvi`id`
         \(NodeInWeb (x₀, (Neighbourhood info _ lm bound)) _)
             -> let lm' = metricf . Shade (inInterior x₀) $ dualNorm lm
                in Neighbourhood (info^.thisNodeData)
                            (UArr.fromList . map (subtract $ info^.thisNodeId)
                                     $ reknit info)
                            lm' bound


bidirectionaliseWebLinks :: ∀ x y . PointsWeb x y -> PointsWeb x y
bidirectionaliseWebLinks web@(PointsWeb wnrsrc) = fmapNodesInEnvi bdse web
 where bdse :: NodeInWeb x y -> Neighbourhood x y
       bdse (NodeInWeb (x, Neighbourhood y outgn lm bound) envis)
                = Neighbourhood y (UArr.fromList . fastNub $ incmn ++ UArr.toList outgn)
                      lm bound
        where i = foldr ((+) . snd) 0 envis
              incmn = case i `Map.lookup` incoming of
                Just o -> subtract i<$>o
                Nothing -> []
       incoming = Map.fromListWith (++) $ Hask.foldl'
                   (\(i,acc) (Neighbourhood _ outgn _ _)
                        -> (i+1, acc . (((,[i]).(+i)<$>UArr.toList outgn)++)) )
                     (0,id) wnrsrc `snd` []



pumpHalfspace :: ∀ v . (SimpleSpace v, Scalar v ~ ℝ)
     => Norm v
     -> v                    -- ^ A vector @v@ for which we want @dv<.>^v ≥ 0@.
     -> (DualVector v, [v])  -- ^ A plane @dv₀@ and some vectors @ws@ with @dv₀<.>^w ≥ 0@,
                             --   which should also fulfill @dv<.>^w ≥ 0@.
     -> Maybe (DualVector v) -- ^ The plane @dv@ fulfilling these properties, if possible.
pumpHalfspace rieM v (prevPlane, ws) = case dualSpaceWitness :: DualSpaceWitness v of
 DualSpaceWitness -> 
  let    ϑs = fmap (\u -> let x = prevPlane<.>^u
                              y = thisPlane<.>^u
                          in atan2 (x-y) (x+y)) $ v:ws
          -- ϑ = 0 means we are mid-between the planes, ϑ > π/2 means we are past
          -- `thisPlane`, ϑ < -π/2 we are past `prevPlane`. In other words, positive ϑ
          -- mean we should mix in more of `prevPlane`, negative more of `thisPlane`.
         [ϑmin, ϑmax] = [minimum, maximum] <*> [ϑs]
         δϑ = ϑmax - ϑmin
         vNudged = v ^+^ sumV (zipWith (^*) ws smallPseudorandSeq)
                    -- Introduce a tiny contribution from the other vectors to avoid
                    -- a degenerate 1D-situation in which @thisPlane ∝ prevPlane@.
         dv = rieM<$|vNudged
         thisPlane = dv ^/ (dv<.>^vNudged)
         cas ϑ = cos $ ϑ - pi/4
  in if δϑ <= pi && minimum (abs<$>ϑs) < pi/2
                 then Just $ let ϑbest = ϑmin + δϑ/2
                             in prevPlane^*cas ϑbest ^+^ thisPlane^*cas (-ϑbest)
                 else Nothing

smallPseudorandSeq :: [ℝ]
smallPseudorandSeq = (*2^^(-45)) . fromIntegral <$> lcg 293633
 where lcg x = x : lcg ((a*x)`mod`m)
       m = 2^31 - 1
       a = 963345    :: Int  -- revised Park-Miller

data LinkingBadness r = LinkingBadness
    { gatherDirectionsBadness :: !r -- ^ Prefer picking neighbours at right angles
                                    --   to the currently-explored-boundary. This
                                    --   is needed while we still have to link to
                                    --   points in different spatial directions.
    , closeSystemBadness :: !r      -- ^ Prefer points directly opposed to the
                                    --   current boundary. This is useful when the
                                    --   system of directions is already complete
                                    --   and we want a nicely symmetric “ball” of
                                    --   neighbours around each point.
    } deriving (Functor)

linkingUndesirability :: ℝ -- ^ Absolute-square distance (euclidean norm squared)
                      -> ℝ -- ^ Directional distance (distance from wall containing
                           --   all already known neighbours)
                      -> LinkingBadness ℝ
                           -- ^ “Badness” of this point as the next neighbour to link to.
                           --   In gatherDirections mode this is large if
                           --   the point is far away, but also if it is
                           --   right normal to the wall. The reason we punish this is that
                           --   adding two points directly opposed to each other would lead
                           --   to an ill-defined wall orientation, i.e. wrong normals
                           --   on the web boundary.
linkingUndesirability distSq wallDist = LinkingBadness
   { gatherDirectionsBadness = distSq^2 / max 0 (distSq-wallDist^2)
   , closeSystemBadness = distSq - wallDist^2/2
   }


bestNeighbours :: ∀ i v . (SimpleSpace v, Scalar v ~ ℝ)
                => Norm v -> [v] -> [(i,v)] -> ([i], Maybe (DualVector v))
bestNeighbours lm' aprioriN = first (map fst) . bestNeighbours' lm' aprioriN

bestNeighbours' :: ∀ i v . (SimpleSpace v, Scalar v ~ ℝ)
                => Norm v -> [v] -> [(i,v)] -> ([(i,v)], Maybe (DualVector v))
bestNeighbours' lm' aprioriN ((c₀i,c₀δx) : candidates)
  = case dualSpaceWitness :: DualSpaceWitness v of
     DualSpaceWitness ->
       let wall₀ = w₀ ^/ (lm|$|w₀) -- sqrt (w₀<.>^c₀δx)
            where w₀ = lm'<$|c₀δx
           lm = dualNorm lm' :: Variance v
       in first ((c₀i,c₀δx):) $ gatherGoodNeighbours lm' lm wall₀ aprioriN [c₀δx] candidates

gatherGoodNeighbours :: ∀ i v . (SimpleSpace v, Scalar v ~ ℝ)
            => Norm v -> Variance v
               -> DualVector v -> [v] -> [v] -> [(i, v)] -> ([(i,v)], Maybe (DualVector v))
gatherGoodNeighbours lm' lm wall aprioriN prev cs
 = case dualSpaceWitness :: DualSpaceWitness v of
    DualSpaceWitness ->
     case sortBy (comparing $ gatherDirectionsBadness.fst)
                                  [ ((/βmin)
                                      <$> linkingUndesirability (normSq lm' δx) wallDist
                                    , (i,δx) )
                                  | (i,δx) <- cs
                                  , let wallDist = - wall<.>^δx
                                  , wallDist >= 0
                                  , let βmin = minimum
                                          [ 1 - ((lm'<$|δx)<.>^δxo)
                                                  / sqrt (normSq lm' δx*normSq lm' δxo)
                                            -- β behaves basically like ϑ², where ϑ is
                                            -- the angle between two neighbour candidates.
                                          | δxo <- prev ]
                                  , βmin > 0
                                  ] of
                  [] -> ([], Just wall)
                  (_,(i,δx)) : cs'
                   | Just wall' <- pumpHalfspace lm' δx (wall,aprioriN++prev)
                          -> first ((i,δx):)
                       $ gatherGoodNeighbours lm' lm (wall'^/(lm|$|wall'))
                               aprioriN (δx:prev) (snd<$>cs')
                  cs' -> let closeSys ((_,(i,δx)):_)
                               | Nothing <- pumpHalfspace lm' δx (wall,aprioriN++prev)
                                   = ([(i,δx)], Nothing)
                             closeSys (_:cs'') = closeSys cs''
                         in closeSys $ sortBy (comparing $ closeSystemBadness.fst) cs'

