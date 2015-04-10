-- |
-- Module      : Data.Manifold.TreeCover
-- Copyright   : (c) Justus Sagemüller 2015
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
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE ParallelListComp           #-}
{-# LANGUAGE UnicodeSyntax              #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE PatternGuards              #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE DataKinds                  #-}


module Data.Manifold.TreeCover (
       -- * Shades 
         Shade, shadeCtr, shadeExpanse, fullShade, pointsShades
       -- * Shade trees
       , ShadeTree(..), fromLeafPoints
       -- ** Combinators
       , separateOverlap
       -- * Simple view helpers
       , onlyNodes, onlyLeaves
       -- ** Auxiliary types
       , SimpleTree, Trees, NonEmptyTree, GenericTree(..)
    ) where


import Data.List hiding (filter)
import Data.Maybe
import qualified Data.Map as Map
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE
import Data.Semigroup
import Data.Ord (comparing)
import Control.DeepSeq

import Data.VectorSpace
import Data.LinearMap
import Data.LinearMap.HerMetric
import Data.AffineSpace
import Data.Basis
import Data.Complex hiding (magnitude)
import Data.Void
import Data.Tagged

import Data.Manifold.Types
import Data.Manifold.Types.Primitive ((^))
import Data.Manifold.PseudoAffine

import qualified Prelude as Hask hiding(foldl)
import qualified Control.Applicative as Hask
import qualified Control.Monad       as Hask
import qualified Data.Foldable       as Hask

import Control.Category.Constrained.Prelude hiding ((^))
import Control.Arrow.Constrained
import Control.Monad.Constrained
import Data.Foldable.Constrained

import GHC.TypeLits
import GHC.Generics (Generic)


-- | Possibly / Partially / asymPtotically singular metric.
data PSM x = PSM {
       psmExpanse :: !(HerMetric' (Needle x))
     , relevantEigenspan :: ![DualSpace (Needle x)]
     }
       

-- | A 'Shade' is a very crude description of a region within a manifold. It
--   can be interpreted as either an ellipsoid shape, or as the Gaussian peak
--   of a normal distribution (use <http://hackage.haskell.org/package/manifold-random>
--   for actually sampling from that distribution).
-- 
--   For a /precise/ description of an arbitrarily-shaped connected subset of a manifold,
--   there is 'Region', whose implementation is vastly more complex.
data Shade x = Shade { shadeCtr :: !x
                     , shadeExpanse :: !(HerMetric' (Needle x)) }

instance (AffineManifold x) => Semimanifold (Shade x) where
  type Needle (Shade x) = Diff x
  Shade c e .+~^ v = Shade (c.+^v) e
  Shade c e .-~^ v = Shade (c.-^v) e

fullShade :: WithField ℝ Manifold x => x -> HerMetric' (Needle x) -> Shade x
fullShade ctr expa = Shade ctr expa

subshadeId' :: WithField ℝ Manifold x
                   => x -> [DualSpace (Needle x)] -> x -> (Int, HourglassBulb)
subshadeId' c expvs x = case x .-~. c of
    Option (Just v) -> let (iu,vl) = maximumBy (comparing $ abs . snd)
                                      $ zip [0..] (map (v <.>^) expvs)
                       in (iu, if vl>0 then UpperBulb else LowerBulb)
    _ -> (-1, error "Trying to obtain the subshadeId of a point not actually included in the shade.")

subshadeId :: WithField ℝ Manifold x => Shade x -> x -> (Int, HourglassBulb)
subshadeId (Shade c expa) = subshadeId' c $ eigenCoSpan expa
                 


-- | Attempt to find a 'Shade' that &#x201c;covers&#x201d; the given points.
--   At least in an affine space (and thus locally in any manifold), this can be used to
--   estimate the parameters of a normal distribution from which some points were
--   sampled.
-- 
--   For /nonconnected/ manifolds it will be necessary to yield separate shades
--   for each connected component. And for an empty input list, there is no shade!
--   Hence the list result.
pointsShades :: WithField ℝ Manifold x => [x] -> [Shade x]
pointsShades = map snd . pointsShades' zeroV

pseudoECM :: WithField ℝ Manifold x => NonEmpty x -> (x, ([x],[x]))
pseudoECM (p₀ NE.:| psr) = foldl' ( \(acc, (rb,nr)) (i,p)
                                  -> case p.-~.acc of 
                                      Option (Just δ) -> (acc .+~^ δ^/i, (p:rb, nr))
                                      _ -> (acc, (rb, p:nr)) )
                             (p₀, mempty)
                             ( zip [1..] $ p₀:psr )

pointsShades' :: WithField ℝ Manifold x => HerMetric' (Needle x) -> [x] -> [([x], Shade x)]
pointsShades' _ [] = []
pointsShades' minExt ps = case expa of 
                           Option (Just e) -> (ps, fullShade ctr e)
                                              : pointsShades' minExt unreachable
                           _ -> pointsShades' minExt inc'd
                                  ++ pointsShades' minExt unreachable
 where (ctr,(inc'd,unreachable)) = pseudoECM $ NE.fromList ps
       expa = ( (^+^minExt) . (^/ fromIntegral(length ps)) . sumV . map projector' )
              <$> mapM (.-~.ctr) ps
       

minusLogOcclusion :: (PseudoAffine x, HasMetric (Needle x)
             , s ~ (Scalar (Needle x)), RealDimension s )
                => Shade x -> x -> s
minusLogOcclusion (Shade p₀ δ) = occ
 where occ p = case p .-~. p₀ of
         Option(Just vd) -> metricSq δinv vd
         _               -> 1/0
       δinv = recipMetric δ
  
-- | Check the statistical likelyhood of a point being within a shade.
occlusion :: (PseudoAffine x, HasMetric (Needle x)
             , s ~ (Scalar (Needle x)), RealDimension s )
                => Shade x -> x -> s
occlusion (Shade p₀ δ) = occ
 where occ p = case p .-~. p₀ of
         Option(Just vd) -> exp . negate $ metricSq δinv vd
         _               -> zeroV
       δinv = recipMetric δ



-- | Hourglass as the geometric shape (two opposing ~conical volumes, sharing
--   only a single point in the middle); has nothing to do with time.
data Hourglass s = Hourglass { upperBulb, lowerBulb :: !s }
            deriving (Generic, Hask.Functor, Hask.Foldable)
instance (NFData s) => NFData (Hourglass s)
instance (Semigroup s) => Semigroup (Hourglass s) where
  Hourglass u l <> Hourglass u' l' = Hourglass (u<>u') (l<>l')
  sconcat hgs = let (us,ls) = NE.unzip $ (upperBulb&&&lowerBulb) <$> hgs
                in Hourglass (sconcat us) (sconcat ls)
instance (Monoid s, Semigroup s) => Monoid (Hourglass s) where
  mempty = Hourglass mempty mempty; mappend = (<>)
  mconcat hgs = let (us,ls) = unzip $ (upperBulb&&&lowerBulb) <$> hgs
                in Hourglass (mconcat us) (mconcat ls)
instance Hask.Applicative Hourglass where
  pure x = Hourglass x x
  Hourglass f g <*> Hourglass x y = Hourglass (f x) (g y)
instance Foldable Hourglass (->) (->) where
  ffoldl f (x, Hourglass a b) = f (f(x,a), b)
  foldMap f (Hourglass a b) = f a `mappend` f b

flipHour :: Hourglass s -> Hourglass s
flipHour (Hourglass u l) = Hourglass l u

newtype Hourglasses s = Hourglasses {
             getHourglasses :: NonEmpty (Hourglass s) }
    deriving (Generic, Hask.Functor, Hask.Foldable)
instance (NFData s) => NFData (Hourglasses s)

data HourglassBulb = UpperBulb | LowerBulb
oneBulb :: HourglassBulb -> (a->a) -> Hourglass a->Hourglass a
oneBulb UpperBulb f (Hourglass u l) = Hourglass (f u) l
oneBulb LowerBulb f (Hourglass u l) = Hourglass u (f l)



data ShadeTree x = PlainLeaves [x]
                 | DisjointBranches !Int (NonEmpty (ShadeTree x))
                 | OverlappingBranches !Int !(Shade x) (NonEmpty (DBranch x))
  deriving (Generic)
           
data DBranch' x c = DBranch { boughDirection :: !(DualSpace (Needle x))
                            , boughContents :: !(Hourglass c) }
  deriving (Generic, Hask.Functor, Hask.Foldable)
type DBranch x = DBranch' x (ShadeTree x)

newtype DBranches' x c = DBranches (NonEmpty (DBranch' x c))
  deriving (Generic, Hask.Functor, Hask.Foldable)

-- ^ /Unsafe/: this assumes the direction information of both containers to be equivalent.
instance (Semigroup c) => Semigroup (DBranches' x c) where
  DBranches b1 <> DBranches b2 = DBranches $ NE.zipWith (\(DBranch d1 c1) (DBranch _ c2)
                                                              -> DBranch d1 $ c1<>c2 ) b1 b2
  


instance (NFData x) => NFData (ShadeTree x) where
  rnf (PlainLeaves xs) = rnf xs
  rnf (DisjointBranches n bs) = n `seq` rnf (NE.toList bs)
  rnf (OverlappingBranches n sh bs) = n `seq` sh `seq` rnf (NE.toList bs)
instance (NFData x) => NFData (DBranch x)
  
-- | Experimental. There might be a more powerful instance possible.
instance (AffineManifold x) => Semimanifold (ShadeTree x) where
  type Needle (ShadeTree x) = Diff x
  PlainLeaves xs .+~^ v = PlainLeaves $ (.+^v)<$>xs 
  OverlappingBranches n sh br .+~^ v
        = OverlappingBranches n (sh.+~^v)
                $ fmap (\(DBranch d c) -> DBranch d $ (.+~^v)<$>c) br
  DisjointBranches n br .+~^ v = DisjointBranches n $ (.+~^v)<$>br

-- | WRT union.
instance WithField ℝ Manifold x => Semigroup (ShadeTree x) where
  PlainLeaves [] <> t = t
  t <> PlainLeaves [] = t
  t <> s = fromLeafPoints $ onlyLeaves t ++ onlyLeaves s
           -- Could probably be done more efficiently
  sconcat = mconcat . NE.toList
instance WithField ℝ Manifold x => Monoid (ShadeTree x) where
  mempty = PlainLeaves []
  mappend = (<>)
  mconcat l = case filter ne l of
               [] -> mempty
               [t] -> t
               l' -> fromLeafPoints $ onlyLeaves =<< l'
   where ne (PlainLeaves []) = False; ne _ = True


-- | Build a really quite nicely balanced tree from a cloud of points, on
--   any real manifold.
-- 
--   Example:
-- 
-- @
-- > :m +Graphics.Dynamic.Plot.R2 Data.Manifold.TreeCover Data.VectorSpace Data.AffineSpace
-- > import Diagrams.Prelude ((^&), P2, R2, circle, fc, (&), moveTo, green)
--  
-- > let testPts0 = [0^&0, 0^&1, 1^&1, 1^&2, 2^&2] :: [P2]  -- Generate sort-of&#x2013;random point cloud
-- > let testPts1 = [p .+^ v^/3 | p<-testPts0, v <- [0^&0, (-1)^&1, 1^&2]]
-- > let testPts2 = [p .+^ v^/4 | p<-testPts1, v <- [0^&0, (-1)^&1, 1^&2]]
-- > let testPts3 = [p .+^ v^/5 | p<-testPts2, v <- [0^&0, (-2)^&1, 1^&2]]
-- > let testPts4 = [p .+^ v^/7 | p<-testPts3, v <- [0^&1, (-2)^&1, 1^&2]]
-- > length testPts4
--     405
-- 
-- > plotWindow [ plot . onlyNodes $ fromLeafPoints testPts4
-- >            , plot [circle 0.06 & moveTo p & fc green :: PlainGraphics | p <- testPts4] ]
-- @
-- 
-- <<images/examples/simple-2d-ShadeTree.png>>
fromLeafPoints :: forall x. WithField ℝ Manifold x => [x] -> ShadeTree x
fromLeafPoints = go zeroV
 where go :: HerMetric' (Needle x) -> [x] -> ShadeTree x
       go preShExpa = \xs -> case pointsShades' (preShExpa^/10) xs of
                     [] -> mempty
                     [(_,rShade)] -> let trials = sShIdPartition rShade xs
                                     in case reduce rShade trials of
                                         Just redBrchs
                                           -> OverlappingBranches
                                                  (length xs) rShade
                                                  (branchProc (shadeExpanse rShade) redBrchs)
                                         _ -> PlainLeaves xs
                     partitions -> DisjointBranches (length xs)
                                   . NE.fromList
                                    $ map (\(xs',pShade) -> go zeroV xs') partitions
        where 
              branchProc redSh = fmap (fmap $ go redSh)
                                 
              reduce :: Shade x -> [DBranch' x [x]] -> Maybe (NonEmpty (DBranch' x [x]))
              reduce _ [] = Nothing
              reduce sh@(Shade c _) brCandidates
                        = case findIndex deficient cards of
                            Just i -> let (DBranch _ reBr, ok) = amputateId i brCandidates
                                      in reduce sh
                                          $ sShIdPartition' c (fold reBr) ok
                            Nothing   -> Just $ NE.fromList brCandidates
               where (cards, maxCard) = (id&&&maximum')
                                $ map (fmap length . boughContents) brCandidates
                     deficient (Hourglass u l) = any (\c -> c^2 <= maxCard + 1) [u,l]
                     maximum' = maximum . fmap (\(Hourglass u l) -> max u l)


sShIdPartition' :: WithField ℝ Manifold x
        => x -> [x] -> [DBranch' x [x]]->[DBranch' x [x]]
sShIdPartition' c xs st
           = foldr (\p -> let (i,h) = ssi p
                                in update_nth (\(DBranch d c)
                                               -> DBranch d (oneBulb h (p:) c))
                                              i)
                         st xs
 where ssi = subshadeId' c (boughDirection<$>st)
sShIdPartition :: WithField ℝ Manifold x => Shade x -> [x] -> [DBranch' x [x]]
sShIdPartition (Shade c expa) xs
    = sShIdPartition' c xs [DBranch v mempty | v <- eigenCoSpan expa]
                                           

update_nth :: (a->a) -> Int -> [a] -> [a]
update_nth _ n l | n<0 = l
update_nth f 0 (c:r) = f c : r
update_nth f n [] = []
update_nth f n (l:r) = l : update_nth f (n-1) r


amputateId :: Int -> [a] -> (a,[a])
amputateId i l = let ([a],bs) = amputateIds [i] l in (a, bs)

deleteIds :: [Int] -> [a] -> [a]
deleteIds kids = snd . amputateIds kids

amputateIds :: [Int]     -- ^ Sorted list of non-negative indices to extract
            -> [a]       -- ^ Input list
            -> ([a],[a]) -- ^ (Extracted elements, remaining elements)
amputateIds = go 0
 where go _ _ [] = ([],[])
       go _ [] l = ([],l)
       go i (k:ks) (x:xs)
         | i==k       = first  (x:) $ go (i+1)    ks  xs
         | otherwise  = second (x:) $ go (i+1) (k:ks) xs


separateOverlap :: WithField ℝ Manifold x
              => ShadeTree x -> ShadeTree x
                     -> ( ShadeTree x -- Overlapping part
                        , (ShadeTree x, ShadeTree x) -- Disjoint parts
                        )
separateOverlap (PlainLeaves []) t = (mempty, (mempty, t))
-- separateOverlap t (PlainLeaves []) = (mempty, (t, mempty))
-- separateOverlap t₁@(OverlappingBranches n₁ sh₁@(Shade ctr₁ ev₁) br₁)
--                 t₂@(OverlappingBranches n₂ sh₂@(Shade ctr₂ ev₂) br₂)
--     | d₁>4 && d₂>4  = ( mempty, (t₁,t₂) )
--     | n₁ > n₂       = seps t₁ t₂
--     | otherwise     = second swap $ seps t₂ t₁
--                       let t₁pts = sShIdPartition sh₂ $ onlyLeaves t₁
--                           cndSectors = zipWith (liftA2 $ separateOverlap . fromLeafPoints)
--                                          t₁pts (NE.toList $ getHourglasses br₂)
--                       in fold (fold cndSectors)
--  where d₁ = minusLogOcclusion sh₁ ctr₂
--        d₂ = minusLogOcclusion sh₂ ctr₁
--        seps (OverlappingBranches n₁ sh₁@(Shade ctr₁ ev₁) br₁)
--             (OverlappingBranches n₂ sh₂@(Shade ctr₂ ev₂) br₂)
--         = let pts = sShIdPartition sh₁ $ onlyLeaves t₂
--               cndSectors = zipWith (liftA2 $ (.fromLeafPoints).separateOverlap)
--                              (NE.toList $ getHourglasses br₁) t₂pts
--           in fold (fold cndSectors)
-- separateOverlap t₁ t₂
--          = ( t₁<>t₂, (mempty, mempty) )


sortByKey :: Ord a => [(a,b)] -> [b]
sortByKey = map snd . sortBy (comparing fst)


data Simplex x n where
   ZeroSimplex :: x -> Simplex x 0
   Simplex :: x -> Simplex x (n-1) -> Simplex x n

newtype Triangulation x n = Triangulation { getTriangulation :: [Simplex x n] }


splxVertices :: Simplex x n -> [x]
splxVertices (ZeroSimplex x) = [x]
splxVertices (Simplex x s') = x : splxVertices s'


data Branchwise :: * -> (Nat -> *) -> Nat -> * where
   Branchwise :: { branchResult :: WithBoundary r n
                 , branchBoundary :: ShadeTree x
                 } -> Branchwise x r n

data WithBoundary :: (Nat -> *) -> Nat -> * where
  WithBoundary :: { inBoundary :: r n
                  , enclosingBoundary :: r (n-1)
                  } -> WithBoundary r n

-- branchwise :: ∀ r n x . WithField ℝ Manifold x
--          ⇒   (∀ k .  ShadeTree x → Option (Branchwise x r k)       )
--            → (∀ k .  r (k-1) → WithBoundary r k → WithBoundary r k
--                                               → WithBoundary r k   )
--            → ShadeTree x → [r n]
-- branchwise f c = map (inBoundary . branchResult) . bw
--  where bw tr | Option(Just r₀)<-f tr  = [r₀]
--        bw (DisjointBranches _ trs) = bw =<< NE.toList trs
--        bw (OverlappingBranches _ _ trs) 
--            = let brResults = fmap bw trs
--              in [ foldr1 (\(Branchwise r bb) (Branchwise r' bb')
--                            -> let (shb, (bbd, bbd')) = separateOverlap bb bb'
--                                   [glue] = branchwise f c shb
--                               in Branchwise (c glue r r') $ bbd<>bbd'
--                          ) . join $ Hask.toList brResults ]
--        bw _ = []
-- 
-- triangBranches :: WithField ℝ Manifold x
--                  => ShadeTree x -> Branchwise x (Triangulation x) n
-- triangBranches _ = undefined
-- 
-- triangulate :: WithField ℝ Manifold x
--                  => ShadeTree x -> Triangulation x n
-- triangulate = inBoundary . branchResult . triangBranches
-- 
-- tringComplete :: WithField ℝ Manifold x
--                  => Triangulation x (n-1) -> Triangulation x n -> Triangulation x n
-- tringComplete (Triangulation trr) (Triangulation tr) = undefined
--  where 
--        bbSimplices = Map.fromList [(i, Left s) | s <- tr | i <- [0::Int ..] ]
--        bbVertices =       [(i, splxVertices s) | s <- tr | i <- [0::Int ..] ]
-- 
 




-- |
-- @
-- 'SimpleTree' x &#x2245; Maybe (x, 'Trees' x)
-- @
type SimpleTree = GenericTree Maybe []
-- |
-- @
-- 'Trees' x &#x2245; [(x, 'Trees' x)]
-- @
type Trees = GenericTree [] []
-- |
-- @
-- 'NonEmptyTree' x &#x2245; (x, 'Trees' x)
-- @
type NonEmptyTree = GenericTree NonEmpty []
    
newtype GenericTree c b x = GenericTree { treeBranches :: c (x,GenericTree b b x) }
 deriving (Hask.Functor)
instance (Hask.MonadPlus c) => Semigroup (GenericTree c b x) where
  GenericTree b1 <> GenericTree b2 = GenericTree $ Hask.mplus b1 b2
instance (Hask.MonadPlus c) => Monoid (GenericTree c b x) where
  mempty = GenericTree Hask.mzero
  mappend = (<>)
deriving instance Show (c (x, GenericTree b b x)) => Show (GenericTree c b x)

-- | Imitate the specialised 'ShadeTree' structure with a simpler, generic tree.
onlyNodes :: WithField ℝ Manifold x => ShadeTree x -> Trees x
onlyNodes (PlainLeaves []) = GenericTree []
onlyNodes (PlainLeaves ps) = let (ctr,_) = pseudoECM $ NE.fromList ps
                             in GenericTree [ (ctr, GenericTree $ (,mempty) <$> ps) ]
onlyNodes (DisjointBranches _ brs) = Hask.foldMap onlyNodes brs
onlyNodes (OverlappingBranches _ (Shade ctr _) brs)
              = GenericTree [ (ctr, Hask.foldMap (Hask.foldMap onlyNodes) brs) ]


-- | Left (and, typically, also right) inverse of 'fromLeafNodes'.
onlyLeaves :: WithField ℝ Manifold x => ShadeTree x -> [x]
onlyLeaves tree = dismantle tree []
 where dismantle (PlainLeaves xs) = (xs++)
       dismantle (OverlappingBranches _ _ brs)
              = foldr ((.) . dismantle) id $ Hask.foldMap (Hask.toList) brs
       dismantle (DisjointBranches _ brs) = foldr ((.) . dismantle) id $ NE.toList brs








data Sawbones x = Sawbones { sawnTrunk1, sawnTrunk2 :: [x]->[x]
                           , sawdust1,   sawdust2   :: [x]      }
instance Semigroup (Sawbones x) where
  Sawbones st11 st12 sd11 sd12 <> Sawbones st21 st22 sd21 sd22
     = Sawbones (st11.st21) (st12.st22) (sd11<>sd21) (sd12<>sd22)
instance Monoid (Sawbones x) where
  mempty = Sawbones id id [] []
  mappend = (<>)

chainsaw :: WithField ℝ Manifold x => Cutplane x -> ShadeTree x -> Sawbones x
chainsaw cpln (PlainLeaves xs) = Sawbones id id sd1 sd2
 where (sd1,sd2) = partition (\x -> sideOfCut cpln x == Option(Just PositiveHalfSphere)) xs
chainsaw cpln (DisjointBranches _ brs) = Hask.foldMap (chainsaw cpln) brs
chainsaw cpln (OverlappingBranches _ (Shade _ bexpa) brs) = Sawbones t1 t2 d1 d2
 where (Sawbones subT1 subT2 subD1 subD2)
             = Hask.foldMap (Hask.foldMap (chainsaw cpln) . boughContents) brs
       [(t1,d1), (t2,d2)] = refiltrate <$> [(subT1,subD1), (subT2,subD2)]
       refiltrate (t,d) = foldl' go (t,[]) $ foci d
        where go (t',d') (dp,dqs) = case fathomCD dp of
                           Option (Just dpCD) | all (unsheltered dpCD) dqs
                                    -> ((dp:).t', d')
                           _        -> (t',    dp:d')
               where unsheltered dpCutDist dq = case ptsDist dp dq of
                        Option (Just d) -> d > dpCutDist
                        _               -> True
                     ptsDist = fmap (metric $ recipMetric bexpa) .: (.-~.)
       fathomCD = fathomCutDistance cpln bexpa
       

type DList x = [x]->[x]
    
data DustyEdges x = DustyEdges { sawChunk :: DList x, chunkDust :: DBranches' x [x] }
instance Semigroup (DustyEdges x) where
  DustyEdges c1 d1 <> DustyEdges c2 d2 = DustyEdges (c1.c2) (d1<>d2)

data Sawboneses x = SingleCut (Sawbones x)
                  | Sawboneses (DBranches' x (DustyEdges x))
    deriving (Generic)
instance Semigroup (Sawboneses x) where
  SingleCut c <> SingleCut d = SingleCut $ c<>d
  Sawboneses c <> Sawboneses d = Sawboneses $ c<>d



-- | Saw a tree into the domains covered by the respective branches of another tree.
sShSaw :: WithField ℝ Manifold x
          => ShadeTree x   -- ^ &#x201c;Reference tree&#x201d;, defines the cut regions.
                           --   Must be at least one level of 'OverlappingBranches' deep.
          -> ShadeTree x   -- ^ Tree to take the actual contents from.
          -> Sawboneses x  -- ^ All points within each region, plus those from the
                           --   boundaries of each neighbouring region.
sShSaw (OverlappingBranches _ (Shade sh _) (DBranch dir _ :| [])) src
          = SingleCut $ chainsaw (cutplaneFromDProdsignChange sh dir) src
sShSaw (OverlappingBranches _ (Shade cctr _) cbrs) (PlainLeaves xs)
          = Sawboneses . DBranches $ NE.fromList ngbsAdded
 where brsEmpty = fmap (\(DBranch dir _)-> DBranch dir mempty) $ NE.toList cbrs
       srcDistrib = sShIdPartition' cctr xs brsEmpty
       ngbsAdded = fmap (\(DBranch dir (Hourglass u l), othrs)
                             -> let [allOthr,allOthr']
                                        = map (DBranches . NE.fromList)
                                            [othrs, fmap (\(DBranch d' o)
                                                          ->DBranch(negateV d') o) othrs]
                                in DBranch dir $ Hourglass (DustyEdges (u++) allOthr)
                                                           (DustyEdges (l++) allOthr')
                        ) $ foci srcDistrib
sShSaw cuts@(OverlappingBranches _ (Shade sh _) cbrs)
        (OverlappingBranches _ (Shade _ bexpa) brs)
          = Sawboneses . DBranches $ ftr'd
 where Option (Just (Sawboneses (DBranches recursed)))
             = Hask.foldMap (Hask.foldMap (pure . sShSaw cuts) . boughContents) brs
       ftr'd = fmap (\(DBranch dir1 ds) -> DBranch dir1 $ fmap (
                         \(DustyEdges bk (DBranches dds))
                                -> DustyEdges bk . DBranches $ fmap (obsFilter dir1) dds
                                                               ) ds ) recursed
       obsFilter dir1 (DBranch dir2 (Hourglass pd2 md2))
                         = DBranch dir2 $ Hourglass pd2' md2'
        where cpln cpSgn = cutplaneFromDProdsignChange sh $ dir1 ^+^ cpSgn*^dir2
              [pd2', md2'] = zipWith (occl . cpln) [-1, 1] [pd2, md2] 
              occl cpl = foldl' go [] . foci
               where go d' (dp,dqs) = case fathomCD dp of
                           Option (Just dpCD) | all (unsheltered dpCD) dqs
                                                      -> d'
                           _                          -> dp:d'
                      where unsheltered dpCutDist dq = case ptsDist dp dq of
                             Option (Just d) -> d > dpCutDist
                             _               -> True
                            ptsDist = fmap (metric $ recipMetric bexpa) .: (.-~.)
                     fathomCD = fathomCutDistance cpl bexpa
sShSaw _ _ = error "`sShSaw` is not supposed to cut anything else but `OverlappingBranches`"


foci :: [a] -> [(a,[a])]
foci [] = []
foci (x:xs) = (x,xs) : fmap (second (x:)) (foci xs)
       

(.:) :: (c->d) -> (a->b->c) -> a->b->d 
(.:) = (.) . (.)

