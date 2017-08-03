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
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE UnicodeSyntax              #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE TemplateHaskell            #-}


module Data.Manifold.TreeCover (
       -- * Shades 
         Shade(..), pattern(:±), Shade'(..), (|±|), IsShade
       -- ** Lenses
       , shadeCtr, shadeExpanse, shadeNarrowness
       -- ** Construction
       , fullShade, fullShade', pointsShades, pointsShade's
       , pointsCovers, pointsCover's, coverAllAround
       -- ** Evaluation
       , occlusion, prettyShowsPrecShade', prettyShowShade'
       -- ** Misc
       , factoriseShade, intersectShade's, linIsoTransformShade
       , embedShade, projectShade
       , Refinable, subShade', refineShade', convolveShade', coerceShade
       , mixShade's
       -- * Shade trees
       , ShadeTree(..), fromLeafPoints, onlyLeaves
       , indexShadeTree, positionIndex
       -- ** View helpers
       , onlyNodes, trunkBranches, nLeaves
       -- ** Auxiliary types
       , SimpleTree, Trees, NonEmptyTree, GenericTree(..), 朳
       -- * Misc
       , HasFlatView(..), shadesMerge, smoothInterpolate
       , allTwigs, twigsWithEnvirons, Twig, TwigEnviron, seekPotentialNeighbours
       , completeTopShading, flexTwigsShading, coerceShadeTree
       , WithAny(..), Shaded, fmapShaded, joinShaded
       , constShaded, zipTreeWithList, stripShadedUntopological
       , stiAsIntervalMapping, spanShading
       , estimateLocalJacobian
       , DifferentialEqn, LocalDifferentialEqn(..)
       , propagateDEqnSolution_loc, LocalDataPropPlan(..)
       , rangeOnGeodesic
       -- ** Triangulation-builders
       , TriangBuild, doTriangBuild
       , AutoTriang, breakdownAutoTriang
       -- ** External
       , AffineManifold, euclideanMetric
    ) where


import Data.List hiding (filter, all, elem, sum, foldr1)
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Vector as Arr
import Data.List.NonEmpty (NonEmpty(..))
import Data.List.FastNub
import qualified Data.List.NonEmpty as NE
import Data.Semigroup
import Data.Ord (comparing)
import Control.DeepSeq

import Data.VectorSpace
import Data.AffineSpace
import Math.LinearMap.Category
import Data.Tagged

import Data.SimplicialComplex
import Data.Manifold.Shade
import Data.Manifold.Types
import Data.Manifold.Types.Primitive ((^), empty)
import Data.Manifold.PseudoAffine
import Data.Manifold.Riemannian
import Data.Manifold.Atlas
import Data.Function.Affine
    
import Data.Embedding
import Data.CoNat

import Control.Lens (Lens', (^.), (.~), (%~), (&), _2, swapped)
import Control.Lens.TH

import qualified Prelude as Hask hiding(foldl, sum, sequence)
import qualified Control.Applicative as Hask
import qualified Control.Monad       as Hask hiding(forM_, sequence)
import Data.Functor.Identity
import Control.Monad.Trans.State
import Control.Monad.Trans.Writer
import Control.Monad.Trans.OuterMaybe
import Control.Monad.Trans.Class
import qualified Data.Foldable       as Hask
import Data.Foldable (all, elem, toList, sum, foldr1)
import qualified Data.Traversable as Hask
import Data.Traversable (forM)

import Control.Category.Constrained.Prelude hiding
     ((^), all, elem, sum, forM, Foldable(..), foldr1, Traversable, traverse)
import Control.Arrow.Constrained
import Control.Monad.Constrained hiding (forM)
import Data.Foldable.Constrained
import Data.Traversable.Constrained (traverse)

import GHC.Generics (Generic)
import Data.Type.Coercion



type Depth = Int
data Wall x = Wall { _wallID :: (Depth,(Int,Int))
                   , _wallAnchor :: Interior x
                   , _wallNormal :: Needle' x
                   , _wallDistance :: Scalar (Needle x)
                   }
makeLenses ''Wall


subshadeId' :: ∀ x . (WithField ℝ PseudoAffine x, LinearSpace (Needle x))
                   => x -> NonEmpty (Needle' x) -> x -> (Int, HourglassBulb)
subshadeId' c expvs x = case ( dualSpaceWitness :: DualNeedleWitness x
                             , x .-~. c ) of
    (DualSpaceWitness, Just v)
                    -> let (iu,vl) = maximumBy (comparing $ abs . snd)
                                      $ zip [0..] (map (v <.>^) $ NE.toList expvs)
                       in (iu, if vl>0 then UpperBulb else LowerBulb)
    _ -> (-1, error "Trying to obtain the subshadeId of a point not actually included in the shade.")

subshadeId :: ( WithField ℝ PseudoAffine x, LinearSpace (Needle x)
              , FiniteDimensional (Needle' x) )
                    => Shade x -> x -> (Int, HourglassBulb)
subshadeId (Shade c expa) = subshadeId' (fromInterior c)
                              . NE.fromList $ normSpanningSystem' expa
                 





-- | Hourglass as the geometric shape (two opposing ~conical volumes, sharing
--   only a single point in the middle); has nothing to do with time.
data Hourglass s = Hourglass { upperBulb, lowerBulb :: !s }
            deriving (Generic, Hask.Functor, Hask.Foldable, Show)
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

data HourglassBulb = UpperBulb | LowerBulb
oneBulb :: HourglassBulb -> (a->a) -> Hourglass a->Hourglass a
oneBulb UpperBulb f (Hourglass u l) = Hourglass (f u) l
oneBulb LowerBulb f (Hourglass u l) = Hourglass u (f l)


type LeafCount = Int
type LeafIndex = Int

data ShadeTree x = PlainLeaves [x]
                 | DisjointBranches !LeafCount (NonEmpty (ShadeTree x))
                 | OverlappingBranches !LeafCount !(Shade x) (NonEmpty (DBranch x))
  deriving (Generic)
deriving instance ( WithField ℝ PseudoAffine x, Show x
                  , Show (Interior x), Show (Needle' x), Show (Metric' x) )
             => Show (ShadeTree x)
           
data DBranch' x c = DBranch { boughDirection :: !(Needle' x)
                            , boughContents :: !(Hourglass c) }
  deriving (Generic, Hask.Functor, Hask.Foldable)
type DBranch x = DBranch' x (ShadeTree x)
deriving instance ( WithField ℝ PseudoAffine x, Show (Needle' x), Show c )
             => Show (DBranch' x c)

newtype DBranches' x c = DBranches (NonEmpty (DBranch' x c))
  deriving (Generic, Hask.Functor, Hask.Foldable)
deriving instance ( WithField ℝ PseudoAffine x, Show (Needle' x), Show c )
             => Show (DBranches' x c)

-- ^ /Unsafe/: this assumes the direction information of both containers to be equivalent.
instance (Semigroup c) => Semigroup (DBranches' x c) where
  DBranches b1 <> DBranches b2 = DBranches $ NE.zipWith (\(DBranch d1 c1) (DBranch _ c2)
                                                              -> DBranch d1 $ c1<>c2 ) b1 b2



trunkBranches :: ShadeTree x -> NonEmpty (LeafIndex, ShadeTree x)
trunkBranches (OverlappingBranches _ _ brs)
        = (`evalState`0)
            . forM (brs >>= \(DBranch _ (Hourglass t b)) -> t:|[b]) $ \st -> do
               i₀ <- get
               put $ i₀ + nLeaves st
               return (i₀, st)
trunkBranches (DisjointBranches _ brs) = (`evalState`0) . forM brs $ \st -> do
               i₀ <- get
               put $ i₀ + nLeaves st
               return (i₀, st)
trunkBranches t = pure (0,t)
  
directionChoices :: WithField ℝ Manifold x
               => [DBranch x]
                 -> [ ( (Needle' x, ShadeTree x)
                      ,[(Needle' x, ShadeTree x)] ) ]
directionChoices = map (snd *** map snd) . directionIChoices 0

directionIChoices :: (WithField ℝ PseudoAffine x, AdditiveGroup (Needle' x))
               => Int -> [DBranch x]
                 -> [ ( (Int, (Needle' x, ShadeTree x))
                      ,[(Int, (Needle' x, ShadeTree x))] ) ]
directionIChoices _ [] = []
directionIChoices i₀ (DBranch ѧ (Hourglass t b) : hs)
         =  ( top, bot : map fst uds )
          : ( bot, top : map fst uds )
          : map (second $ (top:) . (bot:)) uds
 where top = (i₀,(ѧ,t))
       bot = (i₀+1,(negateV ѧ,b))
       uds = directionIChoices (i₀+2) hs

traverseDirectionChoices :: ( WithField ℝ PseudoAffine x, LSpace (Needle x)
                            , Hask.Applicative f )
               => (    (Int, (Needle' x, ShadeTree x))
                    -> [(Int, (Needle' x, ShadeTree x))]
                    -> f (ShadeTree x) )
                 -> [DBranch x]
                 -> f [DBranch x]
traverseDirectionChoices f dbs
           = td [] . scanLeafNums 0
               $ dbs >>= \(DBranch ѧ (Hourglass τ β))
                              -> [(ѧ,τ), (negateV ѧ,β)]
 where td pds (ѧt@(_,(ѧ,_)):vb:vds)
         = liftA3 (\t' b' -> (DBranch ѧ (Hourglass t' b') :))
             (f ѧt $ vb:uds)
             (f vb $ ѧt:uds)
             $ td (ѧt:vb:pds) vds
        where uds = pds ++ vds
       td _ _ = pure []
       scanLeafNums _ [] = []
       scanLeafNums i₀ ((v,t):vts) = (i₀, (v,t)) : scanLeafNums (i₀ + nLeaves t) vts


indexDBranches :: NonEmpty (DBranch x) -> NonEmpty (DBranch' x (Int, ShadeTree x))
indexDBranches (DBranch d (Hourglass t b) :| l) -- this could more concisely be written as a traversal
              = DBranch d (Hourglass (0,t) (nt,b)) :| ixDBs (nt + nb) l
 where nt = nLeaves t; nb = nLeaves b
       ixDBs _ [] = []
       ixDBs i₀ (DBranch δ (Hourglass τ β) : l)
               = DBranch δ (Hourglass (i₀,τ) (i₀+nτ,β)) : ixDBs (i₀ + nτ + nβ) l
        where nτ = nLeaves τ; nβ = nLeaves β

instance (NFData x, NFData (Needle' x)) => NFData (ShadeTree x) where
  rnf (PlainLeaves xs) = rnf xs
  rnf (DisjointBranches n bs) = n `seq` rnf (NE.toList bs)
  rnf (OverlappingBranches n sh bs) = n `seq` sh `seq` rnf (NE.toList bs)
instance (NFData x, NFData (Needle' x)) => NFData (DBranch x)
  
-- | Experimental. There might be a more powerful instance possible.
instance (AffineManifold x) => Semimanifold (ShadeTree x) where
  type Needle (ShadeTree x) = Diff x
  fromInterior = id
  toInterior = pure
  translateP = Tagged (.+~^)
  PlainLeaves xs .+~^ v = PlainLeaves $ (.+^v)<$>xs 
  OverlappingBranches n sh br .+~^ v
        = OverlappingBranches n (sh.+~^v)
                $ fmap (\(DBranch d c) -> DBranch d $ (.+~^v)<$>c) br
  DisjointBranches n br .+~^ v = DisjointBranches n $ (.+~^v)<$>br
  semimanifoldWitness = case semimanifoldWitness :: SemimanifoldWitness x of
     SemimanifoldWitness BoundarylessWitness -> SemimanifoldWitness BoundarylessWitness

-- | WRT union.
instance (WithField ℝ Manifold x, SimpleSpace (Needle x)) => Semigroup (ShadeTree x) where
  PlainLeaves [] <> t = t
  t <> PlainLeaves [] = t
  t <> s = fromLeafPoints $ onlyLeaves t ++ onlyLeaves s
           -- Could probably be done more efficiently
  sconcat = mconcat . NE.toList
instance (WithField ℝ Manifold x, SimpleSpace (Needle x)) => Monoid (ShadeTree x) where
  mempty = PlainLeaves []
  mappend = (<>)
  mconcat l = case filter ne l of
               [] -> mempty
               [t] -> t
               l' -> fromLeafPoints $ onlyLeaves =<< l'
   where ne (PlainLeaves []) = False; ne _ = True


-- | Build a quite nicely balanced tree from a cloud of points, on any real manifold.
-- 
--   Example: https://nbviewer.jupyter.org/github/leftaroundabout/manifolds/blob/master/test/Trees-and-Webs.ipynb#pseudorandomCloudTree
-- 
-- <<images/examples/simple-2d-ShadeTree.png>>
fromLeafPoints :: ∀ x. (WithField ℝ Manifold x, SimpleSpace (Needle x))
                         => [x] -> ShadeTree x
fromLeafPoints = fromLeafPoints' sShIdPartition


-- | The leaves of a shade tree are numbered. For a given index, this function
--   attempts to find the leaf with that ID, within its immediate environment.
indexShadeTree :: ∀ x . ShadeTree x -> Int -> Either Int ([ShadeTree x], x)
indexShadeTree _ i
    | i<0        = Left i
indexShadeTree sh@(PlainLeaves lvs) i = case length lvs of
  n | i<n       -> Right ([sh], lvs!!i)
    | otherwise -> Left $ i-n
indexShadeTree (DisjointBranches n brs) i
    | i<n        = foldl (\case 
                             Left i' -> (`indexShadeTree`i')
                             result  -> return result
                         ) (Left i) brs
    | otherwise  = Left $ i-n
indexShadeTree sh@(OverlappingBranches n _ brs) i
    | i<n        = first (sh:) <$> foldl (\case 
                             Left i' -> (`indexShadeTree`i')
                             result  -> return result
                         ) (Left i) (toList brs>>=toList)
    | otherwise  = Left $ i-n


-- | “Inverse indexing” of a tree. This is roughly a nearest-neighbour search,
--   but not guaranteed to give the correct result unless evaluated at the
--   precise position of a tree leaf.
positionIndex :: ∀ x . (WithField ℝ Manifold x, SimpleSpace (Needle x))
       => Maybe (Metric x)   -- ^ For deciding (at the lowest level) what “close” means;
                             --   this is optional for any tree of depth >1.
        -> ShadeTree x       -- ^ The tree to index into
        -> x                 -- ^ Position to look up
        -> Maybe (Int, ([ShadeTree x], x))
                   -- ^ Index of the leaf near to the query point, the “path” of
                   --   environment trees leading down to its position (in decreasing
                   --   order of size), and actual position of the found node.
positionIndex (Just m) sh@(PlainLeaves lvs) x
        = case catMaybes [ ((i,p),) . normSq m <$> p.-~.x
                            | (i,p) <- zip [0..] lvs] of
           [] -> empty
           l | ((i,p),_) <- minimumBy (comparing snd) l
              -> pure (i, ([sh], p))
positionIndex m (DisjointBranches _ brs) x
        = fst . foldl' (\case
                          (q@(Just _), i₀) -> const (q, i₀)
                          (_, i₀) -> \t' -> ( first (+i₀) <$> positionIndex m t' x
                                            , i₀+nLeaves t' ) )
                       (empty, 0)
              $        brs
positionIndex _ sh@(OverlappingBranches n (Shade c ce) brs) x
   | PseudoAffineWitness (SemimanifoldWitness _)
               <- pseudoAffineWitness :: PseudoAffineWitness x
   , Just vx <- toInterior x>>=(.-~.c)
        = let (_,(i₀,t')) = maximumBy (comparing fst)
                       [ (σ*ω, t')
                       | DBranch d (Hourglass t'u t'd) <- NE.toList $ indexDBranches brs
                       , let ω = d<.>^vx
                       , (t',σ) <- [(t'u, 1), (t'd, -1)] ]
          in ((+i₀) *** first (sh:))
                 <$> positionIndex (return $ dualNorm' ce) t' x
positionIndex _ _ _ = empty



fromFnGraphPoints :: ∀ x y . ( WithField ℝ Manifold x, WithField ℝ Manifold y
                             , SimpleSpace (Needle x), SimpleSpace (Needle y) )
                     => [(x,y)] -> ShadeTree (x,y)
fromFnGraphPoints = case ( dualSpaceWitness :: DualNeedleWitness x
                         , boundarylessWitness :: BoundarylessWitness x
                         , dualSpaceWitness :: DualNeedleWitness y
                         , boundarylessWitness :: BoundarylessWitness y ) of
    (DualSpaceWitness,BoundarylessWitness,DualSpaceWitness,BoundarylessWitness)
        -> fromLeafPoints' $
     \(Shade c expa) xs -> case
            [ DBranch (v, zeroV) mempty
            | v <- normSpanningSystem' (transformNorm (id&&&zeroV) expa :: Metric' x) ] of
         (b:bs) -> sShIdPartition' c xs $ b:|bs

fromLeafPoints' :: ∀ x. (WithField ℝ Manifold x, SimpleSpace (Needle x)) =>
    (Shade x -> [x] -> NonEmpty (DBranch' x [x])) -> [x] -> ShadeTree x
fromLeafPoints' sShIdPart = go boundarylessWitness mempty
 where go :: BoundarylessWitness x -> Metric' x -> [x] -> ShadeTree x
       go bw@BoundarylessWitness preShExpa
            = \xs -> case pointsShades' (scaleNorm (1/3) preShExpa) xs of
                     [] -> mempty
                     [(_,rShade)] -> let trials = sShIdPart rShade xs
                                     in case reduce rShade trials of
                                         Just redBrchs
                                           -> OverlappingBranches
                                                  (length xs) rShade
                                                  (branchProc (_shadeExpanse rShade) redBrchs)
                                         _ -> PlainLeaves xs
                     partitions -> DisjointBranches (length xs)
                                   . NE.fromList
                                    $ map (\(xs',pShade) -> go bw mempty xs') partitions
        where 
              branchProc redSh = fmap (fmap $ go bw redSh)
                                 
              reduce :: Shade x -> NonEmpty (DBranch' x [x])
                                      -> Maybe (NonEmpty (DBranch' x [x]))
              reduce sh@(Shade c _) brCandidates
                        = case findIndex deficient cards of
                            Just i | (DBranch _ reBr, o:ok)
                                             <- amputateId i (NE.toList brCandidates)
                                           -> reduce sh
                                                $ sShIdPartition' c (fold reBr) (o:|ok)
                                   | otherwise -> Nothing
                            _ -> Just brCandidates
               where (cards, maxCard) = (NE.toList &&& maximum')
                                $ fmap (fmap length . boughContents) brCandidates
                     deficient (Hourglass u l) = any (\c -> c^2 <= maxCard + 1) [u,l]
                     maximum' = maximum . NE.toList . fmap (\(Hourglass u l) -> max u l)


sShIdPartition' :: (WithField ℝ PseudoAffine x, SimpleSpace (Needle x))
        => Interior x -> [x] -> NonEmpty (DBranch' x [x])->NonEmpty (DBranch' x [x])
sShIdPartition' c xs st
           = foldr (\p -> let (i,h) = ssi p
                          in asList $ update_nth (\(DBranch d c)
                                                    -> DBranch d (oneBulb h (p:) c))
                                      i )
                   st xs
 where ssi = subshadeId' (fromInterior c) (boughDirection<$>st)
sShIdPartition :: (WithField ℝ PseudoAffine x, SimpleSpace (Needle x))
                    => Shade x -> [x] -> NonEmpty (DBranch' x [x])
sShIdPartition (Shade c expa) xs
 | b:bs <- [DBranch v mempty | v <- normSpanningSystem' expa]
    = sShIdPartition' c xs $ b:|bs
                                           

asList :: ([a]->[b]) -> NonEmpty a->NonEmpty b
asList f = NE.fromList . f . NE.toList

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




sortByKey :: Ord a => [(a,b)] -> [b]
sortByKey = map snd . sortBy (comparing fst)


trunks :: ∀ x. (WithField ℝ PseudoAffine x, SimpleSpace (Needle x))
                  => ShadeTree x -> [Shade x]
trunks t = case (pseudoAffineWitness :: PseudoAffineWitness x, t) of
  (PseudoAffineWitness (SemimanifoldWitness BoundarylessWitness), PlainLeaves lvs)
                                         -> pointsCovers . catMaybes $ toInterior<$>lvs
  (_, DisjointBranches _ brs)            -> Hask.foldMap trunks brs
  (_, OverlappingBranches _ sh _)        -> [sh]


nLeaves :: ShadeTree x -> Int
nLeaves (PlainLeaves lvs) = length lvs
nLeaves (DisjointBranches n _) = n
nLeaves (OverlappingBranches n _ _) = n


instance ImpliesMetric ShadeTree where
  type MetricRequirement ShadeTree x = (WithField ℝ PseudoAffine x, SimpleSpace (Needle x))
  inferMetric = stInfMet
   where stInfMet :: ∀ x . (WithField ℝ PseudoAffine x, SimpleSpace (Needle x))
                                => ShadeTree x -> Metric x
         stInfMet (OverlappingBranches _ (Shade _ e) _) = dualNorm' e
         stInfMet (PlainLeaves lvs)
               = case pointsShades $ Hask.toList . toInterior =<< lvs :: [Shade x] of
             (Shade _ sh:_) -> dualNorm' sh
             _ -> mempty
         stInfMet (DisjointBranches _ (br:|_)) = inferMetric br
  inferMetric' = stInfMet
   where stInfMet :: ∀ x . (WithField ℝ PseudoAffine x, SimpleSpace (Needle x))
                                => ShadeTree x -> Metric' x
         stInfMet (OverlappingBranches _ (Shade _ e) _) = e
         stInfMet (PlainLeaves lvs)
               = case pointsShades $ Hask.toList . toInterior =<< lvs :: [Shade x] of
             (Shade _ sh:_) -> sh
             _ -> mempty
         stInfMet (DisjointBranches _ (br:|_)) = inferMetric' br



overlappingBranches :: Shade x -> NonEmpty (DBranch x) -> ShadeTree x
overlappingBranches shx brs = OverlappingBranches n shx brs
 where n = sum $ fmap (sum . fmap nLeaves) brs

unsafeFmapLeaves :: (x -> x) -> ShadeTree x -> ShadeTree x
unsafeFmapLeaves f (PlainLeaves lvs) = PlainLeaves $ fmap f lvs
unsafeFmapLeaves f (DisjointBranches n brs)
                  = DisjointBranches n $ unsafeFmapLeaves f <$> brs
unsafeFmapLeaves f (OverlappingBranches n sh brs)
                  = OverlappingBranches n sh $ fmap (unsafeFmapLeaves f) <$> brs

unsafeFmapTree :: (NonEmpty x -> NonEmpty y)
               -> (Needle' x -> Needle' y)
               -> (Shade x -> Shade y)
               -> ShadeTree x -> ShadeTree y
unsafeFmapTree _ _ _ (PlainLeaves []) = PlainLeaves []
unsafeFmapTree f _ _ (PlainLeaves lvs) = PlainLeaves . toList . f $ NE.fromList lvs
unsafeFmapTree f fn fs (DisjointBranches n brs)
    = let brs' = unsafeFmapTree f fn fs <$> brs
      in DisjointBranches (sum $ nLeaves<$>brs') brs'
unsafeFmapTree f fn fs (OverlappingBranches n sh brs)
    = let brs' = fmap (\(DBranch dir br)
                      -> DBranch (fn dir) (unsafeFmapTree f fn fs<$>br)
                      ) brs
      in overlappingBranches (fs sh) brs'

coerceShadeTree :: ∀ x y . (LocallyCoercible x y, Manifold x, Manifold y, SimpleSpace (Needle y))
                       => ShadeTree x -> ShadeTree y
coerceShadeTree = case ( dualSpaceWitness :: DualNeedleWitness x
                       , dualSpaceWitness :: DualNeedleWitness y ) of
   (DualSpaceWitness,DualSpaceWitness)
      -> unsafeFmapTree (fmap locallyTrivialDiffeomorphism)
                                 (coerceNeedle' ([]::[(x,y)]) $)
                                 coerceShade




type Twig x = (Int, ShadeTree x)
type TwigEnviron x = [Twig x]

allTwigs :: ∀ x . WithField ℝ PseudoAffine x => ShadeTree x -> [Twig x]
allTwigs tree = go 0 tree []
 where go n₀ (DisjointBranches _ dp)
         = snd (foldl' (\(n₀',prev) br -> (n₀'+nLeaves br, prev . go n₀' br)) (n₀,id) dp)
       go n₀ (OverlappingBranches _ _ dp)
         = snd (foldl' (\(n₀',prev) (DBranch _ (Hourglass top bot))
                          -> ( n₀'+nLeaves top+nLeaves bot
                             , prev . go n₀' top . go (n₀'+nLeaves top) bot) )
                        (n₀,id) $ NE.toList dp)
       go n₀ twig = ((n₀,twig):)

-- Formerly, 'twigsWithEnvirons' what has now become 'traverseTwigsWithEnvirons'.
-- The simple list-yielding version (see rev. b4a427d59ec82889bab2fde39225b14a57b694df)
-- may well be more efficient than the current traversal-derived version.

-- | Example: https://nbviewer.jupyter.org/github/leftaroundabout/manifolds/blob/master/test/Trees-and-Webs.ipynb#pseudorandomCloudTree
-- 
--   <<images/examples/TreesAndWebs/2D-scatter_twig-environs.png>>
twigsWithEnvirons :: ∀ x. (WithField ℝ Manifold x, SimpleSpace (Needle x))
    => ShadeTree x -> [(Twig x, TwigEnviron x)]
twigsWithEnvirons = execWriter . traverseTwigsWithEnvirons (writer . (snd.fst&&&pure))

traverseTwigsWithEnvirons :: ∀ x f .
            (WithField ℝ PseudoAffine x, SimpleSpace (Needle x), Hask.Applicative f)
    => ( (Twig x, TwigEnviron x) -> f (ShadeTree x) ) -> ShadeTree x -> f (ShadeTree x)
traverseTwigsWithEnvirons f = fst . go pseudoAffineWitness [] . (0,)
 where go :: PseudoAffineWitness x -> TwigEnviron x -> Twig x -> (f (ShadeTree x), Bool)
       go sw _ (i₀, DisjointBranches nlvs djbs) = ( fmap (DisjointBranches nlvs)
                                                   . Hask.traverse (fst . go sw [])
                                                   $ NE.zip ioffs djbs
                                               , False )
        where ioffs = NE.scanl (\i -> (+i) . nLeaves) i₀ djbs
       go sw@(PseudoAffineWitness (SemimanifoldWitness BoundarylessWitness)) envi
           ct@(i₀, (OverlappingBranches nlvs rob@(Shade robc _) brs))
                = ( case descentResult of
                     OuterNothing -> f
                         $ purgeRemotes
                            (ct, Hask.foldMap (\(io,te)
                                         -> first (+io) <$> twigProximæ sw robc te) envi)
                     OuterJust dR -> fmap (OverlappingBranches nlvs rob . NE.fromList) dR
                  , False )
        where descentResult = traverseDirectionChoices tdc $ NE.toList brs
              tdc (io, (vy, ty)) alts = case go sw envi'' (i₀+io, ty) of
                                   (_, True) -> OuterNothing
                                   (down, _) -> OuterJust down
               where envi'' = filter (snd >>> trunks >>> \(Shade ce _:_)
                                         -> let Just δyenv = ce.-~.robc
                                                qq = vy<.>^δyenv
                                            in qq > -1
                                       ) envi'
                              ++ map ((+i₀)***snd) alts
              envi' = approach =<< envi
              approach (i₀e, apt@(OverlappingBranches _ (Shade envc _) _))
                  = first (+i₀e) <$> twigsaveTrim hither apt
               where Just δxenv = robc .-~. envc
                     hither (DBranch bdir (Hourglass bdc₁ bdc₂))
                       =  [(0           , bdc₁) | overlap > -1]
                       ++ [(nLeaves bdc₁, bdc₂) | overlap < 1]
                      where overlap = bdir<.>^δxenv
              approach q = [q]
       go (PseudoAffineWitness (SemimanifoldWitness _)) envi plvs@(i₀, (PlainLeaves _))
                         = (f $ purgeRemotes (plvs, envi), True)
       
       twigProximæ :: PseudoAffineWitness x -> Interior x -> ShadeTree x -> TwigEnviron x
       twigProximæ sw x₀ (DisjointBranches _ djbs)
               = Hask.foldMap (\(i₀,st) -> first (+i₀) <$> twigProximæ sw x₀ st)
                    $ NE.zip ioffs djbs
        where ioffs = NE.scanl (\i -> (+i) . nLeaves) 0 djbs
       twigProximæ sw@(PseudoAffineWitness (SemimanifoldWitness _))
                          x₀ ct@(OverlappingBranches _ (Shade xb qb) brs)
                   = twigsaveTrim hither ct
        where Just δxb = x₀ .-~. xb
              hither (DBranch bdir (Hourglass bdc₁ bdc₂))
                =  ((guard (overlap > -1)) >> twigProximæ sw x₀ bdc₁)
                ++ ((guard (overlap < 1)) >> first (+nLeaves bdc₁)<$>twigProximæ sw x₀ bdc₂)
               where overlap = bdir<.>^δxb
       twigProximæ _ _ plainLeaves = [(0, plainLeaves)]
       
       twigsaveTrim :: (DBranch x -> TwigEnviron x) -> ShadeTree x -> TwigEnviron x
       twigsaveTrim f ct@(OverlappingBranches _ _ dbs)
                 = case Hask.mapM (\(i₀,dbr) -> noLeaf $ first(+i₀)<$>f dbr)
                                 $ NE.zip ioffs dbs of
                      Just pqe -> Hask.fold pqe
                      _        -> [(0,ct)]
        where noLeaf [(_,PlainLeaves _)] = empty
              noLeaf bqs = pure bqs
              ioffs = NE.scanl (\i -> (+i) . sum . fmap nLeaves . toList) 0 dbs
       
       purgeRemotes :: (Twig x, TwigEnviron x) -> (Twig x, TwigEnviron x)
       purgeRemotes = id -- See 7d1f3a4 for the implementation; this didn't work reliable. 
    
completeTopShading :: ∀ x y . ( WithField ℝ PseudoAffine x, WithField ℝ PseudoAffine y
                              , SimpleSpace (Needle x), SimpleSpace (Needle y) )
                   => x`Shaded`y -> [Shade' (x,y)]
completeTopShading (PlainLeaves plvs) = case ( dualSpaceWitness :: DualNeedleWitness x
                                             , dualSpaceWitness :: DualNeedleWitness y ) of
       (DualSpaceWitness, DualSpaceWitness)
          -> pointsShade's . catMaybes
               $ toInterior . (_topological &&& _untopological) <$> plvs
completeTopShading (DisjointBranches _ bqs)
                     = take 1 . completeTopShading =<< NE.toList bqs
completeTopShading t = case ( dualSpaceWitness :: DualNeedleWitness x
                            , dualSpaceWitness :: DualNeedleWitness y ) of
       (DualSpaceWitness, DualSpaceWitness)
          -> pointsCover's . catMaybes
                . map (toInterior <<< _topological &&& _untopological) $ onlyLeaves t


transferAsNormsDo :: ∀ v . LSpace v => Norm v -> Variance v -> v-+>v
transferAsNormsDo = case dualSpaceWitness :: DualSpaceWitness v of
                      DualSpaceWitness -> \(Norm m) (Norm n) -> n . m

flexTopShading :: ∀ x y f . ( WithField ℝ Manifold x, WithField ℝ Manifold y
                            , SimpleSpace (Needle x), SimpleSpace (Needle y)
                            , Applicative f (->) (->) )
                  => (Shade' (x,y) -> f (x, (Shade' y, LocalLinear x y)))
                      -> x`Shaded`y -> f (x`Shaded`y)
flexTopShading f tr = seq (assert_onlyToplevDisjoint tr)
                    $ recst (dualSpaceWitness::DualNeedleWitness x
                            ,dualSpaceWitness::DualNeedleWitness y
                            ,pseudoAffineWitness::PseudoAffineWitness y)
                            (completeTopShading tr) tr
 where recst _ qsh@(_:_) (DisjointBranches n bqs)
          = undefined -- DisjointBranches n $ NE.zipWith (recst . (:[])) (NE.fromList qsh) bqs
       recst (DualSpaceWitness,DualSpaceWitness,PseudoAffineWitness (SemimanifoldWitness _))
               [sha@(Shade' (_,yc₀) expa₀)] t = fmap fts $ f sha
        where expa'₀ = dualNorm expa₀
              j₀ :: LocalLinear x y
              j₀ = dependence expa'₀
              (_,expay₀) = summandSpaceNorms expa₀
              fts (xc, (Shade' yc expay, jtg)) = unsafeFmapLeaves applδj t
               where Just δyc = yc.-~.yc₀
                     tfm = transferAsNormsDo expay₀ (dualNorm expay)
                     applδj (WithAny y x)
                           = WithAny (yc₀ .+~^ ((tfm $ δy) ^+^ (jtg $ δx) ^+^ δyc)) x
                      where Just δx = x.-~.xc
                            Just δy = y.-~.(yc₀.+~^(j₀ $ δx))
       
       assert_onlyToplevDisjoint, assert_connected :: x`Shaded`y -> ()
       assert_onlyToplevDisjoint (DisjointBranches _ dp) = rnf (assert_connected<$>dp)
       assert_onlyToplevDisjoint t = assert_connected t
       assert_connected (OverlappingBranches _ _ dp)
           = rnf (Hask.foldMap assert_connected<$>dp)
       assert_connected (PlainLeaves _) = ()

flexTwigsShading :: ∀ x y f . ( WithField ℝ Manifold x, WithField ℝ Manifold y
                              , SimpleSpace (Needle x), SimpleSpace (Needle y)
                              , Hask.Applicative f )
                  => (Shade' (x,y) -> f (x, (Shade' y, LocalLinear x y)))
                      -> x`Shaded`y -> f (x`Shaded`y)
flexTwigsShading f = traverseTwigsWithEnvirons locFlex
 where locFlex :: ∀ μ . ((Int, x`Shaded`y), μ) -> f (x`Shaded`y)
       locFlex ((_,lsh), _) = flexTopShading f lsh
                


seekPotentialNeighbours :: ∀ x . (WithField ℝ PseudoAffine x, SimpleSpace (Needle x))
                => ShadeTree x -> x`Shaded`[Int]
seekPotentialNeighbours tree = zipTreeWithList tree
                     $ case snd<$>leavesWithPotentialNeighbours tree of
                         (n:ns) -> n:|ns

leavesWithPotentialNeighbours :: ∀ x . (WithField ℝ PseudoAffine x, SimpleSpace (Needle x))
                => ShadeTree x -> [(x, [Int])]
leavesWithPotentialNeighbours = map (second snd) . go pseudoAffineWitness 0 0 []
 where go :: PseudoAffineWitness x -> Depth -> Int -> [Wall x] -> ShadeTree x
                -> [(x, ([Wall x], [Int]))]
       go (PseudoAffineWitness (SemimanifoldWitness _)) depth n₀ walls (PlainLeaves lvs)
               = [ (x, ( [ wall & wallDistance .~ d
                         | wall <- walls
                         , Just vw <- [toInterior x>>=(.-~.wall^.wallAnchor)]
                         , let d = (wall^.wallNormal)<.>^vw
                         , d < wall^.wallDistance ]
                       , [] ))
                 | x <- lvs ]
       go pw depth n₀ walls (DisjointBranches _ dp)
         = snd (foldl' (\(n₀',prev) br -> ( n₀'+nLeaves br
                                          , prev . (go pw depth n₀' walls br++)))
                        (n₀,id) dp) []
       go pw@(PseudoAffineWitness (SemimanifoldWitness _))
               depth n₀ walls (OverlappingBranches _ (Shade brCtr _) dp)
         = reassemble $ snd
             (foldl' assignWalls (n₀,id) . directionIChoices 0 $ NE.toList dp) []
        where assignWalls :: (Int, DList (x, ([Wall x],[Int])))
                     -> ((Int,(Needle' x, ShadeTree x)), [(Int,(Needle' x, ShadeTree x))])
                     -> (Int, DList (x, ([Wall x], [Int])))
              assignWalls (n₀',prev) ((iDir,(thisDir,br)),otherDirs)
                    = ( n₀'+nLeaves br
                      , prev . (go pw (depth+1) n₀'
                                   (newWalls ++ (updWall<$>walls))
                                   br ++) )
               where newWalls = [ Wall (depth,(iDir,iDir'))
                                       brCtr
                                       (thisDir^-^otherDir)
                                       (1/0)
                                | (iDir',(otherDir,_)) <- otherDirs ]
                     updWall wall = wall & wallDistance %~ min bcDist
                      where Just vbw = brCtr.-~.wall^.wallAnchor
                            bcDist = (wall^.wallNormal)<.>^vbw
              reassemble :: [(x, ([Wall x],[Int]))] -> [(x, ([Wall x],[Int]))]
              reassemble pts = [ (x, (higherWalls, newGroups++deeperGroups))
                               | (x, (allWalls, deeperGroups)) <- pts
                               , let (levelWalls,higherWalls)
                                      = break ((<depth) . fst . _wallID) allWalls
                                     newGroups = concat
                                         [ Map.findWithDefault []
                                              (wall^.wallID._2.swapped) groups
                                         | wall <- levelWalls ]
                               ]
               where groups = ($[]) <$> Map.fromListWith (.)
                               [ (wall^.wallID._2, (i:))
                               | (i,(_, (gsc,_))) <- zip [n₀..] pts
                               , wall <- takeWhile ((==depth) . fst . _wallID) gsc ]






newtype BaryCoords n = BaryCoords { getBaryCoordsTail :: FreeVect n ℝ }

instance (KnownNat n) => AffineSpace (BaryCoords n) where
  type Diff (BaryCoords n) = FreeVect n ℝ
  BaryCoords v .-. BaryCoords w = v ^-^ w
  BaryCoords v .+^ w = BaryCoords $ v ^+^ w
instance (KnownNat n) => Semimanifold (BaryCoords n) where
  type Needle (BaryCoords n) = FreeVect n ℝ
  fromInterior = id
  toInterior = pure
  translateP = Tagged (.+~^)
  (.+~^) = (.+^)
  semimanifoldWitness = undefined
instance (KnownNat n) => PseudoAffine (BaryCoords n) where
  (.-~.) = pure .: (.-.)

getBaryCoords :: BaryCoords n -> ℝ ^ S n
getBaryCoords (BaryCoords (FreeVect bcs)) = FreeVect $ (1 - Arr.sum bcs) `Arr.cons` bcs
  
getBaryCoords' :: BaryCoords n -> [ℝ]
getBaryCoords' (BaryCoords (FreeVect bcs)) = 1 - Arr.sum bcs : Arr.toList bcs

getBaryCoord :: BaryCoords n -> Int -> ℝ
getBaryCoord (BaryCoords (FreeVect bcs)) 0 = 1 - Arr.sum bcs
getBaryCoord (BaryCoords (FreeVect bcs)) i = case bcs Arr.!? i of
    Just a -> a
    _      -> 0

mkBaryCoords :: KnownNat n => ℝ ^ S n -> BaryCoords n
mkBaryCoords (FreeVect bcs) = BaryCoords $ FreeVect (Arr.tail bcs) ^/ Arr.sum bcs

newtype ISimplex n x = ISimplex { iSimplexBCCordEmbed :: Embedding (->) (BaryCoords n) x }




data TriangBuilder n x where
  TriangVerticesSt :: [x] -> TriangBuilder Z x
  TriangBuilder :: Triangulation (S n) x
                    -> [x]
                    -> [(Simplex n x, [x] -> Maybe x)]
                            -> TriangBuilder (S n) x



              
bottomExtendSuitability :: (KnownNat n, WithField ℝ Manifold x)
                => ISimplex (S n) x -> x -> ℝ
bottomExtendSuitability (ISimplex emb) x = case getBaryCoord (emb >-$ x) 0 of
     0 -> 0
     r -> - recip r

optimalBottomExtension :: (KnownNat n, WithField ℝ Manifold x)
                => ISimplex (S n) x -> [x] -> Maybe Int
optimalBottomExtension s xs
      = case filter ((>0).snd)
               $ zipWith ((. bottomExtendSuitability s) . (,)) [0..] xs of
             [] -> empty
             qs -> pure . fst . maximumBy (comparing snd) $ qs




iSimplexSideViews :: ∀ n x . KnownNat n => ISimplex n x -> [ISimplex n x]
iSimplexSideViews = \(ISimplex is)
              -> take (n+1) $ [ISimplex $ rot j is | j<-[0..] ]
 where rot j (Embedding emb proj)
            = Embedding ( emb . mkBaryCoords . freeRotate j     . getBaryCoords        )
                        (       mkBaryCoords . freeRotate (n-j) . getBaryCoords . proj )
       (Tagged n) = theNatN :: Tagged n Int


type FullTriang t n x = TriangT t n x
          (State (Map.Map (SimplexIT t n x) (ISimplex n x)))

type TriangBuild t n x = TriangT t (S n) x
          ( State (Map.Map (SimplexIT t n x) (Metric x, ISimplex (S n) x) ))

doTriangBuild :: KnownNat n => (∀ t . TriangBuild t n x ()) -> [Simplex (S n) x]
doTriangBuild t = runIdentity (fst <$>
  doTriangT (unliftInTriangT (`evalStateT`mempty) t >> simplexITList >>= mapM lookSimplex))








data AutoTriang n x where
  AutoTriang :: { getAutoTriang :: ∀ t . TriangBuild t n x () } -> AutoTriang (S n) x



breakdownAutoTriang :: ∀ n n' x . (KnownNat n', n ~ S n') => AutoTriang n x -> [Simplex n x]
breakdownAutoTriang (AutoTriang t) = doTriangBuild t
         
                    
   
   
   
       

 
partitionsOfFstLength :: Int -> [a] -> [([a],[a])]
partitionsOfFstLength 0 l = [([],l)]
partitionsOfFstLength n [] = []
partitionsOfFstLength n (x:xs) = ( first (x:) <$> partitionsOfFstLength (n-1) xs )
                              ++ ( second (x:) <$> partitionsOfFstLength n xs )

splxVertices :: Simplex n x -> [x]
splxVertices (ZS x) = [x]
splxVertices (x :<| s') = x : splxVertices s'







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
 deriving (Generic, Hask.Functor, Hask.Foldable, Hask.Traversable)
instance (NFData x, Hask.Foldable c, Hask.Foldable b) => NFData (GenericTree c b x) where
  rnf (GenericTree t) = rnf $ toList t
instance (Hask.MonadPlus c) => Semigroup (GenericTree c b x) where
  GenericTree b1 <> GenericTree b2 = GenericTree $ Hask.mplus b1 b2
instance (Hask.MonadPlus c) => Monoid (GenericTree c b x) where
  mempty = GenericTree Hask.mzero
  mappend = (<>)
instance Show (c (x, GenericTree b b x)) => Show (GenericTree c b x) where
  showsPrec p (GenericTree t) = showParen (p>9) $ ('朳':) . showsPrec 10 t
deriving instance Eq (c (x, GenericTree b b x)) => Eq (GenericTree c b x)

-- | @U+6733 CJK UNIFIED IDEOGRAPH tree@.
--  The main purpose of this is to give 'GenericTree' a more concise 'Show' instance.
朳 :: c (x, GenericTree b b x) -> GenericTree c b x
朳 = GenericTree

-- | Imitate the specialised 'ShadeTree' structure with a simpler, generic tree.
onlyNodes :: ∀ x . (WithField ℝ PseudoAffine x, SimpleSpace (Needle x))
                => ShadeTree x -> Trees x
onlyNodes (PlainLeaves []) = GenericTree []
onlyNodes (PlainLeaves ps) = let (ctr,_) = pseudoECM ([]::[x]) $ NE.fromList ps
                             in GenericTree [ (ctr, GenericTree $ (,mempty) <$> ps) ]
onlyNodes (DisjointBranches _ brs) = Hask.foldMap onlyNodes brs
onlyNodes (OverlappingBranches _ (Shade ctr _) brs)
              = GenericTree [ ( fromInterior ctr
                              , Hask.foldMap (Hask.foldMap onlyNodes) brs ) ]


-- | Left (and, typically, also right) inverse of 'fromLeafNodes'.
onlyLeaves :: WithField ℝ PseudoAffine x => ShadeTree x -> [x]
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






constShaded :: y -> ShadeTree x -> x`Shaded`y
constShaded y = unsafeFmapTree (WithAny y<$>) id (shadeWithAny y)

stripShadedUntopological :: (Semimanifold x, SimpleSpace (Needle x))
                   => x`Shaded`y -> ShadeTree x
stripShadedUntopological = unsafeFmapTree (fmap _topological) id shadeWithoutAnything

fmapShaded :: (Semimanifold x, SimpleSpace (Needle x))
                   => (y -> υ) -> (x`Shaded`y) -> (x`Shaded`υ)
fmapShaded f = unsafeFmapTree (fmap $ \(WithAny y x) -> WithAny (f y) x)
                              id
                              (\(Shade yx shx) -> Shade (fmap f yx) shx)

joinShaded :: (Semimanifold x, SimpleSpace (Needle x))
                   => (x`WithAny`y)`Shaded`z -> x`Shaded`(y,z)
joinShaded = unsafeFmapTree (fmap $ \(WithAny z (WithAny y x)) -> WithAny (y,z) x)
                            id
                            (\(Shade (WithAny z (WithAny y x)) shx)
                                  -> Shade (WithAny (y,z) x) shx )

zipTreeWithList :: ShadeTree x -> NonEmpty y -> (x`Shaded`y)
zipTreeWithList tree = go tree . NE.toList . NE.cycle
 where go (PlainLeaves lvs) ys = PlainLeaves $ zipWith WithAny ys lvs
       go (DisjointBranches n brs) ys
             = DisjointBranches n . NE.fromList
                  $ snd (foldl (\(ys',prev) br -> 
                                    (drop (nLeaves br) ys', prev . (go br ys':)) )
                           (ys,id) $ NE.toList brs) []
       go (OverlappingBranches n (Shade xoc shx) brs) ys
             = OverlappingBranches n (Shade (WithAny (head ys) xoc) shx) . NE.fromList
                  $ snd (foldl (\(ys',prev) (DBranch dir (Hourglass top bot))
                        -> case drop (nLeaves top) ys' of
                              ys'' -> ( drop (nLeaves bot) ys''
                                      , prev . (DBranch dir (Hourglass (go top ys')
                                                                       (go bot ys'')):)
                                      ) )
                           (ys,id) $ NE.toList brs) []

-- | This is to 'ShadeTree' as 'Data.Map.Map' is to 'Data.Set.Set'.
type x`Shaded`y = ShadeTree (x`WithAny`y)

stiWithDensity :: ∀ x y . ( WithField ℝ PseudoAffine x, LinearSpace y, Scalar y ~ ℝ
                          , SimpleSpace (Needle x) )
         => x`Shaded`y -> x -> Cℝay y
stiWithDensity (PlainLeaves lvs)
  | [Shade baryc expa :: Shade x] <- pointsShades . catMaybes 
                                       $ toInterior . _topological <$> lvs
       = let nlvs = fromIntegral $ length lvs :: ℝ
             indiShapes = [(Shade pi expa, y) | WithAny y p <- lvs
                                              , Just pi <- [toInterior p]]
         in \x -> let lcCoeffs = [ occlusion psh x | (psh, _) <- indiShapes ]
                      dens = sum lcCoeffs
                  in mkCone dens . linearCombo . zip (snd<$>indiShapes)
                       $ (/dens)<$>lcCoeffs
stiWithDensity (DisjointBranches _ lvs)
           = \x -> foldr1 qGather $ (`stiWithDensity`x)<$>lvs
 where qGather (Cℝay 0 _) o = o
       qGather o _ = o
stiWithDensity (OverlappingBranches n (Shade (WithAny _ bc) extend) brs)
           = ovbSWD (dualSpaceWitness, pseudoAffineWitness)
 where ovbSWD :: (DualNeedleWitness x, PseudoAffineWitness x) -> x -> Cℝay y
       ovbSWD (DualSpaceWitness, PseudoAffineWitness (SemimanifoldWitness _)) x
                     = case toInterior x>>=(.-~.bc) of
           Just v
             | dist² <- normSq ε v
             , dist² < 9
             , att <- exp(1/(dist²-9)+1/9)
               -> qGather att $ fmap ($ x) downPrepared
           _ -> coneTip
       ε = dualNorm' extend :: Norm (Needle x)
       downPrepared = dp =<< brs
        where dp (DBranch _ (Hourglass up dn))
                 = fmap stiWithDensity $ up:|[dn]
       qGather att contribs = mkCone (att*dens)
                 $ linearCombo [(v, d/dens) | Cℝay d v <- NE.toList contribs]
        where dens = sum (hParamCℝay <$> contribs)

stiAsIntervalMapping :: (x ~ ℝ, y ~ ℝ)
            => x`Shaded`y -> [(x, ((y, Diff y), LinearMap ℝ x y))]
stiAsIntervalMapping = twigsWithEnvirons >=> pure.snd.fst >=> completeTopShading >=> pure.
             \(Shade' (xloc, yloc) shd)
                 -> ( xloc, ( (yloc, recip $ shd|$|(0,1))
                            , dependence (dualNorm shd) ) )

smoothInterpolate :: ∀ x y . ( WithField ℝ Manifold x, LinearSpace y, Scalar y ~ ℝ
                             , SimpleSpace (Needle x) )
             => NonEmpty (x,y) -> x -> y
smoothInterpolate = si boundarylessWitness
 where si :: BoundarylessWitness x -> NonEmpty (x,y) -> x -> y
       si BoundarylessWitness l = \x ->
             case ltr x of
               Cℝay 0 _ -> defy
               Cℝay _ y -> y
        where defy = linearCombo [(y, 1/n) | WithAny y _ <- l']
              n = fromIntegral $ length l'
              l' = (uncurry WithAny . swap) <$> NE.toList l
              ltr = stiWithDensity $ fromLeafPoints l'


spanShading :: ∀ x y . ( WithField ℝ Manifold x, WithField ℝ Manifold y
                       , SimpleSpace (Needle x), SimpleSpace (Needle y) )
          => (Shade x -> Shade y) -> ShadeTree x -> x`Shaded`y
spanShading f = unsafeFmapTree addYs id addYSh
 where addYs :: NonEmpty x -> NonEmpty (x`WithAny`y)
       addYs l = foldr (NE.<|) (fmap (WithAny $ fromInterior ymid) l     )
                               (fmap (`WithAny` fromInterior xmid) yexamp)
          where [xsh@(Shade xmid _)] = pointsCovers . catMaybes . toList
                                           $ toInterior<$>l
                Shade ymid yexpa = f xsh
                yexamp = [ ymid .+~^ σ*^δy
                         | δy <- varianceSpanningSystem yexpa, σ <- [-1,1] ]
       addYSh :: Shade x -> Shade (x`WithAny`y)
       addYSh xsh = shadeWithAny (fromInterior . _shadeCtr $ f xsh) xsh
                      


coneTip :: (AdditiveGroup v) => Cℝay v
coneTip = Cℝay 0 zeroV

mkCone :: AdditiveGroup v => ℝ -> v -> Cℝay v
mkCone 0 _ = coneTip
mkCone h v = Cℝay h v


foci :: [a] -> [(a,[a])]
foci [] = []
foci (x:xs) = (x,xs) : fmap (second (x:)) (foci xs)
       
fociNE :: NonEmpty a -> NonEmpty (a,[a])
fociNE (x:|xs) = (x,xs) :| fmap (second (x:)) (foci xs)
       

(.:) :: (c->d) -> (a->b->c) -> a->b->d 
(.:) = (.) . (.)




class HasFlatView f where
  type FlatView f x
  flatView :: f x -> FlatView f x
  superFlatView :: f x -> [[x]]
      
instance HasFlatView Sawbones where
  type FlatView Sawbones x = [([x],[[x]])]
  flatView (Sawbones t1 t2 d1 d2) = [(t1[],[d1]), (t2[],[d2])]
  superFlatView = foldMap go . flatView
   where go (t,ds) = t : ds

instance HasFlatView Sawboneses where
  type FlatView Sawboneses x = [([x],[[x]])]
  flatView (SingleCut (Sawbones t1 t2 d1 d2)) = [(t1[],[d1]), (t2[],[d2])]
  flatView (Sawboneses (DBranches bs)) = 
        [ (m[], NE.toList ds >>= \(DBranch _ (Hourglass u' l')) -> [u',l'])
        | (DBranch _ (Hourglass u l)) <- NE.toList bs
        , (DustyEdges m (DBranches ds)) <- [u,l]
        ]
  superFlatView = foldMap go . flatView
   where go (t,ds) = t : ds





