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
       , ShadeTree, fromLeafPoints, fromLeafPoints_, onlyLeaves, onlyLeaves_
       , indexShadeTree, treeLeaf, positionIndex
       -- ** View helpers
       , entireTree, onlyNodes, trunkBranches, nLeaves, treeDepth
       -- ** Auxiliary types
       , SimpleTree, Trees, NonEmptyTree, GenericTree(..), 朳
       -- * Misc
       , HasFlatView(..), shadesMerge
       , allTwigs, twigsWithEnvirons, Twig, TwigEnviron, seekPotentialNeighbours
       , completeTopShading, flexTwigsShading, traverseTrunkBranchChoices
       , Shaded(..), fmapShaded
       , constShaded, zipTreeWithList
       , stiAsIntervalMapping, spanShading
       , DBranch, DBranch'(..), Hourglass(..)
       , unsafeFmapTree
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

import Data.Manifold.Shade
import Data.Manifold.Types
import Data.Manifold.Types.Primitive ((^), empty)
import Data.Manifold.PseudoAffine
import Data.Manifold.Riemannian
import Data.Manifold.Atlas
import Data.Function.Affine
    
import Data.Embedding

import Control.Lens (Lens', (^.), (.~), (%~), (&), _2, swapped)
import Control.Lens.TH

import qualified Prelude as Hask hiding(foldl, sum, sequence)
import qualified Control.Applicative as Hask
import qualified Control.Monad       as Hask hiding(forM_, sequence)
import Data.Functor.Identity
import Control.Monad.Trans.State
import Control.Monad.Trans.Writer
import Control.Monad.Trans.List
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

import Development.Placeholders


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
            deriving (Generic, Hask.Functor, Hask.Foldable, Hask.Traversable, Show)
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

type ShadeTree x = x`Shaded`()

data Shaded x y = PlainLeaves [(x,y)]
                | DisjointBranches !LeafCount (NonEmpty (x`Shaded`y))
                | OverlappingBranches !LeafCount !(Shade x) (NonEmpty (DBranch x y))
  deriving (Generic, Hask.Functor, Hask.Foldable, Hask.Traversable)
deriving instance ( WithField ℝ PseudoAffine x, Show x
                  , Show (Interior x), Show (Needle' x), Show (Metric' x) )
             => Show (ShadeTree x)
           
data DBranch' x c = DBranch { boughDirection :: !(Needle' x)
                            , boughContents :: !(Hourglass c) }
  deriving (Generic, Hask.Functor, Hask.Foldable, Hask.Traversable)
type DBranch x y = DBranch' x (x`Shaded`y)
deriving instance ( WithField ℝ PseudoAffine x, Show (Needle' x), Show c )
             => Show (DBranch' x c)

newtype DBranches' x c = DBranches (NonEmpty (DBranch' x c))
  deriving (Generic, Hask.Functor, Hask.Foldable, Hask.Traversable)
deriving instance ( WithField ℝ PseudoAffine x, Show (Needle' x), Show c )
             => Show (DBranches' x c)

-- ^ /Unsafe/: this assumes the direction information of both containers to be equivalent.
instance (Semigroup c) => Semigroup (DBranches' x c) where
  DBranches b1 <> DBranches b2 = DBranches $ NE.zipWith (\(DBranch d1 c1) (DBranch _ c2)
                                                              -> DBranch d1 $ c1<>c2 ) b1 b2



trunkBranches :: x`Shaded`y -> NonEmpty (LeafIndex, x`Shaded`y)
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
               => [DBranch x y]
                 -> [ ( (Needle' x, x`Shaded`y)
                      ,[(Needle' x, x`Shaded`y)] ) ]
directionChoices = map (snd *** map snd) . directionIChoices 0

directionIChoices :: (WithField ℝ PseudoAffine x, AdditiveGroup (Needle' x))
               => Int -> [DBranch x y]
                 -> [ ( (Int, (Needle' x, x`Shaded`y))
                      ,[(Int, (Needle' x, x`Shaded`y))] ) ]
directionIChoices _ [] = []
directionIChoices i₀ (DBranch ѧ (Hourglass t b) : hs)
         =  ( top, bot : map fst uds )
          : ( bot, top : map fst uds )
          : map (second $ (top:) . (bot:)) uds
 where top = (i₀,(ѧ,t))
       bot = (i₀+1,(negateV ѧ,b))
       uds = directionIChoices (i₀+2) hs

traverseDirectionChoices :: ( AdditiveGroup (Needle' x), Hask.Applicative f )
               => (    (Int, (Needle' x, x`Shaded`y))
                    -> [(Int, (Needle' x, x`Shaded`y))]
                    -> f (x`Shaded`z) )
                 -> [DBranch x y]
                 -> f [DBranch x z]
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



traverseTrunkBranchChoices :: Hask.Applicative f
               => ( (Int, x`Shaded`y) -> x`Shaded`y -> f (x`Shaded`z) )
                 -> x`Shaded`y -> f (x`Shaded`z)
traverseTrunkBranchChoices f (OverlappingBranches n sh bs)
        = OverlappingBranches n sh . NE.fromList <$> go 0 id (NE.toList bs)
 where go _ _ [] = pure []
       go i₀ prbs (tbs@(DBranch v (Hourglass τ β)) : dbs)
        = (:) . DBranch v <$>
            (Hourglass <$> (f (i₀, τ) . OverlappingBranches (n-nτ) sh
                            . NE.fromList . prbs $ DBranch v (Hourglass hole β) : dbs)
                       <*> (f (i₀+nτ, β) . OverlappingBranches (n-nβ) sh
                            . NE.fromList . prbs $ DBranch v (Hourglass τ hole) : dbs))
            <*> go (i₀+nτ+nβ) (prbs . (tbs:)) dbs
        where [nτ, nβ] = nLeaves<$>[τ,β]
              hole = PlainLeaves []


indexDBranches :: NonEmpty (DBranch x y) -> NonEmpty (DBranch' x (Int, x`Shaded`y))
indexDBranches (DBranch d (Hourglass t b) :| l) -- this could more concisely be written as a traversal
              = DBranch d (Hourglass (0,t) (nt,b)) :| ixDBs (nt + nb) l
 where nt = nLeaves t; nb = nLeaves b
       ixDBs _ [] = []
       ixDBs i₀ (DBranch δ (Hourglass τ β) : l)
               = DBranch δ (Hourglass (i₀,τ) (i₀+nτ,β)) : ixDBs (i₀ + nτ + nβ) l
        where nτ = nLeaves τ; nβ = nLeaves β

instance (NFData x, NFData (Needle' x), NFData y) => NFData (x`Shaded`y) where
  rnf (PlainLeaves xs) = rnf xs
  rnf (DisjointBranches n bs) = n `seq` rnf (NE.toList bs)
  rnf (OverlappingBranches n sh bs) = n `seq` sh `seq` rnf (NE.toList bs)
instance (NFData x, NFData (Needle' x), NFData y) => NFData (DBranch x y)
  

-- | WRT union.
instance (WithField ℝ Manifold x, SimpleSpace (Needle x)) => Semigroup (ShadeTree x) where
  PlainLeaves [] <> t = t
  t <> PlainLeaves [] = t
  t <> s = fromLeafPoints $ onlyLeaves_ t ++ onlyLeaves_ s
           -- Could probably be done more efficiently
  sconcat = mconcat . NE.toList
instance (WithField ℝ Manifold x, SimpleSpace (Needle x)) => Monoid (ShadeTree x) where
  mempty = PlainLeaves []
  mappend = (<>)
  mconcat l = case filter ne l of
               [] -> mempty
               [t] -> t
               l' -> fromLeafPoints $ onlyLeaves_ =<< l'
   where ne (PlainLeaves []) = False; ne _ = True


-- | Build a quite nicely balanced tree from a cloud of points, on any real manifold.
-- 
--   Example: https://nbviewer.jupyter.org/github/leftaroundabout/manifolds/blob/master/test/Trees-and-Webs.ipynb#pseudorandomCloudTree
-- 
-- <<images/examples/simple-2d-ShadeTree.png>>
fromLeafPoints :: ∀ x. (WithField ℝ Manifold x, SimpleSpace (Needle x))
                        => [x] -> ShadeTree x
fromLeafPoints = fromLeafPoints_ . map (,())

fromLeafPoints_ :: ∀ x y. (WithField ℝ Manifold x, SimpleSpace (Needle x))
                        => [(x,y)] -> x`Shaded`y
fromLeafPoints_ = fromLeafPoints' sShIdPartition


-- | The leaves of a shade tree are numbered. For a given index, this function
--   attempts to find the leaf with that ID, within its immediate environment.
indexShadeTree :: ∀ x y . x`Shaded`y -> Int -> Either Int ([x`Shaded`y], (x,y))
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

treeLeaf :: ∀ x y f . Hask.Functor f
        => Int -> (y -> f y) -> x`Shaded`y -> Either Int (f (x`Shaded`y))
treeLeaf i _ _
    | i<0        = Left i
treeLeaf i f sh@(PlainLeaves lvs) = case length lvs of
  n | i<n
    , (pre, (x,node):post) <- splitAt i lvs
              -> Right . fmap (PlainLeaves . (pre++) . (:post) . (x,)) $ f node
    | otherwise -> Left $ i-n
treeLeaf i f (DisjointBranches n _)
    | i>=n   = Left $ i-n
treeLeaf i f (DisjointBranches n (br:|[]))
        = fmap (DisjointBranches n . pure) <$> treeLeaf i f br
treeLeaf i f (DisjointBranches n (br:|br':brs))
        = case treeLeaf i f br of
            Left overshoot -> fmap (\(DisjointBranches _ (br'':|brs'))
                                   -> DisjointBranches n (br:|br'':brs'))
                  <$> treeLeaf overshoot f
                     (DisjointBranches (n-nLeaves br) $ br':|brs)
            Right done -> Right $ DisjointBranches n . (:|br':brs) <$> done
treeLeaf i f (OverlappingBranches n extend (br@(DBranch dir (Hourglass t b)):|brs))
    | i<nt       = fmap (OverlappingBranches n extend
                         . (:|brs) . DBranch dir . (`Hourglass`b))
                    <$> treeLeaf i f t
    | i<nt+nb    = fmap (OverlappingBranches n extend
                         . (:|brs) . DBranch dir . ( Hourglass t))
                    <$> treeLeaf (i-nt) f b
    | br':brs' <- brs
                 = fmap (\(OverlappingBranches _ _ (br'':|brs''))
                         -> OverlappingBranches n extend $ br:|br'':brs'')
                    <$> treeLeaf (i-nt-nb) f (OverlappingBranches n extend $ br':|brs')
    | otherwise  = Left $ i - nt - nb
 where [nt,nb] = nLeaves<$>[t,b]


-- | “Inverse indexing” of a tree. This is roughly a nearest-neighbour search,
--   but not guaranteed to give the correct result unless evaluated at the
--   precise position of a tree leaf.
positionIndex :: ∀ x y . (WithField ℝ Manifold x, SimpleSpace (Needle x))
       => Maybe (Metric x)   -- ^ For deciding (at the lowest level) what “close” means;
                             --   this is optional for any tree of depth >1.
        -> (x`Shaded`y)      -- ^ The tree to index into
        -> x                 -- ^ Position to look up
        -> Maybe (Int, ([x`Shaded`y], (x,y)))
                   -- ^ Index of the leaf near to the query point, the “path” of
                   --   environment trees leading down to its position (in decreasing
                   --   order of size), and actual position+info of the found node.
positionIndex (Just m) sh@(PlainLeaves lvs) x
        = case catMaybes [ ((i,p),) . normSq m <$> fst p.-~.x
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




fromLeafPoints' :: ∀ x y. (WithField ℝ Manifold x, SimpleSpace (Needle x)) =>
    (Shade x -> [(x,y)] -> NonEmpty (DBranch' x [(x,y)])) -> [(x,y)] -> x`Shaded`y
fromLeafPoints' sShIdPart = go boundarylessWitness mempty
 where go :: BoundarylessWitness x -> Metric' x -> [(x,y)] -> x`Shaded`y
       go bw@BoundarylessWitness preShExpa
            = \xs -> case pointsShades' (scaleNorm (1/3) preShExpa) xs of
                     [] -> PlainLeaves []
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
                                 
              reduce :: Shade x -> NonEmpty (DBranch' x [(x,y)])
                                      -> Maybe (NonEmpty (DBranch' x [(x,y)]))
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
        => Interior x -> [(x,y)] -> NonEmpty (DBranch' x [(x,y)])
                                 -> NonEmpty (DBranch' x [(x,y)])
sShIdPartition' c xs st
           = foldr (\(p,y) -> let (i,h) = ssi p
                          in asList $ update_nth (\(DBranch d c)
                                                    -> DBranch d (oneBulb h ((p,y):) c))
                                      i )
                   st xs
 where ssi = subshadeId' (fromInterior c) (boughDirection<$>st)
sShIdPartition :: (WithField ℝ PseudoAffine x, SimpleSpace (Needle x))
                    => Shade x -> [(x,y)] -> NonEmpty (DBranch' x [(x,y)])
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


trunks :: ∀ x y . (WithField ℝ PseudoAffine x, SimpleSpace (Needle x))
                  => x`Shaded`y -> [Shade x]
trunks t = case (pseudoAffineWitness :: PseudoAffineWitness x, t) of
  (PseudoAffineWitness (SemimanifoldWitness BoundarylessWitness), PlainLeaves lvs)
                                    -> pointsCovers . catMaybes $ toInterior.fst<$>lvs
  (_, DisjointBranches _ brs)       -> Hask.foldMap trunks brs
  (_, OverlappingBranches _ sh _)   -> [sh]


nLeaves :: x`Shaded`y -> Int
nLeaves (PlainLeaves lvs) = length lvs
nLeaves (DisjointBranches n _) = n
nLeaves (OverlappingBranches n _ _) = n

treeDepth :: x`Shaded`y -> Int
treeDepth (PlainLeaves lvs) = 0
treeDepth (DisjointBranches _ brs) = 1 + maximum (treeDepth<$>brs)
treeDepth (OverlappingBranches _ _ brs)
     = 1 + maximum (maximum . fmap treeDepth<$>brs)





overlappingBranches :: Shade x -> NonEmpty (DBranch x y) -> x`Shaded`y
overlappingBranches shx brs = OverlappingBranches n shx brs
 where n = sum $ fmap (sum . fmap nLeaves) brs

unsafeFmapLeaves_ :: (x -> x) -> x`Shaded`y -> x`Shaded`y
unsafeFmapLeaves_ = unsafeFmapLeaves . first

unsafeFmapLeaves :: ((x,y) -> (x,y')) -> x`Shaded`y -> x`Shaded`y'
unsafeFmapLeaves f (PlainLeaves lvs) = PlainLeaves $ fmap f lvs
unsafeFmapLeaves f (DisjointBranches n brs)
                 = DisjointBranches n $ unsafeFmapLeaves f <$> brs
unsafeFmapLeaves f (OverlappingBranches n sh brs)
                  = OverlappingBranches n sh $ fmap (unsafeFmapLeaves f) <$> brs

unsafeFmapTree :: (NonEmpty (x,y) -> NonEmpty (ξ,υ))
               -> (Needle' x -> Needle' ξ)
               -> (Shade x -> Shade ξ)
               -> x`Shaded`y -> ξ`Shaded`υ
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




type Twig x y = (Int, x`Shaded`y)
type TwigEnviron x y = [Twig x y]

allTwigs :: ∀ x y . WithField ℝ PseudoAffine x => x`Shaded`y -> [Twig x y]
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
twigsWithEnvirons :: ∀ x y. (WithField ℝ Manifold x, SimpleSpace (Needle x))
    => x`Shaded`y -> [(Twig x y, TwigEnviron x y)]
twigsWithEnvirons = execWriter . traverseTwigsWithEnvirons (writer . (snd.fst&&&pure))

traverseTwigsWithEnvirons :: ∀ x y f .
            (WithField ℝ PseudoAffine x, SimpleSpace (Needle x), Hask.Applicative f)
    => ( (Twig x y, TwigEnviron x y) -> f (x`Shaded`y) ) -> x`Shaded`y -> f (x`Shaded`y)
traverseTwigsWithEnvirons f = fst . go pseudoAffineWitness [] . (0,)
 where go :: PseudoAffineWitness x -> TwigEnviron x y -> Twig x y -> (f (x`Shaded`y), Bool)
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
       
       twigProximæ :: PseudoAffineWitness x -> Interior x -> x`Shaded`y -> TwigEnviron x y
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
       
       twigsaveTrim :: (DBranch x y -> TwigEnviron x y) -> x`Shaded`y -> TwigEnviron x y
       twigsaveTrim f ct@(OverlappingBranches _ _ dbs)
                 = case Hask.mapM (\(i₀,dbr) -> noLeaf $ first(+i₀)<$>f dbr)
                                 $ NE.zip ioffs dbs of
                      Just pqe -> Hask.fold pqe
                      _        -> [(0,ct)]
        where noLeaf [(_,PlainLeaves _)] = empty
              noLeaf bqs = pure bqs
              ioffs = NE.scanl (\i -> (+i) . sum . fmap nLeaves . toList) 0 dbs
       
       purgeRemotes :: (Twig x y, TwigEnviron x y) -> (Twig x y, TwigEnviron x y)
       purgeRemotes = id -- See 7d1f3a4 for the implementation; this didn't work reliable. 
    
completeTopShading :: ∀ x y . ( WithField ℝ PseudoAffine x, WithField ℝ PseudoAffine y
                              , SimpleSpace (Needle x), SimpleSpace (Needle y) )
                   => x`Shaded`y -> [Shade' (x,y)]
completeTopShading (PlainLeaves plvs) = case ( dualSpaceWitness :: DualNeedleWitness x
                                             , dualSpaceWitness :: DualNeedleWitness y ) of
       (DualSpaceWitness, DualSpaceWitness)
          -> pointsShade's . catMaybes
               $ toInterior <$> plvs
completeTopShading (DisjointBranches _ bqs)
                     = take 1 . completeTopShading =<< NE.toList bqs
completeTopShading t = case ( dualSpaceWitness :: DualNeedleWitness x
                            , dualSpaceWitness :: DualNeedleWitness y ) of
       (DualSpaceWitness, DualSpaceWitness)
          -> pointsCover's . catMaybes
                . map toInterior $ onlyLeaves t


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
                     applδj (x,y)
                           = (x, yc₀ .+~^ ((tfm $ δy) ^+^ (jtg $ δx) ^+^ δyc))
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
                


seekPotentialNeighbours :: ∀ x y . (WithField ℝ PseudoAffine x, SimpleSpace (Needle x))
                => x`Shaded`y -> x`Shaded`(y,[Int])
seekPotentialNeighbours tree = zipTreeWithList tree
                     $ case snd<$>leavesWithPotentialNeighbours tree of
                         (n:ns) -> n:|ns

leavesWithPotentialNeighbours :: ∀ x y
            . (WithField ℝ PseudoAffine x, SimpleSpace (Needle x))
                => x`Shaded`y -> [((x,y), [Int])]
leavesWithPotentialNeighbours = map (second snd) . go pseudoAffineWitness 0 0 []
 where go :: PseudoAffineWitness x -> Depth -> Int -> [Wall x] -> x`Shaded`y
                -> [((x,y), ([Wall x], [Int]))]
       go (PseudoAffineWitness (SemimanifoldWitness _)) depth n₀ walls (PlainLeaves lvs)
               = [ ((x,y), ( [ wall & wallDistance .~ d
                         | wall <- walls
                         , Just vw <- [toInterior x>>=(.-~.wall^.wallAnchor)]
                         , let d = (wall^.wallNormal)<.>^vw
                         , d < wall^.wallDistance ]
                       , [] ))
                 | (x,y) <- lvs ]
       go pw depth n₀ walls (DisjointBranches _ dp)
         = snd (foldl' (\(n₀',prev) br -> ( n₀'+nLeaves br
                                          , prev . (go pw depth n₀' walls br++)))
                        (n₀,id) dp) []
       go pw@(PseudoAffineWitness (SemimanifoldWitness _))
               depth n₀ walls (OverlappingBranches _ (Shade brCtr _) dp)
         = reassemble $ snd
             (foldl' assignWalls (n₀,id) . directionIChoices 0 $ NE.toList dp) []
        where assignWalls :: (Int, DList ((x,y), ([Wall x],[Int])))
                     -> ((Int,(Needle' x, x`Shaded`y)), [(Int,(Needle' x, x`Shaded`y))])
                     -> (Int, DList ((x,y), ([Wall x], [Int])))
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
              reassemble :: [((x,y), ([Wall x],[Int]))] -> [((x,y), ([Wall x],[Int]))]
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

type LeafyTree x y = GenericTree [] (ListT (Either y)) x
    
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
                             in GenericTree [ (ctr, GenericTree $ (,mempty).fst <$> ps) ]
onlyNodes (DisjointBranches _ brs) = Hask.foldMap onlyNodes brs
onlyNodes (OverlappingBranches _ (Shade ctr _) brs)
              = GenericTree [ ( fromInterior ctr
                              , Hask.foldMap (Hask.foldMap onlyNodes) brs ) ]

entireTree :: ∀ x y . (WithField ℝ PseudoAffine x, SimpleSpace (Needle x))
              => x`Shaded`y -> LeafyTree x y
entireTree (PlainLeaves lvs)
    = let (ctr,_) = pseudoECM ([]::[x]) $ NE.fromList lvs
      in  GenericTree [ (ctr, GenericTree . ListT $ Right
                                [ (x, GenericTree . lift $ Left y)
                                | (x,y)<-lvs ] )
                      ]
entireTree (DisjointBranches _ brs)
    = GenericTree [ (x, GenericTree subt)
                  | GenericTree sub <- NE.toList $ fmap entireTree brs
                  , (x, GenericTree subt) <- sub ]
entireTree (OverlappingBranches _ (Shade ctr _) brs)
    = GenericTree [ ( fromInterior ctr
                    , GenericTree . ListT . Right
                       $ Hask.foldMap (Hask.foldMap $ treeBranches . entireTree) brs ) ]


-- | Left (and, typically, also right) inverse of 'fromLeafNodes'.
onlyLeaves_ :: WithField ℝ PseudoAffine x => ShadeTree x -> [x]
onlyLeaves_ = map fst . onlyLeaves

onlyLeaves :: WithField ℝ PseudoAffine x => x`Shaded`y -> [(x,y)]
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






constShaded :: y -> x`Shaded`y₀ -> x`Shaded`y
constShaded y = unsafeFmapTree (fmap . second $ const y) id id

fmapShaded :: (Semimanifold x, SimpleSpace (Needle x))
                   => (y -> υ) -> (x`Shaded`y) -> (x`Shaded`υ)
fmapShaded f = unsafeFmapTree (fmap $ second f) id id

zipTreeWithList :: x`Shaded`w -> NonEmpty y -> (x`Shaded`(w,y))
zipTreeWithList tree = go tree . NE.toList . NE.cycle
 where go (PlainLeaves lvs) ys = PlainLeaves $ zipWith (\(x,w) y -> (x,(w,y))) lvs ys
       go (DisjointBranches n brs) ys
             = DisjointBranches n . NE.fromList
                  $ snd (foldl (\(ys',prev) br -> 
                                    (drop (nLeaves br) ys', prev . (go br ys':)) )
                           (ys,id) $ NE.toList brs) []
       go (OverlappingBranches n shx brs) ys
             = OverlappingBranches n shx . NE.fromList
                  $ snd (foldl (\(ys',prev) (DBranch dir (Hourglass top bot))
                        -> case drop (nLeaves top) ys' of
                              ys'' -> ( drop (nLeaves bot) ys''
                                      , prev . (DBranch dir (Hourglass (go top ys')
                                                                       (go bot ys'')):)
                                      ) )
                           (ys,id) $ NE.toList brs) []

stiWithDensity :: ∀ x y . ( WithField ℝ PseudoAffine x, LinearSpace y, Scalar y ~ ℝ
                          , SimpleSpace (Needle x) )
         => x`Shaded`y -> x -> Cℝay y
stiWithDensity (PlainLeaves lvs)
  | [Shade baryc expa :: Shade x] <- pointsShades . catMaybes 
                                       $ toInterior . fst <$> lvs
       = let nlvs = fromIntegral $ length lvs :: ℝ
             indiShapes = [(Shade pi expa, y) | (p,y) <- lvs
                                              , Just pi <- [toInterior p]]
         in \x -> let lcCoeffs = [ occlusion psh x | (psh, _) <- indiShapes ]
                      dens = sum lcCoeffs
                  in mkCone dens . linearCombo . zip (snd<$>indiShapes)
                       $ (/dens)<$>lcCoeffs
stiWithDensity (DisjointBranches _ lvs)
           = \x -> foldr1 qGather $ (`stiWithDensity`x)<$>lvs
 where qGather (Cℝay 0 _) o = o
       qGather o _ = o
stiWithDensity (OverlappingBranches n (Shade bc extend) brs)
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


spanShading :: ∀ x y . ( WithField ℝ Manifold x, WithField ℝ Manifold y
                       , SimpleSpace (Needle x), SimpleSpace (Needle y) )
          => (Shade x -> Shade y) -> ShadeTree x -> x`Shaded`y
spanShading f = unsafeFmapTree (addYs . fmap fst) id id
 where addYs :: NonEmpty x -> NonEmpty (x,y)
       addYs l = foldr (NE.<|) (fmap (,fromInterior ymid) l     )
                               (fmap (fromInterior xmid,) yexamp)
          where [xsh@(Shade xmid _)] = pointsCovers . catMaybes . toList
                                           $ toInterior<$>l
                Shade ymid yexpa = f xsh
                yexamp = [ ymid .+~^ σ*^δy
                         | δy <- varianceSpanningSystem yexpa, σ <- [-1,1] ]
                      


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





