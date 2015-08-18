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
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE LiberalTypeSynonyms        #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE DataKinds                  #-}


module Data.Manifold.TreeCover (
       -- * Shades 
         Shade, shadeCtr, shadeExpanse, fullShade, pointsShades
       -- * Shade trees
       , ShadeTree(..), fromLeafPoints
       -- * Simple view helpers
       , onlyNodes, onlyLeaves
       -- ** Auxiliary types
       , SimpleTree, Trees, NonEmptyTree, GenericTree(..)
       -- * Misc
       , sShSaw, chainsaw, HasFlatView(..)
       -- ** Triangulation-builders
       , TriangBuild, doTriangBuild, singleFullSimplex, autoglueTriangulation
       , AutoTriang, elementaryTriang, breakdownAutoTriang
    ) where


import Data.List hiding (filter, all, elem, sum)
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
import Data.LinearMap
import Data.LinearMap.HerMetric
import Data.LinearMap.Category
import Data.AffineSpace
import Data.Basis
import Data.Complex hiding (magnitude)
import Data.Void
import Data.Tagged
import Data.Proxy

import Data.SimplicialComplex
import Data.Manifold.Types
import Data.Manifold.Types.Primitive ((^))
import Data.Manifold.PseudoAffine
    
import Data.Embedding
import Data.CoNat

import qualified Prelude as Hask hiding(foldl, sum, sequence)
import qualified Control.Applicative as Hask
import qualified Control.Monad       as Hask hiding(forM_, sequence)
import Data.Functor.Identity
import Control.Monad.Trans.State
import Control.Monad.Trans.Writer
import Control.Monad.Trans.Class
import qualified Data.Foldable       as Hask
import Data.Foldable (all, elem, toList, sum)
import qualified Data.Traversable as Hask
import Data.Traversable (forM)

import qualified Numeric.LinearAlgebra.HMatrix as HMat

import Control.Category.Constrained.Prelude hiding
     ((^), all, elem, sum, forM, Foldable(..), Traversable)
import Control.Arrow.Constrained
import Control.Monad.Constrained hiding (forM)
import Data.Foldable.Constrained

import GHC.Generics (Generic)


-- | Possibly / Partially / asymPtotically singular metric.
data PSM x = PSM {
       psmExpanse :: !(Metric' x)
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
                     , shadeExpanse :: !(Metric' x) }

instance (AffineManifold x) => Semimanifold (Shade x) where
  type Needle (Shade x) = Diff x
  Shade c e .+~^ v = Shade (c.+^v) e
  Shade c e .-~^ v = Shade (c.-^v) e

fullShade :: WithField ℝ Manifold x => x -> Metric' x -> Shade x
fullShade ctr expa = Shade ctr expa

subshadeId' :: WithField ℝ Manifold x
                   => x -> NonEmpty (DualSpace (Needle x)) -> x -> (Int, HourglassBulb)
subshadeId' c expvs x = case x .-~. c of
    Option (Just v) -> let (iu,vl) = maximumBy (comparing $ abs . snd)
                                      $ zip [0..] (map (v <.>^) $ NE.toList expvs)
                       in (iu, if vl>0 then UpperBulb else LowerBulb)
    _ -> (-1, error "Trying to obtain the subshadeId of a point not actually included in the shade.")

subshadeId :: WithField ℝ Manifold x => Shade x -> x -> (Int, HourglassBulb)
subshadeId (Shade c expa) = subshadeId' c . NE.fromList $ eigenCoSpan expa
                 


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

pointsShades' :: WithField ℝ Manifold x => Metric' x -> [x] -> [([x], Shade x)]
pointsShades' _ [] = []
pointsShades' minExt ps = case expa of 
                           Option (Just e) -> (ps, fullShade ctr e)
                                              : pointsShades' minExt unreachable
                           _ -> pointsShades' minExt inc'd
                                  ++ pointsShades' minExt unreachable
 where (ctr,(inc'd,unreachable)) = pseudoECM $ NE.fromList ps
       expa = ( (^+^minExt) . (^/ fromIntegral(length ps)) . sumV . map projector' )
              <$> mapM (.-~.ctr) ps
       

-- | Attempt to reduce the shades to fewer (ideally, a single one), which still cover
--   at least the same area.
shadesMerge :: WithField ℝ Manifold x
                 => ℝ -- ^ &#x201c;Fuzz factor&#x201d; &#x2014; how far two shades can be apart to still be merged.
                 -> [Shade x]
                 -> [Shade x]
shadesMerge fuzz (sh₁@(Shade c₁ e₁) : shs) = case extractJust tryMerge shs of
          (Just mg₁, shs') -> shadesMerge fuzz
                                $ shs'++[mg₁] -- Append to end to prevent undue weighting
                                              -- of first shade and its mergers.
          (_, shs') -> sh₁ : shadesMerge fuzz shs' 
 where tryMerge (Shade c₂ e₂)
           | Option (Just v) <- c₁.-~.c₂
           , Option (Just v') <- c₂.-~.c₁
           , [e₁',e₂'] <- recipMetric<$>[e₁, e₂] 
           , b₁ <- metric e₂' v
           , b₂ <- metric e₁' v
           , b₁==0 || b₂==0 || fuzz/b₁ + fuzz/b₂ > 1
                  = Just $ let cc = c₂ .+~^ v ^/ 2
                               Option (Just cv₁) = c₁.-~.cc
                               Option (Just cv₂) = c₂.-~.cc
                           in Shade cc . sumV $ [e₁, e₂] ++ projector'<$>[cv₁, cv₂] 
           | otherwise  = Nothing
shadesMerge _ shs = shs

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
  


instance (NFData x, NFData (DualSpace (Needle x))) => NFData (ShadeTree x) where
  rnf (PlainLeaves xs) = rnf xs
  rnf (DisjointBranches n bs) = n `seq` rnf (NE.toList bs)
  rnf (OverlappingBranches n sh bs) = n `seq` sh `seq` rnf (NE.toList bs)
instance (NFData x, NFData (DualSpace (Needle x))) => NFData (DBranch x)
  
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
 where go :: Metric' x -> [x] -> ShadeTree x
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


sShIdPartition' :: WithField ℝ Manifold x
        => x -> [x] -> NonEmpty (DBranch' x [x])->NonEmpty (DBranch' x [x])
sShIdPartition' c xs st
           = foldr (\p -> let (i,h) = ssi p
                          in asList $ update_nth (\(DBranch d c)
                                                    -> DBranch d (oneBulb h (p:) c))
                                      i )
                   st xs
 where ssi = subshadeId' c (boughDirection<$>st)
sShIdPartition :: WithField ℝ Manifold x => Shade x -> [x] -> NonEmpty (DBranch' x [x])
sShIdPartition (Shade c expa) xs
 | b:bs <- [DBranch v mempty | v <- eigenCoSpan expa]
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





    

-- simplexFaces :: forall n x . Simplex (S n) x -> Triangulation n x
-- simplexFaces (Simplex p (ZeroSimplex q))    = TriangVertices $ Arr.fromList [p, q]
-- simplexFaces splx = carpent splx $ TriangVertices ps
--  where ps = Arr.fromList $ p : splxVertices qs
--        where carpent (ZeroSimplex (Simplex p qs@(Simplex _ _))
--      | Triangulation es <- simplexFaces qs  = TriangSkeleton $ Simplex p <$> es




newtype BaryCoords n = BaryCoords { getBaryCoordsTail :: FreeVect n ℝ }

instance (KnownNat n) => AffineSpace (BaryCoords n) where
  type Diff (BaryCoords n) = FreeVect n ℝ
  BaryCoords v .-. BaryCoords w = v ^-^ w
  BaryCoords v .+^ w = BaryCoords $ v ^+^ w
instance (KnownNat n) => Semimanifold (BaryCoords n) where
  type Needle (BaryCoords n) = FreeVect n ℝ
  (.+~^) = (.+^)
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

mkBaryCoords' :: KnownNat n => [ℝ] -> Option (BaryCoords n)
mkBaryCoords' bcs = fmap (BaryCoords . (^/sum bcs)) . freeVector . Arr.fromList $ tail bcs

newtype ISimplex n x = ISimplex { iSimplexBCCordEmbed :: Embedding (->) (BaryCoords n) x }




data TriangBuilder n x where
  TriangVerticesSt :: [x] -> TriangBuilder Z x
  TriangBuilder :: Triangulation (S n) x
                    -> [x]
                    -> [(Simplex n x, [x] -> Option x)]
                            -> TriangBuilder (S n) x



-- startTriangulation :: forall n x . (KnownNat n, WithField ℝ Manifold x)
--         => ISimplex n x -> TriangBuilder n x
-- startTriangulation ispl@(ISimplex emb) = startWith $ fromISimplex ispl
--  where startWith (ZeroSimplex p) = TriangVerticesSt [p]
--        startWith s@(Simplex _ _)
--                      = TriangBuilder (Triangulation [s])
--                                      (splxVertices s)
--                                      [ (s', expandInDir j)
--                                        | j<-[0..n]
--                                        | s' <- getTriangulation $ simplexFaces s ]
--         where expandInDir j xs = case sortBy (comparing snd) $ filter ((> -1) . snd) xs_bc of
--                             ((x, q) : _) | q<0   -> pure x
--                             _                    -> Hask.empty
--                where xs_bc = map (\x -> (x, getBaryCoord (emb >-$ x) j)) xs
--        (Tagged n) = theNatN :: Tagged n Int

-- extendTriangulation :: forall n x . (KnownNat n, WithField ℝ Manifold x)
--                            => [x] -> TriangBuilder n x -> TriangBuilder n x
-- extendTriangulation xs (TriangBuilder tr tb te) = foldr tryex (TriangBuilder tr tb []) te
--  where tryex (bspl, expd) (TriangBuilder (Triangulation tr') tb' te')
--          | Option (Just fav) <- expd xs
--                     = let snew = Simplex fav bspl
--                       in TriangBuilder (Triangulation $ snew:tr') (fav:tb') undefined

              
bottomExtendSuitability :: (KnownNat n, WithField ℝ Manifold x)
                => ISimplex (S n) x -> x -> ℝ
bottomExtendSuitability (ISimplex emb) x = case getBaryCoord (emb >-$ x) 0 of
     0 -> 0
     r -> - recip r

optimalBottomExtension :: (KnownNat n, WithField ℝ Manifold x)
                => ISimplex (S n) x -> [x] -> Option Int
optimalBottomExtension s xs
      = case filter ((>0).snd)
               $ zipWith ((. bottomExtendSuitability s) . (,)) [0..] xs of
             [] -> Hask.empty
             qs -> pure . fst . maximumBy (comparing snd) $ qs


simplexPlane :: forall n x . (KnownNat n, WithField ℝ Manifold x)
        => Metric x -> Simplex n x -> Embedding (Linear ℝ) (FreeVect n ℝ) (Needle x)
simplexPlane m s = embedding
 where bc = barycenter s
       spread = init . map ((.-~.bc) >>> \(Option (Just v)) -> v) $ splxVertices s
       embedding = case spanHilbertSubspace m spread of
                     (Option (Just e)) -> e
                     _ -> error "Trying to obtain simplexPlane from zero-volume\
                                \ simplex (which cannot span sufficient basis vectors)."



-- simplexShade :: forall x n . (KnownNat n, WithField ℝ Manifold x)
barycenter :: forall x n . (KnownNat n, WithField ℝ Manifold x) => Simplex n x -> x
barycenter = bc 
 where bc (ZS x) = x
       bc (x :<| xs') = x .+~^ sumV [x'–x | x'<-splxVertices xs'] ^/ (n+1)
       
       Tagged n = theNatN :: Tagged n ℝ
       x' – x = case x'.-~.x of {Option(Just v)->v}

toISimplex :: forall x n . (KnownNat n, WithField ℝ Manifold x)
                 => Metric x -> Simplex n x -> ISimplex n x
toISimplex m s = ISimplex $ fromEmbedProject fromBrc toBrc
 where bc = barycenter s
       (Embedding emb (DenseLinear prj))
                         = simplexPlane m s
       (r₀:rs) = [ prj HMat.#> asPackedVector v
                   | x <- splxVertices s, let (Option (Just v)) = x.-~.bc ]
       tmat = HMat.inv $ HMat.fromColumns [ r - r₀ | r<-rs ] 
       toBrc x = case x.-~.bc of
         Option (Just v) -> let rx = prj HMat.#> asPackedVector v - r₀
                            in finalise $ tmat HMat.#> rx
       finalise v = case freeVector $ HMat.toList v of
         Option (Just bv) -> BaryCoords bv
       fromBrc bccs = bc .+~^ (emb $ v)
        where v = linearCombo $ (fromPackedVector r₀, b₀) : zip (fromPackedVector<$>rs) bs
              (b₀:bs) = getBaryCoords' bccs

fromISimplex :: forall x n . (KnownNat n, WithField ℝ Manifold x)
                   => ISimplex n x -> Simplex n x
fromISimplex (ISimplex emb) = s
 where (Option (Just s))
          = makeSimplex' [ emb $-> jOnly
                         | j <- [0..n]
                         , let (Option (Just jOnly)) = mkBaryCoords' [ if k==j then 1 else 0
                                                                     | k<-[0..n] ]
                         ]
       (Tagged n) = theNatN :: Tagged n Int

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

singleFullSimplex :: ∀ t n x . (KnownNat n, WithField ℝ Manifold x)
          => ISimplex n x -> FullTriang t n x (SimplexIT t n x)
singleFullSimplex is = do
   frame <- disjointSimplex (fromISimplex is)
   lift . modify' $ Map.insert frame is
   return frame
       
fullOpenSimplex :: ∀ t n x . (KnownNat n, WithField ℝ Manifold x)
          => Metric x -> Simplex (S n) x -> TriangBuild t n x [SimplexIT t n x]
fullOpenSimplex m s = do
   let is = toISimplex m s
   frame <- disjointSimplex (fromISimplex is)
   fsides <- toList <$> lookSplxFacesIT frame
   lift . forM (zip fsides $ iSimplexSideViews is)
      $ \(fside,is') -> modify' $ Map.insert fside (m,is')
   return fsides


hypotheticalSimplexScore :: ∀ t n n' x . (KnownNat n', WithField ℝ Manifold x, n~S n')
          => SimplexIT t Z x
           -> SimplexIT t n x
           -> TriangBuild t n x ( Option Double )
hypotheticalSimplexScore p b = do
   altViews :: [(SimplexIT t Z x, SimplexIT t n x)] <- do
      pSups <- lookSupersimplicesIT p
      nOpts <- forM pSups $ \psup -> fmap (fmap $ \((bq,_p), _b') -> (bq,psup))
                      $ distinctSimplices b psup
      return $ catOptions nOpts
   scores <- forM ((p,b) :| altViews) $ \(p',b') -> do
      x <- lookVertexIT p'
      q <- lift $ Map.lookup b' <$> get
      return $ case q of
         Just(_,is) | s<-bottomExtendSuitability is x, s>0
                 -> pure s
         _       -> Hask.empty
   return . fmap sum $ Hask.sequence scores

spanSemiOpenSimplex :: ∀ t n n' x . (KnownNat n', WithField ℝ Manifold x, n~S n')
          => SimplexIT t Z x       -- ^ Tip of the desired simplex.
          -> SimplexIT t n x       -- ^ Base of the desired simplex.
          -> TriangBuild t n x [SimplexIT t n x]
                                   -- ^ Return the exposed faces of the new simplices.
spanSemiOpenSimplex p b = do
   m <- lift $ fst <$> (Map.!b) <$> get
   neighbours <- filterM isAdjacent =<< lookSupersimplicesIT p
   let bs = b:|neighbours
   frame <- webinateTriang p b
   backSplx <- lookSimplex frame
   let iSplx = toISimplex m backSplx
   fsides <- toList <$> lookSplxFacesIT frame
   let sviews = filter (not . (`elem`bs) . fst) $ zip fsides (iSimplexSideViews iSplx)
   lift . forM sviews $ \(fside,is') -> modify' $ Map.insert fside (m,is')
   lift . Hask.forM_ bs $ \fside -> modify' $ Map.delete fside
   return $ fst <$> sviews
 where isAdjacent = fmap (isJust . getOption) . sharedBoundary b

multiextendTriang :: ∀ t n n' x . (KnownNat n', WithField ℝ Manifold x, n~S n')
          => [SimplexIT t Z x] -> TriangBuild t n x ()
multiextendTriang vs = do
   ps <- mapM lookVertexIT vs
   sides <- lift $ Map.toList <$> get
   forM_ sides $ \(f,(m,s)) ->
      case optimalBottomExtension s ps of
        Option (Just c) -> spanSemiOpenSimplex (vs !! c) f
        _               -> return []

-- | BUGGY: this does connect the supplied triangulations, but it doesn't choose
--   the right boundary simplices yet. Probable cause: inconsistent internal
--   numbering of the subsimplices.
autoglueTriangulation :: ∀ t n n' n'' x
            . (KnownNat n'', WithField ℝ Manifold x, n~S n', n'~S n'')
           => (∀ t' . TriangBuild t' n' x ()) -> TriangBuild t n' x ()
autoglueTriangulation tb = do
    mbBounds <- Map.toList <$> lift get
    mps <- pointsOfSurf mbBounds
    
    WriterT gbBounds <- liftInTriangT $ mixinTriangulation tb'
    lift . forM_ gbBounds $ \(i,ms) -> do
        modify' $ Map.insert i ms
    gps <- pointsOfSurf gbBounds
    
    autoglue mps gbBounds
    autoglue gps mbBounds
    
 where tb' :: ∀ s . TriangT s n x Identity
                     (WriterT (Metric x, ISimplex n x) [] (SimplexIT s n' x))
       tb' = unliftInTriangT (`evalStateT`mempty) $
                  tb >> (WriterT . Map.toList) <$> lift get
       
       pointsOfSurf s = fnubConcatMap Hask.toList <$> forM s (lookSplxVerticesIT . fst)
       
       autoglue :: [SimplexIT t Z x] -> [(SimplexIT t n' x, (Metric x, ISimplex n x))]
                       -> TriangBuild t n' x ()
       autoglue vs sides = do
          forM_ sides $ \(f,_) -> do
             possibs <- forM vs $ \p -> fmap(p,) <$> hypotheticalSimplexScore p f
             case catOptions possibs of
               [] -> return ()
               qs -> do
                 spanSemiOpenSimplex (fst `id` maximumBy (comparing $ snd) qs) f
                 return ()


data AutoTriang n x where
  AutoTriang :: { getAutoTriang :: ∀ t . TriangBuild t n x () } -> AutoTriang (S n) x

instance (KnownNat n, WithField ℝ Manifold x) => Semigroup (AutoTriang (S (S n)) x) where
  (<>) = autoTriangMappend

autoTriangMappend :: ∀ n n' n'' x . ( KnownNat n'', n ~ S n', n' ~ S n''
                                    , WithField ℝ Manifold x             )
          => AutoTriang n x -> AutoTriang n x -> AutoTriang n x
AutoTriang a `autoTriangMappend` AutoTriang b = AutoTriang c
 where c :: ∀ t . TriangBuild t n' x ()
       c = a >> autoglueTriangulation b

elementaryTriang :: ∀ n n' x . (KnownNat n', n~S n', WithField ℝ EuclidSpace x)
                      => Simplex n x -> AutoTriang n x
elementaryTriang t = AutoTriang (fullOpenSimplex m t >> return ())
 where (Tagged m) = euclideanMetric :: Tagged x (Metric x)

breakdownAutoTriang :: ∀ n n' x . (KnownNat n', n ~ S n') => AutoTriang n x -> [Simplex n x]
breakdownAutoTriang (AutoTriang t) = doTriangBuild t
         
                    
--  where tr :: Triangulation n x
--        outfc :: Map.Map (SimplexIT t n' x) (Metric x, ISimplex n x)
--        (((), tr), outfc) = runState (doTriangT tb') mempty
--        tb' :: ∀ t' . TriangT t' n x 
--                         ( State ( Map.Map (SimplexIT t' n' x)
--                              (Metric x, ISimplex n x) ) ) ()
--        tb' = tb
   
   
   
       

-- primitiveTriangulation :: forall x n . (KnownNat n,WithField ℝ Manifold x)
--                              => [x] -> Triangulation n x
-- primitiveTriangulation xs = head $ build <$> buildOpts
--  where build :: ([x], [x]) -> Triangulation n x
--        build (mainVerts, sideVerts) = Triangulation [mainSplx]
--         where (Option (Just mainSplx)) = makeSimplex mainVerts
-- --              mainFaces = Map.fromAscList . zip [0..] . getTriangulation
-- --                                 $ simplexFaces mainSplx
--        buildOpts = partitionsOfFstLength n xs
--        (Tagged n) = theNatN :: Tagged n Int
 
partitionsOfFstLength :: Int -> [a] -> [([a],[a])]
partitionsOfFstLength 0 l = [([],l)]
partitionsOfFstLength n [] = []
partitionsOfFstLength n (x:xs) = first (x:) <$> partitionsOfFstLength (n-1) xs
                              ++ second (x:) <$> partitionsOfFstLength n xs

splxVertices :: Simplex n x -> [x]
splxVertices (ZS x) = [x]
splxVertices (x :<| s') = x : splxVertices s'



-- triangulate :: forall x n . (KnownNat n, WithField ℝ Manifold x)
--                  => ShadeTree x -> Triangulation n x
-- triangulate (DisjointBranches _ brs)
--     = Triangulation $ Hask.foldMap (getTriangulation . triangulate) brs
-- triangulate (PlainLeaves xs) = primitiveTriangulation xs

-- triangBranches :: WithField ℝ Manifold x
--                  => ShadeTree x -> Branchwise x (Triangulation x) n
-- triangBranches _ = undefined
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
chainsaw cpln (PlainLeaves xs) = Sawbones (sd1++) (sd2++) sd2 sd1
 where (sd1,sd2) = partition (\x -> sideOfCut cpln x == Option(Just PositiveHalfSphere)) xs
chainsaw cpln (DisjointBranches _ brs) = Hask.foldMap (chainsaw cpln) brs
chainsaw cpln (OverlappingBranches _ (Shade _ bexpa) brs) = Sawbones t1 t2 d1 d2
 where (Sawbones t1 t2 subD1 subD2)
             = Hask.foldMap (Hask.foldMap (chainsaw cpln) . boughContents) brs
       [d1,d2] = map (foldl' go [] . foci) [subD1, subD2]
        where go d' (dp,dqs) = case fathomCD dp of
                 Option (Just dpCD) | not $ any (shelter dpCD) dqs
                    -> dp:d' -- dp is close enough to cut plane to make dust.
                 _  -> d'    -- some dq is actually closer than the cut plane => discard dp.
               where shelter dpCutDist dq = case ptsDist dp dq of
                        Option (Just d) -> d < abs dpCutDist
                        _               -> False
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
          = SingleCut $ chainsaw (Cutplane sh $ stiefel1Project dir) src
sShSaw (OverlappingBranches _ (Shade cctr _) cbrs) (PlainLeaves xs)
          = Sawboneses . DBranches $ NE.fromList ngbsAdded
 where brsEmpty = fmap (\(DBranch dir _)-> DBranch dir mempty) cbrs
       srcDistrib = sShIdPartition' cctr xs brsEmpty
       ngbsAdded = fmap (\(DBranch dir (Hourglass u l), othrs)
                             -> let [allOthr,allOthr']
                                        = map (DBranches . NE.fromList)
                                            [othrs, fmap (\(DBranch d' o)
                                                          ->DBranch(negateV d') o) othrs]
                                in DBranch dir $ Hourglass (DustyEdges (u++) allOthr)
                                                           (DustyEdges (l++) allOthr')
                        ) $ foci (NE.toList srcDistrib)
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
        where cpln cpSgn = Cutplane sh . stiefel1Project $ dir1 ^+^ cpSgn*^dir2
              [pd2', md2'] = zipWith (occl . cpln) [-1, 1] [pd2, md2] 
              occl cpl = foldl' go [] . foci
               where go d' (dp,dqs) = case fathomCD dp of
                           Option (Just dpCD) | not $ any (shelter dpCD) dqs
                                     -> dp:d'
                           _         -> d'
                      where shelter dpCutDist dq = case ptsDist dp dq of
                             Option (Just d) -> d < abs dpCutDist
                             _               -> False
                            ptsDist = fmap (metric $ recipMetric bexpa) .: (.-~.)
                     fathomCD = fathomCutDistance cpl bexpa
sShSaw _ _ = error "`sShSaw` is not supposed to cut anything else but `OverlappingBranches`"


foci :: [a] -> [(a,[a])]
foci [] = []
foci (x:xs) = (x,xs) : fmap (second (x:)) (foci xs)
       

(.:) :: (c->d) -> (a->b->c) -> a->b->d 
(.:) = (.) . (.)


catOptions :: [Option a] -> [a]
catOptions = catMaybes . map getOption



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






extractJust :: (a->Maybe b) -> [a] -> (Maybe b, [a])
extractJust f [] = (Nothing,[])
extractJust f (x:xs) | Just r <- f x  = (Just r, xs)
                     | otherwise      = second (x:) $ extractJust f xs

