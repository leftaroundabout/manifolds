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
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE ViewPatterns               #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE LiberalTypeSynonyms        #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE DataKinds                  #-}


module Data.Manifold.TreeCover (
       -- * Shades 
         Shade(..), pattern(:±), Shade'(..), (|±|), IsShade
       -- ** Lenses
       , shadeCtr, shadeExpanse, shadeNarrowness
       -- ** Construction
       , fullShade, fullShade', pointsShades, pointsCovers
       -- ** Evaluation
       , occlusion
       -- ** Misc
       , factoriseShade, intersectShade's
       -- * Shade trees
       , ShadeTree(..), fromLeafPoints, onlyLeaves, indexShadeTree
       -- * View helpers
       , onlyNodes
       -- ** Auxiliary types
       , SimpleTree, Trees, NonEmptyTree, GenericTree(..)
       -- * Misc
       , sShSaw, chainsaw, HasFlatView(..), shadesMerge, smoothInterpolate
       , twigsWithEnvirons, completeTopShading, flexTwigsShading
       , WithAny(..), Shaded, stiAsIntervalMapping, spanShading
       , constShaded, stripShadedUntopological
       , DifferentialEqn, filterDEqnSolution_loc
       -- ** Triangulation-builders
       , TriangBuild, doTriangBuild, singleFullSimplex, autoglueTriangulation
       , AutoTriang, elementaryTriang, breakdownAutoTriang
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
import Data.Manifold.Types.Primitive ((^), empty)
import Data.Manifold.PseudoAffine
import Data.Function.Differentiable
import Data.Function.Differentiable.Data
    
import Data.Embedding
import Data.CoNat

import qualified Prelude as Hask hiding(foldl, sum, sequence)
import qualified Control.Applicative as Hask
import qualified Control.Monad       as Hask hiding(forM_, sequence)
import Data.Functor.Identity
import Control.Monad.Trans.State
import Control.Monad.Trans.Writer
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Class
import qualified Data.Foldable       as Hask
import Data.Foldable (all, elem, toList, sum, foldr1)
import qualified Data.Traversable as Hask
import Data.Traversable (forM)

import qualified Numeric.LinearAlgebra.HMatrix as HMat

import Control.Category.Constrained.Prelude hiding
     ((^), all, elem, sum, forM, Foldable(..), foldr1, Traversable, traverse)
import Control.Arrow.Constrained
import Control.Monad.Constrained hiding (forM)
import Data.Foldable.Constrained
import Data.Traversable.Constrained (traverse)

import GHC.Generics (Generic)


-- | Possibly / Partially / asymPtotically singular metric.
data PSM x = PSM {
       psmExpanse :: !(Metric' x)
     , relevantEigenspan :: ![Needle' x]
     }
       

-- | A 'Shade' is a very crude description of a region within a manifold. It
--   can be interpreted as either an ellipsoid shape, or as the Gaussian peak
--   of a normal distribution (use <http://hackage.haskell.org/package/manifold-random>
--   for actually sampling from that distribution).
-- 
--   For a /precise/ description of an arbitrarily-shaped connected subset of a manifold,
--   there is 'Region', whose implementation is vastly more complex.
data Shade x = Shade { _shadeCtr :: !(Interior x)
                     , _shadeExpanse :: !(Metric' x) }
deriving instance (Show x, Show (Needle x), WithField ℝ Manifold x) => Show (Shade x)

-- | A &#x201c;co-shade&#x201d; can describe ellipsoid regions as well, but unlike
--   'Shade' it can be unlimited / infinitely wide in some directions.
--   It does OTOH need to have nonzero thickness, which 'Shade' needs not.
data Shade' x = Shade' { _shade'Ctr :: !(Interior x)
                       , _shade'Narrowness :: !(Metric x) }
deriving instance (Show x, Show (DualSpace (Needle x)), WithField ℝ Manifold x)
             => Show (Shade' x)

class IsShade shade where
--  type (*) shade :: *->*
  -- | Access the center of a 'Shade' or a 'Shade''.
  shadeCtr :: Functor f (->) (->) => (Interior x->f (Interior x)) -> shade x -> f (shade x)
--  -- | Convert between 'Shade' and 'Shade' (which must be neither singular nor infinite).
--  unsafeDualShade :: WithField ℝ Manifold x => shade x -> shade* x
  -- | Check the statistical likelihood-density of a point being within a shade.
  --   This is taken as a normal distribution.
  occlusion :: ( Manifold x, s ~ (Scalar (Needle x)), RealDimension s )
                => shade x -> x -> s
  factoriseShade :: ( Manifold x, RealDimension (Scalar (Needle x))
                    , Manifold y, RealDimension (Scalar (Needle y)) )
                => shade (x,y) -> (shade x, shade y)

instance IsShade Shade where
  shadeCtr f (Shade c e) = fmap (`Shade`e) $ f c
  occlusion (Shade p₀ δ) = occ
   where occ p = case p .-~. p₀ of
           Option(Just vd) | mSq <- metricSq δinv vd
                           , mSq == mSq  -- avoid NaN
                           -> exp (negate mSq)
           _               -> zeroV
         δinv = recipMetric δ
  factoriseShade (Shade (x₀,y₀) δxy) = (Shade x₀ δx, Shade y₀ δy)
   where (δx,δy) = factoriseMetric' δxy

shadeExpanse :: Functor f (->) (->) => (Metric' x -> f (Metric' x)) -> Shade x -> f (Shade x)
shadeExpanse f (Shade c e) = fmap (Shade c) $ f e

instance IsShade Shade' where
  shadeCtr f (Shade' c e) = fmap (`Shade'`e) $ f c
  occlusion (Shade' p₀ δinv) = occ
   where occ p = case p .-~. p₀ of
           Option(Just vd) | mSq <- metricSq δinv vd
                           , mSq == mSq  -- avoid NaN
                           -> exp (negate mSq)
           _               -> zeroV
  factoriseShade (Shade' (x₀,y₀) δxy) = (Shade' x₀ δx, Shade' y₀ δy)
   where (δx,δy) = factoriseMetric δxy

shadeNarrowness :: Functor f (->) (->) => (Metric x -> f (Metric x)) -> Shade' x -> f (Shade' x)
shadeNarrowness f (Shade' c e) = fmap (Shade' c) $ f e

instance (AffineManifold x) => Semimanifold (Shade x) where
  type Needle (Shade x) = Diff x
  fromInterior = id
  toInterior = pure
  translateP = Tagged (.+~^)
  Shade c e .+~^ v = Shade (c.+^v) e
  Shade c e .-~^ v = Shade (c.-^v) e

fullShade :: WithField ℝ Manifold x => x -> Metric' x -> Shade x
fullShade ctr expa = Shade ctr expa

fullShade' :: WithField ℝ Manifold x => x -> Metric x -> Shade' x
fullShade' ctr expa = Shade' ctr expa


-- | Span a 'Shade' from a center point and multiple deviation-vectors.
pattern (:±) :: () => WithField ℝ Manifold x => x -> [Needle x] -> Shade x
pattern x :± shs <- Shade x (eigenSpan -> shs)
 where x :± shs = fullShade x . sumV $ projector'<$>shs


-- | Similar to ':±', but instead of expanding the shade, each vector /restricts/ it.
--   Iff these form a orthogonal basis (in whatever sense applicable), then both
--   methods will be equivalent.
-- 
--   Note that '|±|' is only possible, as such, in an inner-product space; in
--   general you need reciprocal vectors ('Needle'') to define a 'Shade''.
(|±|) :: WithField ℝ EuclidSpace x => x -> [Needle x] -> Shade' x
x |±| shs = Shade' x $ sumV [projector $ v^/(v<.>v) | v<-shs]



subshadeId' :: WithField ℝ Manifold x
                   => x -> NonEmpty (Needle' x) -> x -> (Int, HourglassBulb)
subshadeId' c expvs x = case x .-~. c of
    Option (Just v) -> let (iu,vl) = maximumBy (comparing $ abs . snd)
                                      $ zip [0..] (map (v <.>^) $ NE.toList expvs)
                       in (iu, if vl>0 then UpperBulb else LowerBulb)
    _ -> (-1, error "Trying to obtain the subshadeId of a point not actually included in the shade.")

subshadeId :: WithField ℝ Manifold x => Shade x -> x -> (Int, HourglassBulb)
subshadeId (Shade c expa) = subshadeId' c . NE.fromList $ eigenCoSpan expa
                 


-- | Attempt to find a 'Shade' that describes the distribution of given points.
--   At least in an affine space (and thus locally in any manifold), this can be used to
--   estimate the parameters of a normal distribution from which some points were
--   sampled. Note that some points will be &#x201c;outside&#x201d; of the shade,
--   as happens for a normal distribution with some statistical likelyhood.
--   (Use 'pointsCovers' if you need to prevent that.)
-- 
--   For /nonconnected/ manifolds it will be necessary to yield separate shades
--   for each connected component. And for an empty input list, there is no shade!
--   Hence the result type is a list.
pointsShades :: WithField ℝ Manifold x => [x] -> [Shade x]
pointsShades = map snd . pointsShades' zeroV

-- | Like 'pointsShades', but ensure that all points are actually in
--   the shade, i.e. if @['Shade' x₀ ex]@ is the result then
--   @'metric' (recipMetric ex) (p-x₀) ≤ 1@ for all @p@ in the list.
pointsCovers :: ∀ x . WithField ℝ Manifold x => [x] -> [Shade x]
pointsCovers = map guaranteeIn . pointsShades' zeroV
 where guaranteeIn (ps, Shade x₀ ex) 
          = case ps >>= \p -> let Option (Just v) = p.-~.x₀
                              in guard (metric ex' v > 1) >> [(p,projector' v)]
             of []   -> Shade x₀ ex
                outs -> guaranteeIn ( fst<$>outs
                                    , Shade x₀
                                         $ ex ^+^ sumV (snd<$>outs)
                                                    ^/ fromIntegral (2 * length outs) )
        where ex' = recipMetric ex

pointsShade's :: WithField ℝ Manifold x => [x] -> [Shade' x]
pointsShade's = map (\(Shade c e) -> Shade' c $ recipMetric e) . pointsShades

pointsCover's :: WithField ℝ Manifold x => [x] -> [Shade' x]
pointsCover's = map (\(Shade c e) -> Shade' c $ recipMetric e) . pointsCovers

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
       

-- | Attempt to reduce the number of shades to fewer (ideally, a single one).
--   In the simplest cases these should guaranteed cover the same area;
--   for non-flat manifolds it only works in a heuristic sense.
shadesMerge :: WithField ℝ Manifold x
                 => ℝ -- ^ How near (inverse normalised distance, relative to shade expanse)
                      --   two shades must be to be merged. If this is zero, any shades
                      --   in the same connected region of a manifold are merged.
                 -> [Shade x] -- ^ A list of /n/ shades.
                 -> [Shade x] -- ^ /m/ &#x2264; /n/ shades which cover at least the same area.
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
           , fuzz*b₁*b₂ <= b₁ + b₂
                  = Just $ let cc = c₂ .+~^ v ^/ 2
                               Option (Just cv₁) = c₁.-~.cc
                               Option (Just cv₂) = c₂.-~.cc
                           in Shade cc . sumV $ [e₁, e₂] ++ (projector'<$>[cv₁, cv₂])
           | otherwise  = Nothing
shadesMerge _ shs = shs

-- | Evaluate the shade as a quadratic form; essentially
-- @
-- minusLogOcclusion sh x = x <.>^ (sh^.shadeExpanse $ x - sh^.shadeCtr)
-- @
-- where 'shadeExpanse' gives a metric (matrix) that characterises the
-- width of the shade.
minusLogOcclusion' :: ( Manifold x, s ~ (Scalar (Needle x)), RealDimension s )
              => Shade' x -> x -> s
minusLogOcclusion' (Shade' p₀ δinv) = occ
 where occ p = case p .-~. p₀ of
         Option(Just vd) | mSq <- metricSq δinv vd
                         , mSq == mSq  -- avoid NaN
                         -> mSq
         _               -> 1/0
minusLogOcclusion :: ( Manifold x, s ~ (Scalar (Needle x)), RealDimension s )
              => Shade x -> x -> s
minusLogOcclusion (Shade p₀ δ) = occ
 where occ p = case p .-~. p₀ of
         Option(Just vd) | mSq <- metricSq δinv vd
                         , mSq == mSq  -- avoid NaN
                         -> mSq
         _               -> 1/0
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

data HourglassBulb = UpperBulb | LowerBulb
oneBulb :: HourglassBulb -> (a->a) -> Hourglass a->Hourglass a
oneBulb UpperBulb f (Hourglass u l) = Hourglass (f u) l
oneBulb LowerBulb f (Hourglass u l) = Hourglass u (f l)



data ShadeTree x = PlainLeaves [x]
                 | DisjointBranches !Int (NonEmpty (ShadeTree x))
                 | OverlappingBranches !Int !(Shade x) (NonEmpty (DBranch x))
  deriving (Generic)
           
data DBranch' x c = DBranch { boughDirection :: !(Needle' x)
                            , boughContents :: !(Hourglass c) }
  deriving (Generic, Hask.Functor, Hask.Foldable)
type DBranch x = DBranch' x (ShadeTree x)

newtype DBranches' x c = DBranches (NonEmpty (DBranch' x c))
  deriving (Generic, Hask.Functor, Hask.Foldable)

-- ^ /Unsafe/: this assumes the direction information of both containers to be equivalent.
instance (Semigroup c) => Semigroup (DBranches' x c) where
  DBranches b1 <> DBranches b2 = DBranches $ NE.zipWith (\(DBranch d1 c1) (DBranch _ c2)
                                                              -> DBranch d1 $ c1<>c2 ) b1 b2
  
directionChoices :: WithField ℝ Manifold x
               => [DBranch x]
                 -> [ ( (Needle' x, ShadeTree x)
                      ,[(Needle' x, ShadeTree x)] ) ]
directionChoices [] = []
directionChoices (DBranch ѧ (Hourglass t b) : hs)
       =  ( (ѧ,t), (v,b) : map fst uds)
          : ((v,b), (ѧ,t) : map fst uds)
          : map (second $ ((ѧ,t):) . ((v,b):)) uds
 where v = negateV ѧ
       uds = directionChoices hs

traverseDirectionChoices :: (WithField ℝ Manifold x, Hask.Applicative f)
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


-- | Build a quite nicely balanced tree from a cloud of points, on any real manifold.
-- 
--   Example: https://nbviewer.jupyter.org/github/leftaroundabout/manifolds/blob/master/test/Trees-and-Webs.ipynb#pseudorandomCloudTree
-- 
-- <<images/examples/simple-2d-ShadeTree.png>>
fromLeafPoints :: ∀ x. WithField ℝ Manifold x => [x] -> ShadeTree x
fromLeafPoints = fromLeafPoints' sShIdPartition


indexShadeTree :: ∀ x . WithField ℝ Manifold x
       => ShadeTree x -> Int -> Either Int ([ShadeTree x], x)
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


fromFnGraphPoints :: ∀ x y . (WithField ℝ Manifold x, WithField ℝ Manifold y)
                     => [(x,y)] -> ShadeTree (x,y)
fromFnGraphPoints = fromLeafPoints' fg_sShIdPart
 where fg_sShIdPart :: Shade (x,y) -> [(x,y)] -> NonEmpty (DBranch' (x,y) [(x,y)])
       fg_sShIdPart (Shade c expa) xs
        | b:bs <- [DBranch (v, zeroV) mempty
                    | v <- eigenCoSpan
                           (transformMetric' fst expa :: Metric' x) ]
                      = sShIdPartition' c xs $ b:|bs

fromLeafPoints' :: ∀ x. WithField ℝ Manifold x =>
    (Shade x -> [x] -> NonEmpty (DBranch' x [x])) -> [x] -> ShadeTree x
fromLeafPoints' sShIdPart = go zeroV
 where go :: Metric' x -> [x] -> ShadeTree x
       go preShExpa = \xs -> case pointsShades' (preShExpa^/10) xs of
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


trunks :: ∀ x. WithField ℝ Manifold x => ShadeTree x -> [Shade x]
trunks (PlainLeaves lvs) = pointsCovers lvs
trunks (DisjointBranches _ brs) = Hask.foldMap trunks brs
trunks (OverlappingBranches _ sh _) = [sh]


nLeaves :: ShadeTree x -> Int
nLeaves (PlainLeaves lvs) = length lvs
nLeaves (DisjointBranches n _) = n
nLeaves (OverlappingBranches n _ _) = n

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


intersectShade's :: ∀ y . WithField ℝ Manifold y => [Shade' y] -> Option (Shade' y)
intersectShade's [] = error "Global `Shade'` not implemented, so can't do intersection of zero co-shades."
intersectShade's (sh:shs) = Hask.foldrM inter2 sh shs
 where inter2 :: Shade' y -> Shade' y -> Option (Shade' y)
       inter2 (Shade' c e) (Shade' ζ η)
           | μe < 1 && μη < 1  = return $ Shade' iCtr iExpa
           | otherwise         = empty
        where [c', ζ'] = [ ctr.+~^linearCombo
                                     [ (v, 1 / (1 + metricSq oExpa w))
                                     | v <- (*^) <$> [-1,1] <*> span
                                     , let p = ctr .+~^ v  :: y
                                           Option (Just w) = p.-~.oCtr
                                     ]
                         | ctr                  <- [c,     ζ    ]
                         | span <- eigenCoSpan'<$> [e,     η    ]
                         | (oCtr,oExpa)         <- [(ζ,η), (c,e)]
                         ]
              Option (Just c'2ζ') = ζ'.-~.c'
              Option (Just c2ζ') = ζ'.-~.c
              Option (Just ζ2c') = c'.-~.ζ
              μc = metricSq e c2ζ'
              μζ = metricSq η ζ2c'
              iCtr = c' .+~^ c'2ζ' ^* (μζ/(μc + μζ)) -- weighted mean between c' and ζ'.
              Option (Just rc) = c.-~.iCtr
              Option (Just rζ) = ζ.-~.iCtr
              rcⰰ = toDualWith e rc
              rζⰰ = toDualWith η rζ
              μe = rcⰰ<.>^rc
              μη = rζⰰ<.>^rζ
              iExpa = (e^+^η)^/2 ^+^ projector rcⰰ^/(1-μe) ^+^ projector rζⰰ^/(1-μη)




type DifferentialEqn x y = Shade (x,y) -> Shade' (LocalLinear x y)


filterDEqnSolution_loc :: ∀ x y . (WithField ℝ Manifold x, WithField ℝ Manifold y)
           => DifferentialEqn x y -> ((x, Shade' y), [(x, Shade' y)])
                   -> Option (Shade' y)
filterDEqnSolution_loc f ((x, shy@(Shade' y expay)), neighbours@(_:_)) = yc
 where jShade@(Shade' j₀ jExpa) = f shxy
       [shxy] = pointsCovers [ (xs, ys.+~^δy)
                             | (xs, Shade' ys yse) <- (x,shy):neighbours
                             , δy <- eigenCoSpan' yse ]
       [Shade' _ expax] = pointsCover's (fst<$>neighbours)
       marginδs :: [(Needle x, (Needle y, Metric y))]
       marginδs = [ (δxm, (δym, expany))
                  | (xn, Shade' yn expany) <- neighbours
                  , let (Option (Just δxm)) = xn.-~.x
                        (Option (Just δym)) = yn.-~.y
                  ]
       back2Centre :: (Needle x, (Needle y, Metric y)) -> Shade' y
       back2Centre (δx, (δym, expany))
            = Shade' (y.+~^δyb) . recipMetric
                $ recipMetric' expany
                  ^+^ recipMetric' (applyLinMapMetric jExpa δx')
        where δyb = δym ^-^ (j₀ $ δx)
              δx' = toDualWith expax δx
       yc :: Option (Shade' y)
       yc = intersectShade's $ back2Centre <$> marginδs
       xSpan = eigenCoSpan' expax


-- Formerly, this was the signature of what has now become 'traverseTwigsWithEnvirons'.
-- The simple list-yielding version (see rev. b4a427d59ec82889bab2fde39225b14a57b694df
-- may well be more efficient than this version via a traversal.
twigsWithEnvirons :: ∀ x. WithField ℝ Manifold x
    => ShadeTree x -> [((Int, ShadeTree x), [(Int, ShadeTree x)])]
twigsWithEnvirons = execWriter . traverseTwigsWithEnvirons (writer . (snd.fst&&&pure))

data OuterMaybeT f a = OuterNothing | OuterJust (f a) deriving (Hask.Functor)
instance (Hask.Applicative f) => Hask.Applicative (OuterMaybeT f) where
  pure = OuterJust . pure
  OuterJust fs <*> OuterJust xs = OuterJust $ fs <*> xs
  _ <*> _ = OuterNothing

traverseTwigsWithEnvirons :: ∀ x f .
            (WithField ℝ Manifold x, Hask.Applicative f)
    => ( ((Int, ShadeTree x), [(Int, ShadeTree x)]) -> f (ShadeTree x))
         -> ShadeTree x -> f (ShadeTree x)
traverseTwigsWithEnvirons f = fst . go [] . (0,)
 where go :: [(Int, ShadeTree x)] -> (Int, ShadeTree x)
                          -> (f (ShadeTree x), Bool)
       go _ (i₀, DisjointBranches nlvs djbs) = ( fmap (DisjointBranches nlvs)
                                                   . Hask.traverse (fst . go [])
                                                   $ NE.zip ioffs djbs
                                               , False )
        where ioffs = NE.scanl (\i -> (+i) . nLeaves) i₀ djbs
       go envi ct@(i₀, (OverlappingBranches nlvs rob@(Shade robc _) brs))
                = ( case descentResult of
                     OuterNothing -> f
                         $ purgeRemotes
                            (ct, Hask.foldMap (\(io,te)
                                            -> first (+io) <$> twigProximæ robc te) envi)
                     OuterJust dR -> fmap (OverlappingBranches nlvs rob . NE.fromList) dR
                  , False )
        where descentResult = traverseDirectionChoices tdc $ NE.toList brs
              tdc (io, (vy, ty)) alts = case go envi'' (i₀+io, ty) of
                                   (_, True) -> OuterNothing
                                   (down, _) -> OuterJust down
               where envi'' = filter (snd >>> trunks >>> \(Shade ce _:_)
                                         -> let Option (Just δyenv) = ce.-~.robc
                                                qq = vy<.>^δyenv
                                            in qq > -1 && qq < 5
                                       ) envi'
                              ++ map ((+i₀)***snd) alts
              envi' = approach =<< envi
              approach (i₀e, apt@(OverlappingBranches _ (Shade envc _) _))
                  = first (+i₀e) <$> twigsaveTrim hither apt
               where Option (Just δxenv) = robc .-~. envc
                     hither (DBranch bdir (Hourglass bdc₁ bdc₂))
                       | bdir<.>^δxenv > 0  = [(0           , bdc₁)]
                       | otherwise          = [(nLeaves bdc₁, bdc₂)]
              approach q = [q]
       go envi plvs@(i₀, (PlainLeaves _))
                         = (f $ purgeRemotes (plvs, envi), True)
       
       twigProximæ :: x -> ShadeTree x -> [(Int, ShadeTree x)]
       twigProximæ x₀ (DisjointBranches _ djbs)
               = Hask.foldMap (\(i₀,st) -> first (+i₀) <$> twigProximæ x₀ st)
                    $ NE.zip ioffs djbs
        where ioffs = NE.scanl (\i -> (+i) . nLeaves) 0 djbs
       twigProximæ x₀ ct@(OverlappingBranches _ (Shade xb qb) brs)
                   = twigsaveTrim hither ct
        where Option (Just δxb) = x₀ .-~. xb
              hither (DBranch bdir (Hourglass bdc₁ bdc₂))
                 | bdir<.>^δxb > 0  = twigProximæ x₀ bdc₁
                 | otherwise        = first (+nLeaves bdc₁)
                                     <$> twigProximæ x₀ bdc₂
       twigProximæ _ plainLeaves = [(0, plainLeaves)]
       
       twigsaveTrim :: (DBranch x -> [(Int,ShadeTree x)])
                       -> ShadeTree x -> [(Int,ShadeTree x)]
       twigsaveTrim f ct@(OverlappingBranches _ _ dbs)
                 = case Hask.mapM (\(i₀,dbr) -> noLeaf $ first(+i₀)<$>f dbr)
                                 $ NE.zip ioffs dbs of
                      Just pqe -> Hask.fold pqe
                      _        -> [(0,ct)]
        where noLeaf [(_,PlainLeaves _)] = empty
              noLeaf bqs = pure bqs
              ioffs = NE.scanl (\i -> (+i) . sum . fmap nLeaves . toList) 0 dbs
       
       purgeRemotes :: ((Int,ShadeTree x), [(Int,ShadeTree x)])
                    -> ((Int,ShadeTree x), [(Int,ShadeTree x)])
       purgeRemotes = id -- See 7d1f3a4 for the implementation; this didn't work reliable. 
    
completeTopShading :: (WithField ℝ Manifold x, WithField ℝ Manifold y)
                   => x`Shaded`y -> [Shade' (x,y)]
completeTopShading (PlainLeaves plvs)
                     = pointsShade's $ (_topological &&& _untopological) <$> plvs
completeTopShading (DisjointBranches _ bqs)
                     = take 1 . completeTopShading =<< NE.toList bqs
completeTopShading t = pointsCover's . map (_topological &&& _untopological) $ onlyLeaves t

flexTopShading :: ∀ x y f . ( WithField ℝ Manifold x, WithField ℝ Manifold y
                            , Applicative f (->) (->) )
                  => (Shade' (x,y) -> f (x, (Shade' y, LocalLinear x y)))
                      -> x`Shaded`y -> f (x`Shaded`y)
flexTopShading f tr = seq (assert_onlyToplevDisjoint tr)
                    $ recst (completeTopShading tr) tr
 where recst qsh@(_:_) (DisjointBranches n bqs)
          = undefined -- DisjointBranches n $ NE.zipWith (recst . (:[])) (NE.fromList qsh) bqs
       recst [sha@(Shade' (_,yc₀) expa₀)] t = fmap fts $ f sha
        where expa'₀ = recipMetric' expa₀
              j₀ :: LocalLinear x y
              Option (Just j₀) = covariance expa'₀
              (_,expay₀) = factoriseMetric expa₀
              fts (xc, (Shade' yc expay, jtg)) = unsafeFmapLeaves applδj t
               where Option (Just δyc) = yc.-~.yc₀
                     tfm = imitateMetricSpanChange expay₀ (recipMetric' expay)
                     applδj (WithAny y x)
                           = WithAny (yc₀ .+~^ ((tfm$δy) ^+^ (jtg$δx) ^+^ δyc)) x
                      where Option (Just δx) = x.-~.xc
                            Option (Just δy) = y.-~.(yc₀.+~^(j₀$δx))
       
       assert_onlyToplevDisjoint, assert_connected :: x`Shaded`y -> ()
       assert_onlyToplevDisjoint (DisjointBranches _ dp) = rnf (assert_connected<$>dp)
       assert_onlyToplevDisjoint t = assert_connected t
       assert_connected (OverlappingBranches _ _ dp)
           = rnf (Hask.foldMap assert_connected<$>dp)
       assert_connected (PlainLeaves _) = ()

flexTwigsShading :: ∀ x y f . ( WithField ℝ Manifold x, WithField ℝ Manifold y
                              , Hask.Applicative f )
                  => (Shade' (x,y) -> f (x, (Shade' y, LocalLinear x y)))
                      -> x`Shaded`y -> f (x`Shaded`y)
flexTwigsShading f = traverseTwigsWithEnvirons locFlex
 where locFlex :: ∀ μ . ((Int, x`Shaded`y), μ) -> f (x`Shaded`y)
       locFlex ((_,lsh), _) = flexTopShading f lsh
                







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
  fromInterior = id
  toInterior = pure
  translateP = Tagged (.+~^)
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
--                             _                    -> empty
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
             [] -> empty
             qs -> pure . fst . maximumBy (comparing snd) $ qs


simplexPlane :: forall n x . (KnownNat n, WithField ℝ Manifold x)
        => Metric x -> Simplex n x -> Embedding (Linear ℝ) (FreeVect n ℝ) (Needle x)
simplexPlane m s = embedding
 where bc = simplexBarycenter s
       spread = init . map ((.-~.bc) >>> \(Option (Just v)) -> v) $ splxVertices s
       embedding = case spanHilbertSubspace m spread of
                     (Option (Just e)) -> e
                     _ -> error "Trying to obtain simplexPlane from zero-volume\
                                \ simplex (which cannot span sufficient basis vectors)."


leavesBarycenter :: WithField ℝ Manifold x => NonEmpty x -> x
leavesBarycenter (x :| xs) = x .+~^ sumV [x'–x | x'<-xs] ^/ (n+1)
 where n = fromIntegral $ length xs
       x' – x = case x'.-~.x of {Option(Just v)->v}

-- simplexShade :: forall x n . (KnownNat n, WithField ℝ Manifold x)
simplexBarycenter :: forall x n . (KnownNat n, WithField ℝ Manifold x) => Simplex n x -> x
simplexBarycenter = bc 
 where bc (ZS x) = x
       bc (x :<| xs') = x .+~^ sumV [x'–x | x'<-splxVertices xs'] ^/ (n+1)
       
       Tagged n = theNatN :: Tagged n ℝ
       x' – x = case x'.-~.x of {Option(Just v)->v}

toISimplex :: forall x n . (KnownNat n, WithField ℝ Manifold x)
                 => Metric x -> Simplex n x -> ISimplex n x
toISimplex m s = ISimplex $ fromEmbedProject fromBrc toBrc
 where bc = simplexBarycenter s
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
         _       -> empty
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
 where m = euclideanMetric t

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
partitionsOfFstLength n (x:xs) = ( first (x:) <$> partitionsOfFstLength (n-1) xs )
                              ++ ( second (x:) <$> partitionsOfFstLength n xs )

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
 deriving (Generic, Hask.Functor, Hask.Foldable, Hask.Traversable)
instance (NFData x, Hask.Foldable c, Hask.Foldable b) => NFData (GenericTree c b x) where
  rnf (GenericTree t) = rnf $ toList t
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



-- | Essentially the same as @(x,y)@, but not considered as a product topology.
--   The 'Semimanifold' etc. instances just copy the topology of @x@, ignoring @y@.
data x`WithAny`y
      = WithAny { _untopological :: y
                , _topological :: !x  }
 deriving (Hask.Functor, Show, Generic)

instance (NFData x, NFData y) => NFData (WithAny x y)

instance (Semimanifold x) => Semimanifold (x`WithAny`y) where
  type Needle (WithAny x y) = Needle x
  type Interior (WithAny x y) = Interior x `WithAny` y
  WithAny y x .+~^ δx = WithAny y $ x.+~^δx
  fromInterior (WithAny y x) = WithAny y $ fromInterior x
  toInterior (WithAny y x) = fmap (WithAny y) $ toInterior x
  translateP = tpWD
   where tpWD :: ∀ x y . Semimanifold x => Tagged (WithAny x y)
                            (Interior x`WithAny`y -> Needle x -> Interior x`WithAny`y)
         tpWD = Tagged `id` \(WithAny y x) δx -> WithAny y $ tpx x δx
          where Tagged tpx = translateP :: Tagged x (Interior x -> Needle x -> Interior x)
            
instance (PseudoAffine x) => PseudoAffine (x`WithAny`y) where
  WithAny _ x .-~. WithAny _ ξ = x.-~.ξ

instance (AffineSpace x) => AffineSpace (x`WithAny`y) where
  type Diff (WithAny x y) = Diff x
  WithAny _ x .-. WithAny _ ξ = x.-.ξ
  WithAny y x .+^ δx = WithAny y $ x.+^δx 

instance (VectorSpace x, Monoid y) => VectorSpace (x`WithAny`y) where
  type Scalar (WithAny x y) = Scalar x
  μ *^ WithAny y x = WithAny y $ μ*^x 

instance (AdditiveGroup x, Monoid y) => AdditiveGroup (x`WithAny`y) where
  zeroV = WithAny mempty zeroV
  negateV (WithAny y x) = WithAny y $ negateV x
  WithAny y x ^+^ WithAny υ ξ = WithAny (mappend y υ) (x^+^ξ)

instance (AdditiveGroup x) => Hask.Applicative (WithAny x) where
  pure x = WithAny x zeroV
  WithAny f x <*> WithAny t ξ = WithAny (f t) (x^+^ξ)
  
instance (AdditiveGroup x) => Hask.Monad (WithAny x) where
  return x = WithAny x zeroV
  WithAny y x >>= f = WithAny r $ x^+^q
   where WithAny r q = f y

shadeWithAny :: y -> Shade x -> Shade (x`WithAny`y)
shadeWithAny y (Shade x xe) = Shade (WithAny y x) xe

shadeWithoutAnything :: Shade (x`WithAny`y) -> Shade x
shadeWithoutAnything (Shade (WithAny _ b) e) = Shade b e

constShaded :: y -> ShadeTree x -> x`Shaded`y
constShaded y = unsafeFmapTree (WithAny y<$>) id (shadeWithAny y)

stripShadedUntopological :: x`Shaded`y -> ShadeTree x
stripShadedUntopological = unsafeFmapTree (fmap _topological) id shadeWithoutAnything

-- | This is to 'ShadeTree' as 'Data.Map.Map' is to 'Data.Set.Set'.
type x`Shaded`y = ShadeTree (x`WithAny`y)

stiWithDensity :: (WithField ℝ Manifold x, WithField ℝ LinearManifold y)
         => x`Shaded`y -> x -> Cℝay y
stiWithDensity (PlainLeaves lvs)
  | [locShape@(Shade baryc expa)] <- pointsShades $ _topological <$> lvs
       = let nlvs = fromIntegral $ length lvs :: ℝ
             indiShapes = [(Shade p expa, y) | WithAny y p <- lvs]
         in \x -> let lcCoeffs = [ occlusion psh x | (psh, _) <- indiShapes ]
                      dens = sum lcCoeffs
                  in mkCone dens . linearCombo . zip (snd<$>indiShapes)
                       $ (/dens)<$>lcCoeffs
stiWithDensity (DisjointBranches _ lvs)
           = \x -> foldr1 qGather $ (`stiWithDensity`x)<$>lvs
 where qGather (Cℝay 0 _) o = o
       qGather o _ = o
stiWithDensity (OverlappingBranches n (Shade (WithAny _ bc) extend) brs) = ovbSWD
 where ovbSWD x = case x .-~. bc of
           Option (Just v)
             | dist² <- metricSq ε v
             , dist² < 9
             , att <- exp(1/(dist²-9)+1/9)
               -> qGather att $ fmap ($x) downPrepared
           _ -> coneTip
       ε = recipMetric extend
       downPrepared = dp =<< brs
        where dp (DBranch _ (Hourglass up dn))
                 = fmap stiWithDensity $ up:|[dn]
       qGather att contribs = mkCone (att*dens)
                 $ linearCombo [(v, d/dens) | Cℝay d v <- NE.toList contribs]
        where dens = sum (hParamCℝay <$> contribs)

stiAsIntervalMapping :: (x ~ ℝ, y ~ ℝ)
            => x`Shaded`y -> [(x, ((y, Diff y), Linear ℝ x y))]
stiAsIntervalMapping = twigsWithEnvirons >=> pure.snd.fst >=> completeTopShading >=> pure.
             \(Shade' (xloc, yloc) shd)
                 -> ( xloc, ( (yloc, recip $ metric shd (0,1))
                            , case covariance (recipMetric' shd) of
                                {Option(Just j)->j} ) )

smoothInterpolate :: (WithField ℝ Manifold x, WithField ℝ LinearManifold y)
             => NonEmpty (x,y) -> x -> y
smoothInterpolate l = \x ->
             case ltr x of
               Cℝay 0 _ -> defy
               Cℝay _ y -> y
 where defy = linearCombo [(y, 1/n) | WithAny y _ <- l']
       n = fromIntegral $ length l'
       l' = (uncurry WithAny . swap) <$> NE.toList l
       ltr = stiWithDensity $ fromLeafPoints l'


spanShading :: ∀ x y . (WithField ℝ Manifold x, WithField ℝ Manifold y)
          => (Shade x -> Shade y) -> ShadeTree x -> x`Shaded`y
spanShading f = unsafeFmapTree addYs id addYSh
 where addYs :: NonEmpty x -> NonEmpty (x`WithAny`y)
       addYs l = foldr (NE.<|) (fmap ( WithAny ymid) l     )
                               (fmap (`WithAny`xmid) yexamp)
          where [xsh@(Shade xmid _)] = pointsCovers $ toList l
                Shade ymid yexpa = f xsh
                yexamp = [ ymid .+~^ σ*^δy
                         | δy <- eigenSpan yexpa, σ <- [-1,1] ]
       addYSh :: Shade x -> Shade (x`WithAny`y)
       addYSh xsh = shadeWithAny (_shadeCtr $ f xsh) xsh
                      


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

