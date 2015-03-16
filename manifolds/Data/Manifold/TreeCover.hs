-- |
-- Module      : Data.Manifold.TreeCover
-- Copyright   : (c) Justus Sagemüller 2015
-- License     : GPL v3
-- 
-- Maintainer  : (@) sagemueller $ geo.uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 
{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE UndecidableInstances     #-}
{-# LANGUAGE StandaloneDeriving       #-}
{-# LANGUAGE DeriveGeneric            #-}
{-# LANGUAGE DeriveFunctor            #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE FunctionalDependencies   #-}
{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE RankNTypes               #-}
{-# LANGUAGE TupleSections            #-}
{-# LANGUAGE ParallelListComp         #-}
{-# LANGUAGE UnicodeSyntax            #-}
{-# LANGUAGE ConstraintKinds          #-}
{-# LANGUAGE PatternGuards            #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE ScopedTypeVariables      #-}
{-# LANGUAGE RecordWildCards          #-}
{-# LANGUAGE DataKinds                #-}


module Data.Manifold.TreeCover (
       -- * Shades 
         Shade, shadeCtr, shadeExpanse, fullShade, pointsShades
       -- * Shade trees
       , ShadeTree(..), fromLeafPoints
       -- * Simple view helpers
       , onlyNodes
       -- ** Auxiliary types
       , SimpleTree, Trees, NonEmptyTree, GenericTree(..)
    ) where


import Data.List
import Data.Maybe
import qualified Data.Map as Map
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
import Data.Manifold.PseudoAffine

import qualified Prelude as Hask
import qualified Control.Monad as Hask
import qualified Data.Foldable as Hask

import Control.Category.Constrained.Prelude hiding ((^))
import Control.Arrow.Constrained
import Control.Monad.Constrained
import Data.Foldable.Constrained

import GHC.TypeLits
import GHC.Generics (Generic)


-- | Possibly / Partially / asymPtotically singular metric.
data PSM x = PSM {
       psmExpanse :: HerMetric' (PseudoDiff x)
     , relevantEigenspan :: [DualSpace (PseudoDiff x)]
     }
       

-- | A 'Shade' is a very crude description of a region within a manifold. It
--   can be interpreted as either an ellipsoid shape, or as the Gaussian peak
--   of a normal distribution (use <http://hackage.haskell.org/package/manifold-random>
--   for actually sampling from that distribution).
-- 
--   For a /precise/ description of an arbitrarily-shaped connected subset of a manifold,
--   there is 'Region', whose implementation is vastly more complex.
data Shade x = Shade { shadeCtr :: x
                     , shadeExpanse' :: PSM x }

shadeExpanse :: Shade x -> HerMetric' (PseudoDiff x)
shadeExpanse (Shade _ (PSM e _)) = e

fullShade :: RealPseudoAffine x => x -> HerMetric' (PseudoDiff x) -> Shade x
fullShade ctr expa = Shade ctr (PSM expa (eigenCoSpan expa))

subshadeId :: RealPseudoAffine x => Shade x -> x -> Int
subshadeId (Shade c (PSM _ expvs)) = \x
             -> case x .-~. c of
                 Option (Just v) -> let (iu,vl) = maximumBy (comparing $ abs . snd)
                                                   $ zip [0,2..] (map (v <.>^) expvs)
                                    in iu + if vl>0 then 1 else 0
                 _ -> -1
                 


-- | Attempt to find a 'Shade' that &#x201c;covers&#x201d; the given points.
--   At least in an affine space (and thus locally in any manifold), this can be used to
--   estimate the parameters of a normal distribution from which some points were
--   sampled.
-- 
--   For /nonconnected/ manifolds it will be necessary to yield separate shades
--   for each connected component. And for an empty input list, there is no shade!
--   Hence the list result.
pointsShades :: RealPseudoAffine x => [x] -> [Shade x]
pointsShades = map snd . pointsShades'

pseudoECM :: RealPseudoAffine x => NE.NonEmpty x -> (x, ([x],[x]))
pseudoECM (p₀ NE.:| psr) = foldl' ( \(acc, (rb,nr)) (i,p)
                                  -> case p.-~.acc of 
                                      Option (Just δ) -> (acc .+~^ δ^/i, (p:rb, nr))
                                      _ -> (acc, (rb, p:nr)) )
                             (p₀, mempty)
                             ( zip [1..] $ p₀:psr )

pointsShades' :: RealPseudoAffine x => [x] -> [([x], Shade x)]
pointsShades' [] = []
pointsShades' ps = case expa of 
                           Option (Just e) -> (ps, fullShade ctr e)
                                              : pointsShades' unreachable
                           _ -> pointsShades' inc'd ++ pointsShades' unreachable
 where (ctr,(inc'd,unreachable)) = pseudoECM $ NE.fromList ps
       expa = ( (^/ fromIntegral(length ps)) . sumV . map projector' )
              <$> mapM (.-~.ctr) ps
       
  
-- | Check the statistical likelyhood of a point being within a shade.
occlusion :: (PseudoAffine x, HasMetric (PseudoDiff x)
             , s ~ (Scalar (PseudoDiff x)), RealDimension s )
                => Shade x -> x -> s
occlusion (Shade p₀ (PSM δ _)) = occ
 where occ p = case p .-~. p₀ of
         Option(Just vd) -> exp . negate $ metricSq δinv vd
         _               -> zeroV
       δinv = recipMetric δ



data ShadeTree x = PlainLeaves [x]
                 | DisjointBranches Int (NE.NonEmpty (ShadeTree x))
                 | OverlappingBranches Int (Shade x) (NE.NonEmpty (ShadeTree x))
  deriving (Generic)
instance (NFData x) => NFData (ShadeTree x) where
  rnf (PlainLeaves xs) = rnf xs
  rnf (DisjointBranches n bs) = n `seq` rnf (NE.toList bs)
  rnf (OverlappingBranches n sh bs) = n `seq` sh `seq` rnf (NE.toList bs)
  

fromLeafPoints :: RealPseudoAffine x => [x] -> ShadeTree x
fromLeafPoints = \xs -> case pointsShades' xs of
                     [] -> PlainLeaves []
                     [(_,rShade)] -> let trials = spread rShade [] xs
                                     in case reduce rShade trials of
                                         Just (redSh,redBrchs)
                                           -> OverlappingBranches (length xs) redSh
                                                                  (branchProc redBrchs)
                                         _ -> PlainLeaves xs
                     partitions -> DisjointBranches (length xs)
                                   . NE.fromList
                                    $ map (\(xs',pShade) ->
                                       OverlappingBranches (length xs')
                                                           pShade
                                                           (branchProc $ spread pShade [] xs'))
                                       partitions
 where spread shade = foldr (\p -> cons2nth p $ subshadeId shade p)
       branchProc = NE.fromList . map fromLeafPoints
       reduce (Shade _ (PSM _ [])) _ = Nothing
       reduce sh@(Shade ctr (PSM s e)) brCandidates
                 = case findIndex deficient cards of
                     Just idef -> let iv = idef`div`2
                                      i = iv*2; i' = i+1 
                                      sh' = Shade ctr (PSM s $ deleteIds [iv] e)
                                      (reBr, ok) = amputateIds [i,i'] brCandidates
                                  in reduce sh' (spread sh' ok $ join reBr)
                     Nothing   -> Just (sh, brCandidates)
        where (cards, maxCard) = (id&&&maximum) $ map length brCandidates
              deficient c = c^2 <= maxCard + 1
                                           

cons2nth :: a -> Int -> [[a]] -> [[a]]
cons2nth _ n l | n<0 = l
cons2nth x 0 (c:r) = (x:c):r
cons2nth x n [] = cons2nth x n [[]]
cons2nth x n (l:r) = l : cons2nth x (n-1) r


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


xorXChange :: RealPseudoAffine x
              => ShadeTree x -> ShadeTree x -> ( ShadeTree x -- Disjoint part
                                               , ShadeTree x -- Overlapping part
                                               )
xorXChange t₁ t₂ = (undefined, undefined)


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

branchwise :: ∀ r n x . RealPseudoAffine x
         ⇒   (∀ k .  ShadeTree x → Option (Branchwise x r k)       )
           → (∀ k .  r (k-1) → WithBoundary r k → WithBoundary r k
                                              → WithBoundary r k   )
           → ShadeTree x → [r n]
branchwise f c = map (inBoundary . branchResult) . bw
 where bw tr | Option(Just r₀)<-f tr  = [r₀]
       bw (DisjointBranches _ trs) = bw =<< NE.toList trs
       bw (OverlappingBranches _ _ trs) 
           = let brResults = fmap bw trs
             in [ foldr1 (\(Branchwise r bb) (Branchwise r' bb')
                           -> let (bb'', shb) = xorXChange bb bb'
                                  [glue] = branchwise f c shb
                              in Branchwise (c glue r r') bb''
                         ) . join $ NE.toList brResults ]
       bw _ = []

triangBranches :: RealPseudoAffine x
                 => ShadeTree x -> Branchwise x (Triangulation x) n
triangBranches _ = undefined

triangulate :: RealPseudoAffine x
                 => ShadeTree x -> Triangulation x n
triangulate = inBoundary . branchResult . triangBranches

tringComplete :: RealPseudoAffine x
                 => Triangulation x (n-1) -> Triangulation x n -> Triangulation x n
tringComplete (Triangulation trr) (Triangulation tr) = undefined
 where 
       bbSimplices = Map.fromList [(i, Left s) | s <- tr | i <- [0::Int ..] ]
       bbVertices =       [(i, splxVertices s) | s <- tr | i <- [0::Int ..] ]

 

type RealPseudoAffine x
          = (PseudoAffine x, HasMetric (PseudoDiff x), Scalar (PseudoDiff x) ~ ℝ)




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
type NonEmptyTree = GenericTree NE.NonEmpty []
    
newtype GenericTree c b x = GenericTree { treeBranches :: c (x,GenericTree b b x) }
 deriving (Hask.Functor)
instance (Hask.MonadPlus c) => Semigroup (GenericTree c b x) where
  GenericTree b1 <> GenericTree b2 = GenericTree $ Hask.mplus b1 b2
instance (Hask.MonadPlus c) => Monoid (GenericTree c b x) where
  mempty = GenericTree Hask.mzero
  mappend = (<>)
deriving instance Show (c (x, GenericTree b b x)) => Show (GenericTree c b x)

onlyNodes :: RealPseudoAffine x => ShadeTree x -> Trees x
onlyNodes (PlainLeaves []) = GenericTree []
onlyNodes (PlainLeaves ps) = let (ctr,_) = pseudoECM $ NE.fromList ps
                             in GenericTree [ (ctr, GenericTree $ (,mempty) <$> ps) ]
onlyNodes (DisjointBranches _ brs) = Hask.foldMap onlyNodes brs
onlyNodes (OverlappingBranches _ (Shade ctr _) brs)
              = GenericTree [ (ctr, Hask.foldMap onlyNodes brs) ]
