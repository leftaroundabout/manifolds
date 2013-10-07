-- |
-- Module      : Data.Manifold
-- Copyright   : (c) Justus Sagemüller 2013
-- License     : GPL v3
-- 
-- Maintainer  : (@) sagemuej $ smail.uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 


{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE UndecidableInstances     #-}
-- {-# LANGUAGE OverlappingInstances     #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE RankNTypes               #-}
{-# LANGUAGE TupleSections            #-}
{-# LANGUAGE ConstraintKinds          #-}
{-# LANGUAGE PatternGuards            #-}
-- {-# LANGUAGE StandaloneDeriving       #-}
{-# LANGUAGE ScopedTypeVariables      #-}


module Data.Manifold where

import Data.List
import qualified Data.Map as Map
import Data.Maybe
import Data.Function

import qualified Data.Vector as V
import Data.Vector(fromList, toList, (!), singleton)
import qualified Data.Vector.Algorithms.Insertion as VAIns

import Data.VectorSpace
import Data.Basis

import Control.Arrow
import Control.Monad
import Control.Monad.Trans.Maybe
import Control.Comonad

import Debug.Trace




type EuclidSpace v = (HasBasis v, EqFloating(Scalar v), Eq v)
type EqFloating f = (Eq f, Ord f, Floating f)


-- | A chart is a homeomorphism from a connected, open subset /Q/ ⊂ /M/ of
-- an /n/-manifold /M/ to either the open unit disk /Dⁿ/ ⊂ /V/ ≃ ℝ/ⁿ/, or
-- the half-disk /Hⁿ/ = {/x/ ∊ /Dⁿ/: x₀≥0}. In e.g. the former case, 'chartInMap'
-- is thus defined ∀ /v/ ∊ /V/ : |/v/| < 1, while 'chartOutMap p' will yield @Just x@
-- with /x/ ∊ /Dⁿ/ provided /p/ is in /Q/, and @Nothing@ otherwise.
-- Obviously, @fromJust . 'chartOutMap' . 'chartInMap'@ should be equivalent to @id@
-- on /Dⁿ/, and @'chartInMap' . fromJust . 'chartOutMap'@ to @id@ on /Q/.
data Chart :: * -> * where
  Chart :: (Manifold m, v ~ TangentSpace m) =>
        { chartInMap :: v -> m
        , chartOutMap :: m -> Maybe v
        , chartKind :: ChartKind      } -> Chart m
data ChartKind = LandlockedChart  -- ^ A /M/ ⇆ /Dⁿ/ chart, for ordinary manifolds
               | RimChart         -- ^ A /M/ ⇆ /Hⁿ/ chart, for manifolds with a rim

isInUpperHemi :: EuclidSpace v => v -> Bool
isInUpperHemi v = (snd . head) (decompose v) >= 0

rimGuard :: EuclidSpace v => ChartKind -> v -> Maybe v
rimGuard LandlockedChart v = Just v
rimGuard RimChart v
 | isInUpperHemi v = Just v
 | otherwise       = Nothing

chartEnv :: Manifold m => Chart m
               -> (TangentSpace m->TangentSpace m)
               -> m -> Maybe m
chartEnv (Chart inMap outMap chKind) f 
   = fmap inMap . (>>=rimGuard chKind) . fmap f . outMap

chartEnv' :: (Manifold m, Monad f) => Chart m
               -> (TangentSpace m->f(TangentSpace m))
               -> m -> MaybeT f m
chartEnv' (Chart inMap outMap chKind) f x
  = MaybeT $ case outMap x of
              Just w -> liftM (fmap inMap . rimGuard chKind) $ f w
              Nothing -> return Nothing
   

 

type Atlas m = [Chart m]

class (EuclidSpace(TangentSpace m)) => Manifold m where
  type TangentSpace m :: *
  
  localAtlas :: m -> Atlas m
  
--   transferSimplex :: Chart m                  -> Chart m
--                   -> Simplex (TangentSpace m) -> Maybe(Simplex(TangentSpace m))
  
--   triangulation :: m -> Triangulation m
--   triangulation = autoTriangulation
  




data S2 = S2 { ϑParamS2 :: Double -- [0, π[
             , φParamS2 :: Double -- [0, 2π[
             }


instance Manifold S2 where
  type TangentSpace S2 = (Double, Double)
  localAtlas (S2 ϑ φ)
   | ϑ<pi-2     = [ Chart (\(x,y)
                             -> S2(2 * sqrt(x^2+y^2)) (atan2 y x) )
                          (\(S2 ϑ' φ')
                             -> let r=ϑ'/2
                                in guard (r<1) >> Just (r * cos φ', r * sin φ') )
                          LandlockedChart ]
   | ϑ>2        = [ Chart (\(x,y)
                             -> S2(pi - 2*sqrt(x^2+y^2)) (atan2 y x) )
                          (\(S2 ϑ' φ')
                             -> let r=(pi-ϑ')/2
                                in guard (r<1) >> Just (r * cos φ', r * sin φ') )
                          LandlockedChart ]
   | otherwise  = localAtlas(S2 0 φ) ++ localAtlas(S2 (2*pi) φ)






data Simplex p = Simplex {
    subSimplicesMkp :: Array (ClRefSimplex p)
  }

data SubdivAccID = SubdivAccID { 
   subdivFacebasis
 , sdfbSubdiv
 , sdfbSubdivFaceID   :: Int
 } deriving (Eq, Show)
 
data ClRefSimplex p = ClRefSimplex {
    subSimplexInnards :: OpenSimplex p
  , simplexClosureRef :: Array Int
  }
data ClRefSimplexSubdiv p = ClRefSimplexSubdiv {
    simplexSubdivInnards :: OpenSimplex p
  , simplexClosureRefInFace :: Array Int
  , simplexClosureRefInSds  :: Array Int
  }

data OpenSimplex p = SimplexInnards {
    osimplexBarycenter :: p
  , osimplexSubdivs :: Array (Array (ClRefSimplexSubdiv p))
  , osimplexSubdividers :: Array (OpenSimplex p, Array SubdivAccID)
  }

-- class HasSimplices s where
--   onOpenSimplices :: (OpenSimplex p -> OpenSimplex q) -> s p -> s q
--   onSimplices :: (Simplex p -> Simplex q) -> s p -> s q
-- instance HasSimplices Simplex where
--   onOpenSimplices = fmap . onOpenSimplices
--   onSimplices = id
-- 

simplexMainInnard :: Simplex p -> OpenSimplex p
simplexMainInnard = subSimplexInnards . V.head . subSimplicesMkp

subSimplices :: Simplex p -> Array (Simplex p)
subSimplices (Simplex subsMkp) = fmap assembleSub subsMkp
 where assembleSub (ClRefSimplex innard sSubRefs)
          = Simplex $ (ClRefSimplex innard V.empty) `V.cons` fmap reIndex sSubRefs
        where reIndex i = ClRefSimplex thisSubInr $ V.backpermute fwdRefMap thisSubSrs
               where (ClRefSimplex thisSubInr thisSubSrs) = subsMkp ! i
              fwdRefMap = inverseAssoc sSubRefs

zeroSimplex :: p -> Simplex p
zeroSimplex = Simplex . V.singleton . (`ClRefSimplex`V.empty) . zeroOpenSimplex

zeroOpenSimplex :: p -> OpenSimplex p
zeroOpenSimplex p = SimplexInnards p V.empty V.empty

openSimplexDimension :: OpenSimplex p -> Int
openSimplexDimension (SimplexInnards _ subdivs _) 
   = invFactorial (V.length subdivs) - 1

simplexSubdivs :: Simplex p -> Array(Simplex p)
simplexSubdivs s@(Simplex subqs) 
          = V.indexed (V.zip osimplexSubdivs (V.tail subs)) >>= assembleSubdGroup
 where subs = subSimplices s
       refAll = V.enumFromN 1 $ V.length subqs - 1
       mainInr@(SimplexInnards {..}) = subSimplexInnards $ V.head subqs
       assembleSubdGroup (sideID, (sdGroup, side))
         = V.zipWith assembleSubd (sdGroup) (simplexSubdivs side)
        where assembleSubd (ClRefSimplexSubdiv {..}) (Simplex sideSubdSubs)
                = Simplex $ ClRefSimplex subsimplexinnards refAll
                    `V.cons` fmap rerefSubdsubFromFace simplexClosureRefInFace
                    `V.++`   fmap rerefSubdsubFromSds  simplexClosureRefInSds
               where rerefSubdsubFromSds sdID
                        = ClRefSimplex cutWallInr cutWallSubRef
                      where (cutWallInr, cutWallUses) = osimplexSubdividers ! sdID
                            (SubdivAccID{..})
                                 = V.find ((==sideID) . subdivFacebasis) cutWallUses
                            cutWallSubRef = 
                     rerefSubdsubFromFace fcID
                        = ClRefSimplex faceSubdInr $ fmap (+1) faceSubdSubRef
                      where (ClRefSimplex faceSubdInr faceSubdSubRef) 
                                                         = sideSubdSubs ! fcID
         

subdividersWithSubs :: Simplex p -> [(OpenSimplex p, Array (OpenSimplex p))]
subdividersWithSubs = undefined
--   (Simplex subs)
--             = map (second gatherDivSubs) dvds
--  where gatherDivSubs (subSrc@(SubdivAccID{..}):_)
--          = fromSide `V.cons` fromLesserDivs
--         where fromSide = subdivGroups ! subdivFacebasis ! sdfbSubdiv
--               fromLesserDivs = 
--        (SimplexInnards baryc subdivGroups dvds) = V.head subs
-- 
{-# SPECIALIZE invFactorial :: Int -> Int #-}
invFactorial :: Integral i => i->i
invFactorial k = invFact 1 1
 where invFact n j
        | j >= k   = n
        | n'<-n+1  = invFact n' $ j*n'


-- | Note that the 'Functor' instances of 'Simplex' and 'Triangulation'
-- are only vaguely related to the actual category-theoretic /simplicial functor/.
instance Functor Simplex where
  fmap f = Simplex . fmap (fmap f) . subSimplicesMkp

instance Functor ClRefSimplex where
  fmap f (ClRefSimplex si srf) = ClRefSimplex (fmap f si) srf

instance Functor OpenSimplex where
  fmap f (SimplexInnards brc divs dvders)
        = SimplexInnards ( f brc )
                         ( (fmap.fmap.fmap ) f divs   )
                         ( (fmap.first.fmap) f dvders )

instance Comonad OpenSimplex where
  extract (SimplexInnards brc _ _) = brc
  
  duplicate s@(SimplexInnards brc sdGroups subdvds)
   = SimplexInnards s
         ( (fmap.fmap) 
             (\(ClRefSimplex si srf) -> ClRefSimplex (duplicate si) srf )
             sdGroups )
         ( (fmap.first) duplicate subdvds )

-- Works something like the following: 'extract' retrieves the barycenter,
-- 'duplicate' replaces the barycenter of each subsimplex /s/ with all of /s/ itself.
instance Comonad Simplex where
 
  extract (Simplex subs)
   | ClRefSimplex(SimplexInnards baryc _ _)_ <- V.head subs  = baryc
  
  duplicate (Simplex inrs) = duplicat
   where duplicat = Simplex $ fmap lookupSides inrs
         
         dduplicat@(Simplex ddsubs) = fmap duplicate duplicat
         
         lookupSides ( ClRefSimplex (SimplexInnards baryc sdGroups subdvds)
                                    subsubIds                               )
           = ClRefSimplex (SimplexInnards (Simplex $ V.backpermute inrs subsubIds) 
                                          dupdSds dupdSdvds                        )
                          subsubIds
          where dupdSds = V.zipWith recm
                             sdGroups
                             ( fmap (osimplexBarycenter . subSimplexInnards) thisSubSubs )
                thisSubSubs = V.backpermute ddsubs subsubIds
                dupdSdvds = fmap sdFRecm subdvds
                recm subdivs faceBase
                  = V.zipWith recmi subdivs faceSDBases
                 where recmi (ClRefSimplex subdiv subdivMq) faceSubdiv 
                                              = simplexMainInnard dupSub
                        where sdqFaces = fmap fst 
                                          . V.filter (any ((==j) . sdfbSubdiv) . snd)
                                          $ sdGFaces
                              dupSub = duplicate . Simplex 
                                              . fmap (`ClRefSimplex`undefined) $
                                         subdiv 
                                `V.cons` fmap fst (subSimplicesMkp faceSubdiv)
                                    V.++ sdqFaces
                                `V.snoc` zeroOpenSimplex baryc
                       faceSDBases = fmap osimplexBarycenter 
                                       $ fmap fst (subSimplicesMkp faceBase)
                       sdGFaces = V.fromList
                                . filter (any ((==i) . subdivFacebasis) . snd)
                                $ subdvds
                sdFRecm (SimplexInnards b s _, orient) 
                 | V.null s  = (SimplexInnards (zeroSimplex b) V.empty [], orient)
                sdFRecm (_, orient@(SubdivAccID i j k : _)) 
                      = (fst dupSub, orient)
                 where dupSub = (subSimplicesMkp . duplicate . osimplexBarycenter)
                                  (dupdSds ! i ! j) ! k




affineSimplexCone :: forall v . EuclidSpace v => v -> Simplex v -> Simplex v
affineSimplexCone p base@(Simplex baseSubs) = Simplex subs
 where subs = coneFillSubs V.++ baseSubs' `V.snoc` (zeroOpenSimplex p, V.empty)
       coneFillSubs = fmap fillConeSub baseSubs
       fillConeSub (baseSubInr, baseSubqRef) = (csubInr, subqRef)
        where csubInr = undefined
              subqRef = undefined
--                | V.null baseSubqRef
--                    = SimplexInnards lineBaryc lineSubs V.empty
--                        where lineBaryc = midBetween [p, osimplexBarycenter baseSubInr]
--                              lineSubs  = undefined
--                | otherwise
--                    = simplexMainInnard $ affineSimplexCone p baseSubsimplex
              
       baseSubs' = fmap (\(bsinr, bssSubrefs)
                          -> ( bsinr, fmap (+ V.length coneFillSubs) bssSubrefs )
                        ) baseSubs

affineSimplex :: forall v . EuclidSpace v => [v] -> Simplex v
affineSimplex (v:vs) = foldr affineSimplexCone (zeroSimplex v) vs

recalcInnardsAffine :: forall v . EuclidSpace v => Simplex v -> Simplex v
recalcInnardsAffine (Simplex baseSubs) = Simplex $ baseSubs V.// [(0, reMainInr)]
 where properSubs = V.tail baseSubs
       properSubsIds = V.enumFromN 1 $ V.length properSubs
       dim = openSimplexDimension (V.head properSubs) + 1
       reMainInr = ( SimplexInnards barycenter subdivs subdvds
                   , properSubsIds                             ) 
       barycenter = zeroOpenSimplex . midBetween . V.toList
                      $ fmap (osimplexBarycenter . fst) properSubs
       subdivs = V.imap bSdGroups properSubs
        where bSdGroups i = undefined
       subdvds = V.toList $ V.zip properSubsIds properSubs >>= extrDividers
        where extrDividers (im1, (sideQInr, sideQRx))
                = ( if openSimplexDimension sideQInr < dim-1
                     then undefined
                     else id )
                    $ fmap coneOnSideDvd (osimplexSubdividers sideQInr)
               where 
                     coneOnSideDvd (sdvdInr, sdvdSrc)
                      = ( simplexMainInnard $ recalcInnardsAffine hollowDvd
                        , fmap reref sdvdSrc                                )
                      where reref = undefined
                            hollowDvd = Simplex $
                                        undefined
                                  -- The subdivider's innard (to be filled by 'recalcInnardsAffine' recursively).
                               `V.cons` undefined
                                  -- The subdivider's faces, which are lesser subdividers themselves already calculated.
                               V.++    (sdvdInr, enumFromN (divDim+1) divDim) 
                                  -- The known face as taken from the given shell.
                               `V.cons` undefined
                                  -- The 
                               `V.snoc` (barycenter, [])
                                  -- The vertex at the outer simplex' barycenter.
                            divDim = openSimplexDimension sdvdInr + 1
                            divInSideSubs = undefined
                            completionSrc = head sdvdSrc
                            (SimplexInnards _ sideSubdGroups sideDividers) = sideQInr
                  



class LtdShow s where
  ltdShow :: Int -> s -> String

ltdShows :: LtdShow s => Int -> s -> ShowS
ltdShows n o s = ltdShow n o ++ s

ltdPrint :: LtdShow s => Int -> s -> IO()
ltdPrint n = putStrLn . ltdShow n

newtype LtdShowT a = LtdShow { runLtdShow :: a }

instance (Show a) => LtdShow ( LtdShowT a ) where
  ltdShow n = go "" (n*16) . show . runLtdShow where
       go ('{':um) 0 _ = "..}" ++ go um 0 []
       go ('[':um) 0 _ = "..]" ++ go um 0 []
       go ('(':um) 0 _ = "..)" ++ go um 0 []
       go [] n _ | n<=0     = "..."
       go unmatched n (c:cs)
        | c `elem` "([{"   = c : go (c:unmatched) (n-8) cs
       go ('{':um) n ('}':cs) = '}' : go um (n-1) cs
       go ('[':um) n (']':cs) = ']' : go um (n-1) cs
       go ('(':um) n (')':cs) = ')' : go um (n-1) cs
       go unmatched n (c:cs) = c : go unmatched n' cs
        where n' | c`elem`(['a'..'z']++['A'..'Z']++['0'..'9'])  = n-1
                 | otherwise                                    = n-8
       go [] _ "" = ""
                                      

instance (LtdShow s) => LtdShow (Array s) where
  ltdShow n arr 
     | n<=1, l>0  = "[∘∘{" ++ show l ++ "}∘∘]"
     | otherwise  = ('[':) . V.foldr (("∘ "++).) " ∘]"
                     . V.imap(\i -> ltdShows $ round(
                                     fromIntegral n 
                                      * 2**(-1 - sqrt(fromIntegral i)) ))
                     $ arr
   where l = V.length arr
         
instance (LtdShow l, LtdShow r) => LtdShow (l,r) where
  ltdShow n (l, r) = "(" ++ pShow l ++ ", " ++ pShow r ++ ")"
   where pShow :: LtdShow s => s->String
         pShow = ltdShow $ n`quot`2


instance (Show p) => LtdShow (Simplex p) where
  ltdShow 0 _ = "Simplex (...) (...)"
  ltdShow n (Simplex sinrs) = "Simplex (" ++ pShow (fmap fst sinrs) ++ ")"
   where pShow :: LtdShow s => s->String
         pShow = ltdShow $ n`quot`2

instance (Show p) => LtdShow (OpenSimplex p) where
  ltdShow 0 _ = "SI (...) (...) (...)"
  ltdShow n (SimplexInnards brc sds dvds) = "SI " ++ show brc
                                      ++ pShow sds
                                      ++ " " ++ pShow (V.fromList dvds)
   where pShow :: LtdShow s => s->String
         pShow = ltdShow $ n`quot`3
                                      
instance (Show p) => LtdShow [p] where
  ltdShow n l = "[" ++ lsh' n l "]"
   where lsh' 0 _ = ("... "++)
         lsh' _ [] = id
         lsh' n (x:xs) = ((show x ++ ", ") ++) . lsh' (n-1) xs

      
              
midBetween :: (VectorSpace v, Fractional(Scalar v)) => [v] -> v
midBetween vs = sumV vs ^/ (fromIntegral $ length vs)
       

  


-- | Remove \"gaps\" in an array of unique numbers, i.e. the set of elements
-- is mapped strict-monotonically to @[0 .. length arr - 1]@.
sediment :: Array Int -> Array Int
sediment = V.map fst . saSortBy(compare`on`fst.snd)
             . V.indexed . saSortBy(compare`on`snd) . V.indexed


-- | 'inverseAssoc' is basically the inverse of 'Data.Vector.backpermute'.
inverseAssoc :: Array Int -> Array Int
inverseAssoc = V.fromList . psFillGaps . V.toList
                    . saSortBy (compare`on`snd) . V.indexed
 where psFillGaps [(e,_)] = [e]
       psFillGaps ( (a,α) : r@((b,β):_) )
        | β == succ α  = a : psFillGaps r
        | otherwise    = a : psFillGaps ( (undefined, succ α) : r )





 


infixl 7 ↺↺, ↺↻
class Permutation π where
  (↺↺) :: π -> π -> π
  (↺↻) :: π -> π -> π
  p↺↻q = p ↺↺ invPerm q
  invPerm :: π -> π




deleteAt :: Int -> [a] -> [a]
deleteAt n = uncurry(++) . second tail . splitAt n

reglueRemAt :: Int -> [a] -> [a]
reglueRemAt n = uncurry(flip(++)) . second tail . splitAt n

-- | @'omit1s' [0,1,2,3] = [[1,2,3], [0,2,3], [0,1,3], [0,1,2]]@
omit1s :: [a] -> [[a]]
omit1s [] = []
omit1s [_] = [[]]
omit1s (v:vs) = vs : map(v:) (omit1s vs)

-- | @'gapPositions' [0,1,2,3] = [[1,2,3], [2,3,0], [3,0,1], [0,1,2]]@
gapPositions :: [a] -> [[a]]
gapPositions = gp id
 where gp rq (v:vs) = (vs++rq[]) : gp (rq.(v:)) vs
       gp _ _ = []


type Map = Map.Map


type Array = V.Vector


{-# INLINE enumFromN #-}
enumFromN :: Num a => a -> Int -> [a]
enumFromN i0 = V.toList . V.enumFromN i0

saSort :: Ord a => Array a -> Array a
saSort = V.modify VAIns.sort

-- The sorting algorithm of choice is simple insertion sort, because simplices
-- that can feasibly be handled will always have low dimension, so the better
-- complexity of more sophisticated sorting algorithms is no use on the short
-- vertex arrays.
{-# INLINE saSortBy #-}
saSortBy :: VAIns.Comparison a -> Array a -> Array a
saSortBy cmp = V.modify $ VAIns.sortBy cmp


-- | Unlike the related 'zipWith', 'associateWith' \"spreads out\" the shorter
-- list by duplicating elements, before merging, to minimise the number of
-- elements from the longer list which aren't used.
associateWith :: (a->b->c) -> [a] -> [b] -> [c]
associateWith f a b
  | lb>la      = spreadn(lb`quot`la) f a b
  | otherwise  = spreadn(la`quot`lb) (flip f) b a
 where la = length a; lb = length b
       spreadn n f' = go
        where go (e:es) t
               | (et, tr) <- splitAt n t  
                    = foldr((:) . f' e) (go es tr) et
              go _ _ = []
              
-- | @associate = associateWith (,)@.
associate :: [a] -> [b] -> [(a,b)]
associate = associateWith (,)

associaterSectorsWith :: (a->[b]->c) -> [a] -> [b] -> [c]
associaterSectorsWith f a b = spreadn(lb`quot`la) a b
 where la = length a; lb = length b
       spreadn n (e:es) t
        | (et, tr) <- splitAt n t  = f e et : spreadn n es tr
       spreadn _ _ _ = []

associaterSectors :: [a] -> [b] -> [(a,[b])]
associaterSectors = associaterSectorsWith (,)
       
associatelSectorsWith :: ([a]->b->c) -> [a] -> [b] -> [c]
associatelSectorsWith f = flip (associaterSectorsWith $ flip f)

associatelSectors :: [a] -> [b] -> [([a],b)]
associatelSectors = associatelSectorsWith (,)

partitions :: Int -> [a] -> [[a]]
partitions n = go
 where go [] = []
       go l | (chunk,rest) <- splitAt n l  = chunk : go rest

divide :: Int -> [a] -> [[a]]
divide n ls = partitions(length ls`div`n) ls
 
 
mapOnNth :: (a->a) -> Int -> [a] -> [a]
mapOnNth f 0 (l:ls) = f l : ls
mapOnNth f n (l:ls) = l : mapOnNth f (n-1) ls
mapOnNth _ _   []   = []

mapExceptOnNth :: (a->a) -> Int -> [a] -> [a]
mapExceptOnNth f 0 (l:ls) = l : map f ls
mapExceptOnNth f n (l:ls) = f l : mapOnNth f (n-1) ls
mapExceptOnNth _ _   []   = []

{-# INLINE coordMap #-}
coordMap :: HasBasis v => ([Scalar v] -> [Scalar v]) -> v -> v
coordMap f = recompose . uncurry zip . second f . unzip . decompose


type Endomorphism a = a->a



data Space2D = Space2D Double Double
       deriving(Eq, Show)
data Space2DIndex = X' | Y

instance AdditiveGroup Space2D where
  zeroV = Space2D 0 0
  Space2D x y ^+^ Space2D x' y' = Space2D (x+x') (y+y')
  negateV (Space2D x y) = Space2D (-x) (-y)
instance VectorSpace Space2D where
  type Scalar Space2D = Double
  λ *^ Space2D x y = Space2D (λ*x) (λ*y)
instance HasBasis Space2D where
  type Basis Space2D = Space2DIndex
  basisValue X' = Space2D 1 0
  basisValue Y  = Space2D 0 1
  decompose (Space2D x y) = [(X', x), (Y, y)]
  decompose' (Space2D x _) X' = x
  decompose' (Space2D _ y) Y  = y


data Space3D = Space3D Double Double Double
       deriving(Eq, Show)
data Space3DIndex = X'' | Y' | Z

instance AdditiveGroup Space3D where
  zeroV = Space3D 0 0 0
  Space3D x y z ^+^ Space3D x' y' z' = Space3D (x+x') (y+y') (z+z')
  negateV (Space3D x y z) = Space3D (-x) (-y) (-z)
instance VectorSpace Space3D where
  type Scalar Space3D = Double
  λ *^ Space3D x y z = Space3D (λ*x) (λ*y) (λ*z)
instance HasBasis Space3D where
  type Basis Space3D = Space3DIndex
  basisValue X'' = Space3D 1 0 0
  basisValue Y'  = Space3D 0 1 0
  basisValue Z   = Space3D 0 0 1
  decompose (Space3D x y z) = [(X'', x), (Y', y), (Z, z)]
  decompose' (Space3D x _ _) X'' = x
  decompose' (Space3D _ y _) Y'  = y
  decompose' (Space3D _ _ z) Z   = z
