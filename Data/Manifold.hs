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
  
  triangulation :: m -> Triangulation m
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




type FastNub a = (Eq a, Ord a) -- S̶h̶o̶u̶l̶d̶ ̶r̶e̶a̶l̶l̶y̶ ̶b̶e̶ ̶(̶E̶q̶ ̶a̶,̶̶ ̶H̶a̶s̶h̶a̶b̶l̶e̶ ̶a̶)̶
fastNub :: FastNub a => [a] -> [a]
fastNub = map head . group . sort

-- | Simply a merge sort that discards equivalent elements.
fastNubBy :: (a->a->Ordering) -> [a] -> [a]
fastNubBy _ [] = []
fastNubBy _ [e] = [e]
fastNubBy cmp es = merge(fastNubBy cmp lhs)(fastNubBy cmp rhs)
 where (lhs,rhs) = splitAt (length es `quot` 2) es
       merge [] rs = rs
       merge ls [] = ls
       merge (l:ls) (r:rs) = case cmp l r of
                              LT -> l : merge ls (r:rs)
                              GT -> r : merge (l:ls) rs
                              EQ -> merge (l:ls) rs

-- | Like 'fastNubBy', but doesn't just discard duplicates but \"merges\" them.
-- @'fastNubBy' cmp = cmp `'fastNubByWith'` 'const'@.
fastNubByWith :: (a->a->Ordering) -> (a->a->a) -> [a] -> [a]
fastNubByWith _ _ [] = []
fastNubByWith _ _ [e] = [e]
fastNubByWith cmp cmb es = merge(fastNubByWith cmp cmb lhs)(fastNubByWith cmp cmb rhs)
 where (lhs,rhs) = splitAt (length es `quot` 2) es
       merge [] rs = rs
       merge ls [] = ls
       merge (l:ls) (r:rs) = case cmp l r of
                              LT -> l : merge ls (r:rs)
                              GT -> r : merge (l:ls) rs
                              EQ -> merge (cmb l r : ls) rs

sfGroupBy :: (a->a->Ordering) -> [a] -> [[a]]
sfGroupBy cmp = fastNubByWith (cmp`on`head) (++) . map(:[])


data Simplex p = Simplex { subSimplices :: [SimplexInnards p] }

data SimplexInnards p = SimplexInnards
    simplexBarycenter :: p
  , simplexSubdivs :: [SimplexInnards p]
  , simplexSubdividers :: [SimplexInnards p]
  } 


-- | Note that the 'Functor' instances of 'Simplex' and 'Triangulation'
-- are only vaguely related to the actual category-theoretic /simplicial functor/.
instance Functor Simplex where
  fmap f(Simplex edges innards) = Simplex (fmap f edges) (fmap (fmap f) innards)

instance Functor SimplexInnards where
  fmap f (SimplexInnards brc divs dvders)
       = SimplexInnards (f brc) (fmap (fmap f) divs) (fmap (fmap f) dvders)

-- Should look something like the following: 'extract' retrieves the barycenter,
-- 'duplicate' replaces the barycenter of each subsimplex /s/ with all of /s/ itself.
instance Comonad Simplex where
  extract (Simplex (SimplexInnards baryc _ _:_)) = baryc
  duplicate s@(Simplex inrs) = Simplex $ fmap (lookupSidesIn s) inrs





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
  ltdShow n (Simplex [p] []) = "S0 (" ++ show p ++ ")"
  ltdShow 0 _ = "Simplex (...) (...)"
  ltdShow n (Simplex sss inrs) = "SN " ++ pShow sss
                          ++ " (" ++ pShow inrs ++ ")"
   where pShow :: LtdShow s => s->String
         pShow = ltdShow $ n`quot`2

instance (Show p) => LtdShow (SimplexInnards p) where
  ltdShow 0 _ = "SI (...) (...)"
  ltdShow n (SimplexInnards sds dvds) = "SI " ++ pShow sds
                                      ++ " " ++ pShow dvds
   where pShow :: LtdShow s => s->String
         pShow = ltdShow $ n`quot`2
                                      

simplexBoundary :: Simplex p -> Triangulation p
simplexBoundary (SimplexN bnds _) = wronglyDisjointSimplicesTriangulation bnds
simplexBoundary (PermutedSimplex _ s) = simplexBoundary s
simplexBoundary s = Triangulation $ V.singleton (s, [])


simplexDimension :: Simplex p -> Int
simplexDimension (Simplex0 _) = 0
simplexDimension (SimplexN faces _) = V.length faces - 1
simplexDimension (PermutedSimplex _ s) = simplexDimension s

simplexBarySubdivNSimplices :: Simplex p -> Int
simplexBarySubdivNSimplices (Simplex0 _) = 1
simplexBarySubdivNSimplices (SimplexN _ (SimplexInnards sds _)) = V.length sds
simplexBarySubdivNSimplices (PermutedSimplex _ s) = simplexBarySubdivNSimplices s


shareSubSplxStraighly :: SubSimplexSideShare -> SimplexSideShare 
shareSubSplxStraighly ssh = SimplexSideShare ssh SimplexIdPermutation

traceSubsplxPath :: [Int] -> Endomorphism SubSimplexSideShare
traceSubsplxPath idId sd = foldr ShareInFace sd idId





data SimplexNeighbourRef = SimplexNeighbourRef
  { boundarySubsimplexId :: Int
  , simplexNeighbourIdInTriang :: Int
  , simplexNeighbourBndSubsplxId :: Int
  , neighbourSimplexBdnGlueOrientation :: SimplexPermutation
  }

newtype Triangulation p = Triangulation
    { simplicialComplex :: Array (Simplex p, [(Int, SimplexPermutation)])
    }

sComplexSimplices :: Triangulation p -> Array(Simplex p)
sComplexSimplices = V.map fst . simplicialComplex

instance (Show p) => LtdShow (Triangulation p) where
  ltdShow n (Triangulation cmplx)
      = "Triang "++ltdShow n (V.map (second LtdShow) cmplx)
    
disjointTriangulation :: Triangulation p -> Triangulation p -> Triangulation p
disjointTriangulation (Triangulation sps1) (Triangulation sps2)
   = Triangulation $ sps1 V.++ V.map(second . map $ first(+l1)) sps2
 where l1 = V.length sps1

autoglueTriangulation :: Eq p => [Simplex p] -> Triangulation p
autoglueTriangulation = Triangulation . V.map(,[]) . fromList

wronglyDisjointTriangulationCons :: Simplex p -> Triangulation p -> Triangulation p
wronglyDisjointTriangulationCons s
     = disjointTriangulation (Triangulation $ V.singleton(s,[]))

wronglyDisjointSimplicesTriangulation :: Array (Simplex p) -> Triangulation p
wronglyDisjointSimplicesTriangulation = Triangulation . V.map (,[])

singletonTriangulation :: Simplex p -> Triangulation p
singletonTriangulation = Triangulation . V.singleton . (,[])

infixr 5 ⊿⌧,⊿⊳

(⊿⌧) :: Eq p => Simplex p -> Triangulation p -> Triangulation p
(⊿⌧) = wronglyDisjointTriangulationCons

(⊿⊳) :: Eq p => Simplex p -> Simplex p -> Triangulation p
s1 ⊿⊳ s2 = wronglyDisjointSimplicesTriangulation $ V.fromList [s1, s2]


triangulationVertices :: Eq p => Triangulation p -> [p]
triangulationVertices (Triangulation sComplex) 
    = nub $ simplexVertices =<< toList (V.map fst sComplex)

simplexBarycentricSubdivision :: Simplex p -> Triangulation p
simplexBarycentricSubdivision s@(SimplexN _ (SimplexInnards subdiv _))
         = wronglyDisjointSimplicesTriangulation $ fmap finalise subdiv
    where finalise(SubSimplex inrs bounds)
                          = SimplexN (fmap (findSharedSide s) bounds) inrs
 
simplexBarycentricSubdivision (PermutedSimplex _ s) = simplexBarycentricSubdivision s
simplexBarycentricSubdivision s0 = singletonTriangulation s0

barycentricSubdivisions :: Triangulation p -> Triangulation p
barycentricSubdivisions t
  = wronglyDisjointSimplicesTriangulation
      $ sComplexSimplices t >>= sComplexSimplices . simplexBarycentricSubdivision

nStepBarycentricSubdivisions :: Int -> Triangulation p -> Triangulation p
nStepBarycentricSubdivisions 0 = id
nStepBarycentricSubdivisions n = nStepBarycentricSubdivisions (n-1) . barycentricSubdivisions
    

instance Functor Triangulation where
  fmap f(Triangulation c) = Triangulation(fmap(first $ fmap f)c)


data IndexedVert p = IndexedVert {indexedVertex::p, vertexIndex::Int}
instance Eq (IndexedVert p) where {(==) = (==)`on`vertexIndex}
instance Ord (IndexedVert p) where {compare = compare`on`vertexIndex}

-- The sketch below is not good. A better one might be the following,
-- procedural-style:
-- while (∃ wrong-rim):
--    pick a rim subsimplex to build a cone c on top of, such that
--    the number of other rim-simplices which can also build a cone to
--    the tip of c is maximised.
-- 
-- autoTriangulation :: forall m . Manifold m => m -> Triangulation m
-- autoTriangulation m = undefined -- Triangulation
--  where 
--        basisChart :: Chart m
--        basisChart = head $ localAtlas m
--        
--        chartCovers :: Chart m -> m -> Bool
--        chartCovers (Chart _ outMap _) p = isJust $ outMap p
--        
--        expandablyRim :: Chart m -> [m] -> [m]
--        expandablyRim (Chart inMap outMap chKind) = 
--        
--        basisSimplexVerts :: [m]
--        basisSimplexVerts = liftM fromJust . runMaybeT $ chartEnv' basisChart spreadStBall m
--        
--        spreadStBall :: EuclidSpace v => v -> [v]
--        spreadStBall v = map recompose $
--                    zeroP : map dimSingP decomp'
--         where zeroP = map (\(b, _) -> (b,0)) decomp
--               dimSingP(n,_) = map z decomp'
--                where z(n',(b,q))
--                       | n'/=n          = (b,0)
--                       | q'<-signum q
--                       , q'/=0          = (b, q'*0.9)
--                       | otherwise      = (b, 0.9)
--               decomp = decompose v
--               decomp' = zip [0..] decomp
              

ballAround :: EuclidSpace v
    =>  Scalar v        -- ^ Size of the ball to be created
     -> v               -- ^ Center of the ball (this also defines what space we're in, and thereby the dimension of the ball)
     -> Triangulation v -- ^ A barycentrically-subdividable simplicial complex triangulating the ball in question
r `ballAround`p = fmap ((^+^p) . l₁tol₂) 
                    $ wronglyDisjointSimplicesTriangulation orthoplex
 where orthoplex
        | [] <- vDecomp  = singleton $ Simplex0 p
        | otherwise      = orthSides
         
       vDecomp = decompose p
       vBasis = map fst vDecomp
       n = length $ vDecomp
       
       orthSides = V.map (affineSimplex . (p:)) $ fromList orthVertices
       
       orthVertices = (map.map) ( recompose . zip vBasis )
                            $ map directSide orthDirections
       directSide [] = []
       directSide (c:cs) = (c:map(const 0)cs) : map(0:)(directSide cs)
       orthDirections = map (take n) . take (2^n)     -- e.g. [ [-r,-r], [-r, r], [ r,-r], [ r, r] ]
                      . fix.fix $ \q ~(l:ls) -> (-r:l) : (r:l) : q ls
       
       l₁tol₂ = coordMap inflate
        where inflate vl = map scale vl
               where l₁ = sum $ map abs vl
                     l₂ = sqrt . sum $ map (^2) vl
                     scale | l₂>0       = (* (l₁ / l₂))
                           | otherwise = id



affineSimplex :: forall v . EuclidSpace v => [v] -> Simplex v
affineSimplex' :: forall v . EuclidSpace v => [v] -> Map SubSplxIndex (Simplex v)
-- affineSimplex _ = undefined
-- affineSimplex [v] = Simplex0 v
affineSimplex vertices = affineSimplex' vertices Map.! SubSplxIndex[]
affineSimplex' vertices = subLookup
 where 
       subLookup :: Map SubSplxIndex (Simplex v)
       subLookup = prepareSubs vertices
       
       prepareSubs vs = foldr mpIns Map.empty unqSubGroups
         where 
               unqSubGroups :: [ (Simplex v, [(SubSplxIndex, SimplexPermutation)]) ]
               unqSubGroups
                  = map ( first $ \(SubSplxIndex path) 
                      -> constructSubAt path vs (SubSplxIndex . (path++) )
                     ) subgroups
                     
               constructSubAt :: [Int] -> [v] -> ([Int]->SubSplxIndex) -> Simplex v
               constructSubAt (dir:path) vs' pb
                  = constructSubAt path (reglueRemAt dir vs') pb
               constructSubAt [] vs' pb 
                  = spannedAffineSplx vs' $ (subLookup Map.!) . pb
                  
               mpIns :: (Simplex v, [(SubSplxIndex, SimplexPermutation)])
                             -> Endomorphism (Map SubSplxIndex (Simplex v))
               mpIns (ref, slaves) prev 
                  = foldr (\(idx,π) -> Map.insert idx (permuteSimplex π ref) ) prev slaves
                              
               subgroups :: [(SubSplxIndex, [(SubSplxIndex,SimplexPermutation)])]
               subgroups = distinctSubsplxGroups dimension
               
               dimension :: Int
               dimension = length vs - 1
       
       
spannedAffineSplx :: forall v. EuclidSpace v 
            => [v]                 -- ^ The vertices.
            -> ([Int]->Simplex v)  -- ^ Lookup function for the required sides.
            -> Simplex v
spannedAffineSplx [v] _ = Simplex0 v
spannedAffineSplx vs subF = result
  where
        result :: Simplex v
        result = SimplexN (fromList theFaces)
                              innards
        
        innards :: SimplexInnards v
        innards = SimplexInnards subdivs subdvds
        
        subdivs, subdvds :: Array (SubSimplex v)
        subdivs = V.map snd $ conesClass buildSDCones ShareSubdivision isFcPath
        
        conesClass :: ( Simplex v -> (SubSimplexSideShare->(Int,Simplex v)) -> (SubSimplexSideShare->SimplexSideShare) -> Array(SubSimplex v) )
                      -> (Int->SubSimplexSideShare) -> ([Int] -> Bool)
                          -> Array(SubSimplexSideShare, SubSimplex v)
        conesClass cnBuilder sbKind cclFilter = do 
             (bsdLookup, base) <- fromList . map(first traceSubsplxPath) 
                                                 $ filter (cclFilter . fst) uniqueSSPs
             let fiLookup = (fst &&& findSharedSide result
                                        . uncurry SimplexSideShare
                                        . first ShareSubdivider    )
                                . subdvdsSel . bsdLookup
             (cbsId, cone) <- V.indexed $ cnBuilder base fiLookup 
                                            (shareSubSplxStraighly . bsdLookup)
             return (bsdLookup $ sbKind cbsId, cone)
        
        subdvds = SimplexBarycenter barycenter
                    `V.cons` V.map snd uniqueSubdvds
        
        subdvdsSel :: SubSimplexSideShare -> (Int, SimplexPermutation)
        subdvdsSel (ShareSubdivider 0) = (0, SimplexIdPermutation)
        subdvdsSel sssh = sel id sssh
         where sel lkls (ShareInFace i sh) = sel (lkls . (i:)) sh
               sel lkls sh = let (SubSplxIndex rlkup, π) 
                                    = fcSrcLookup Map.! (SubSplxIndex $ lkls[])
                                 pathToTrace = traceSubsplxPath rlkup sh
                             in second(const π) 
                                   $ uniqueSubdvdsSel Map.! pathToTrace
        
        fcSrcLookup :: Map SubSplxIndex (SubSplxIndex, SimplexPermutation)
        fcSrcLookup = distinctSubsplxSelect dimension
        
        uniqueSubdvdsSel :: Map
                        SubSimplexSideShare -- The face-subdivision that the desired simplex is a cone over.
                        (Int, SubSimplex v) -- Index of that cone in the resultant subdividers-array, and actual subsimplex implementation.
        uniqueSubdvdsSel = Map.fromList . toList
                            $ V.imap (\i (ssh,ssmr) -> (ssh,(i+1,ssmr))) uniqueSubdvds
        
        uniqueSubdvds :: Array ( SubSimplexSideShare -- The face-part that the associated simplex is a cone over.
                               , SubSimplex v        )
        uniqueSubdvds = V.concat [fFcSdvds, fLdsSdvs, fLdsSdvds]
         where fLdsSdvs  = conesClass buildSDCones ShareSubdivision isLdsPath
               fFcSdvds  = conesClass buildSDDCones ShareSubdivider isFcPath
               fLdsSdvds = conesClass buildSDDCones ShareSubdivider isLdsPath
        
        
        uniqueSSPs :: [([Int], Simplex v)]
        uniqueSSPs = map((id &&& subF) . getSubSplxIndex . fst)
                       $ distinctProperSubsplxGroups dimension
        
        buildSDCones, buildSDDCones
            :: Simplex v
            -- ^ The cones' base simplex /b/, i.e. the simplex the subdivisions of which form the cones' bases.
            -> (SubSimplexSideShare->(Int, Simplex v))
            -- ^ Index of the subdivider that is the cone over this shared-side (relative to /b/), as well as this simplex in constructed form.
            -> (SubSimplexSideShare->SimplexSideShare)
            -- ^ Sideshare-index of a subdivision of /b/, as a side of the simplex containing the built cones.
            -> Array (SubSimplex v)
            -- ^ Cones of the barycenter over /b/'s subdivisions.
            
        buildSDCones (Simplex0 p) _ sfShare
               = singleton $ SubSimplex cnInrs cnvBounds
         where (SimplexN _ cnInrs) = spannedAffineSplx cnBounds vsFun
               (cnBounds, cnvBounds)
                | even dimension
                    = (          [ p                           , barycenter        ]
                      , fromList [ sfShare $ ShareSubdivision 0, barycenterShare   ] )
                | otherwise    
                    = (          [ barycenter        , p                           ]
                      , fromList [ barycenterShare   , sfShare $ ShareSubdivision 0] )
               vsFun = Simplex0 . (cnBounds!!) . head
        buildSDCones b@(SimplexN sSides (SimplexInnards sDivs _)) swLookup sfShare
               = V.imap (buildCone_baseIn b swLookup sfShare . ShareSubdivision) sDivs
--         buildSDCones v@(PermutedSimplex π s)
--          where σ = invPerm π
        -- TODO: buildSDCones b@(PermutedSimplex ...) ...

        buildSDDCones (Simplex0 _) _ _ = V.empty
        buildSDDCones b@(SimplexN sSides (SimplexInnards _ sDivd)) swLookup sfShare
               = V.imap (buildCone_baseIn b swLookup sfShare . ShareSubdivider) sDivd

        buildCone_baseIn :: Simplex v 
                            -- Enclosing base simplex /e/. /b/ is a subdivision or subdivider of this.
                            -> (SubSimplexSideShare->(Int, Simplex v)) -> (SubSimplexSideShare->SimplexSideShare)
                            -- ^ Wall-simplex-lookups, cf. 'buildSDCones'.
                            -> SubSimplexSideShare
                            -- ^ Index of /b/ inside /e/.
                            -> SubSimplex v 
                            -- ^ The base /b/ of the desired cone.
                            -> SubSimplex v
        buildCone_baseIn e swLookup sfShare sdIdx (SimplexBarycenter eb)
                    = SubSimplex cnInrs cnvBounds
         where (SimplexN _ cnInrs) = spannedAffineSplx coneVs vsFun
               coneVs = [barycenter, eb]
               vsFun [0] = Simplex0 barycenter
               vsFun [1] = Simplex0 eb
               cnvBounds = fromList [barycenterShare, sfShare sdIdx]
        buildCone_baseIn e swLookup sfShare sdIdx (SubSimplex cbInrs cbBounds) 
                    = SubSimplex cnInrs cnvBounds
         where (SimplexN _ cnInrs) = spannedAffineSplx coneVs vsFun
               coneVs = barycenter : fSimplexVertices cnBase
               cnBounds = cnBase `V.cons` V.map snd cnMantle
               cnMantle = V.map (\(SimplexSideShare bfs π) 
                                    -> let(i, z) = swLookup bfs
                                       in ((i,π), up1pS π`permuteSimplex`z) )
                                cbBounds
               up1pS SimplexIdPermutation = SimplexIdPermutation
               up1pS π@(SimplexPermutation pa)
                 = SimplexPermutation 
                     $ (0,π) `V.cons` V.map (\(i,σ)->(i+1, up1pS σ)) pa
               cnvBounds = sfShare sdIdx 
                            `V.cons`
                            V.map (uncurry(SimplexSideShare . ShareSubdivider)
                                       . fst)       cnMantle
               cnBase = SimplexN (fmap (findSharedSide e) cbBounds) cbInrs
               vsFun (dsideId:drestId) = locateSubSimplex(SubSplxIndex drestId)
                                              $ cnBounds ! dsideId
--                       sSubdivs = simplicialComplex $ simplexBarycentricSubdivision e
--                       cnvBounds = fromList [ barycenterShare, sfShare prePath ]
        
        barycenterShare :: SimplexSideShare
        barycenterShare = SimplexSideShare (ShareSubdivider 0)
                                           SimplexIdPermutation
        
        barycenter :: v
        barycenter = midBetween $ map simplexBarycenter theFaces
        
        theFaces :: [Simplex v]
        theFaces = [ subF[i] | i <- [0 .. dimension] ]
        
        dimension :: Int
        dimension = length vs - 1
        
        isFcPath, isLdsPath :: [Int] -> Bool
        isFcPath = null . tail
        isLdsPath = not . null . tail
       
              
midBetween :: (VectorSpace v, Fractional(Scalar v)) => [v] -> v
midBetween vs = sumV vs ^/ (fromIntegral $ length vs)
       

thisWholeSimplex = SubSplxIndex[]

type SubSplxPathfinder = SubSplxIndex -> SubSplxIndex

splxPathAriths :: (Int->Int->Int) -> SubSplxPathfinder->SubSplxPathfinder->SubSplxPathfinder
splxPathAriths ifx f1 f2 p
   = SubSplxIndex $ zipWith ifx (getSubSplxIndex $ f1 p) (getSubSplxIndex $ f2 p)

instance Num SubSplxPathfinder where
  fromInteger n (SubSplxIndex p) = SubSplxIndex(fromInteger n : p)
  (+) = splxPathAriths(+)
  (-) = splxPathAriths(+)
  (*) = splxPathAriths(+)
  abs = id
  signum = const $ const thisWholeSimplex
instance Enum SubSplxPathfinder where
  toEnum = fromIntegral
  fromEnum p = head . getSubSplxIndex $ p thisWholeSimplex

pathToSubSmplx :: SubSplxPathfinder->SubSplxIndex
pathToSubSmplx = ($ thisWholeSimplex) 
instance Show SubSplxIndex where
  show(SubSplxIndex p)
   | chainShow@(_:_) <- intercalate"."(map show p) = "pathToSubSmplx("++chainShow++")"
   | otherwise = "thisWholeSimplex"

locateSubSimplex :: SubSplxIndex -> Simplex p -> Simplex p
locateSubSimplex (SubSplxIndex (dir:path)) (SimplexN faces _)
     = locateSubSimplex (SubSplxIndex path) $ faces ! dir
locateSubSimplex idx (PermutedSimplex SimplexIdPermutation s)
     = locateSubSimplex idx s
locateSubSimplex idx (PermutedSimplex π (PermutedSimplex σ s))
     = locateSubSimplex idx $ PermutedSimplex (π↺↺σ) s
locateSubSimplex (SubSplxIndex (dir:path))
                 (PermutedSimplex (SimplexPermutation rm) (SimplexN faces _))
   = let (tgt, π) = rm ! dir
     in  locateSubSimplex (SubSplxIndex path) $ permuteSimplex π (faces ! tgt)
locateSubSimplex _ s = s

type SimplexPermutation' = Array Int

instance Permutation SimplexPermutation' where
  (↺↺) = V.backpermute
  invPerm = fst . undoableSort



asSimplexPermutation :: SimplexPermutation' -> SimplexPermutation
asSimplexPermutation vPerm
  | V.and $ V.imap(==) vPerm  = SimplexIdPermutation
  | otherwise                 = SimplexPermutation $
                      mapElAndRest( \k qerm
                         -> (k, asSimplexPermutation $ V.map (m k) qerm)
                       ) vPerm
     where m k q
            | q<k   = q - k + n - 1
            | q>k   = q - k     - 1
           
           n = V.length vPerm
           
           mapElAndRest :: (a -> Array a -> b) -> Array a -> Array b
           mapElAndRest f arr = V.zipWith f arr gapqs
            where gapqs = V.map fromList . fromList . gapPositions $ toList arr
   


-- | Remove \"gaps\" in an array of unique numbers, i.e. the set of elements
-- is mapped strict-monotonically to @[0 .. length arr - 1]@.
sediment :: Array Int -> Array Int
sediment = V.map fst . saSortBy(compare`on`fst.snd)
             . V.indexed . saSortBy(compare`on`snd) . V.indexed



distinctSubsplxGroups :: Int               -- Dimension of the simplex.
             -> [ ( SubSplxIndex           -- Index of the \"one necessary\" simplex in one group of equivalent subsimplices.
                  , [ ( SubSplxIndex       -- Other indices that actually refer to the same single subsimplex.
                      , SimplexPermutation -- Permutation of that simplex that need to be performed.
                      )])]
distinctSubsplxGroups = (sel!!)
 where sel = [ groupEquivs $ findAll [0 .. n] | n<-[0..] ]
       
       findAll :: [Int] -> [ (SubSplxIndex, [Int]) ]
       findAll [] = []
       findAll sid = (thisWholeSimplex, sid)
                       : (deeper =<< zip[0..] (gapPositions sid))
        where deeper(wy, newSpl) = map (first wy) $ findAll newSpl
              
       groupEquivs :: [ (SubSplxIndex, [Int]) ]
                      -> [(SubSplxIndex, [(SubSplxIndex,SimplexPermutation)])]
       groupEquivs = {-sortBy (compare`on`fst)
                      .-} map (\(_, eqvs@((dpath,dperm):_))
                           -> ( dpath
                              , map (\(path,perm)
                                   -> ( path, asSimplexPermutation $ dperm↺↻perm )
                                 ) eqvs
                              ) )
                      . fastNubByWith ( compare `on` fst )
                                      ( \(c1,l1)(_,l2) -> (c1,l1++l2) )
                      . map(\(path, cfg) -> let(unSort,sorted)=undoableSort $ fromList cfg
                                            in (toList sorted, [(path, unSort)])           )

distinctProperSubsplxGroups :: Int -> [(SubSplxIndex, [(SubSplxIndex,SimplexPermutation)])]
distinctProperSubsplxGroups = (sel!!)
 where sel = [ filter((/=thisWholeSimplex) . fst) $ distinctSubsplxGroups n | n<-[0.. ] ]

distinctDim0SubsplxGroups :: Int -> [(SubSplxIndex, [(SubSplxIndex,SimplexPermutation)])]
distinctDim0SubsplxGroups = (sel!!)
 where sel = [ filter((==n) . length . getSubSplxIndex . fst) 
                      $ distinctSubsplxGroups n 
             | n<-[0.. ] ]

distinctSubsplxSelect :: Int -> Map SubSplxIndex (SubSplxIndex, SimplexPermutation)
distinctSubsplxSelect = (sel!!)
 where sel = [ constructMap $ distinctSubsplxGroups n | n<-[0.. ] ]
       constructMap = foldr ins Map.empty
        where ins (ref, slaves) prev = foldr (\(idx,π) -> Map.insert idx (ref,π)) prev slaves

undoableSort :: Ord a => Array a -> (SimplexPermutation', Array a)
undoableSort = V.unzip . saSortBy(compare`on`snd) . V.indexed


data ManifoldFromTriangltn a tSpc = ManifoldFromTriangltn
         { manifoldTriangulation :: Triangulation a
         , triangltnFocus :: [Int]                  }





 


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

saSort :: Ord a => Array a -> Array a
saSort = V.modify VAIns.sort

-- The sorting algorithm of choice is simple insertion sort, because simplices
-- that can feasibly be handled will always have low dimension, so the better
-- complexity of more sophisticated sorting algorithms is no use on the short
-- vertex arrays.
{-# inline saSortBy #-}
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
