{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE ConstraintKinds          #-}
{-# LANGUAGE StandaloneDeriving       #-}
{-# LANGUAGE ScopedTypeVariables      #-}

import Data.List
import Data.Maybe
import Data.Function

import Data.VectorSpace
import Data.Basis

import Control.Arrow
import Control.Monad
import Control.Monad.Trans.Maybe


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
  
  triangulation :: m -> Triangulation m
--   triangulation = autoTriangulation
  
  localAtlas :: m -> Atlas m




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




type FastNub a = (Eq a, Ord a) -- Should really be (Eq a, Hashable a)
fastNub :: FastNub a => [a] -> [a]
fastNub = map head . group . sort




data Simplex p
   = Simplex0 p
   | SimplexN { simplexNLDBounds :: [Simplex p]
              , simplexNBarycentricSD :: Triangulation p
              } 

instance (Show p) => Show (Simplex p) where
  show (Simplex0 p) = "Simplex0(" ++ show p ++ ")"
  show (SimplexN sss _) = "SimplexN " ++ show sss ++ " undefined"

simplexVertices :: Eq p => Simplex p -> [p]
simplexVertices (Simplex0 p) = [p]
simplexVertices (SimplexN vs _) = nub $ simplexVertices =<< vs 

simplexDimension :: Simplex p -> Int
simplexDimension (Simplex0 _) = 0
simplexDimension (SimplexN (face:_) _) = simplexDimension face + 1

--               deriving(Eq)

instance Functor Simplex where
  fmap f(Simplex0 p) = Simplex0(f p)
  fmap f(SimplexN lds subdiv) = SimplexN (map(fmap f) lds) (fmap f subdiv)

newtype Triangulation p
  = Triangulation
    { simplicialComplex      :: [Simplex p]
--     , barycentricSubdivision :: Triangulation p 
    }       --  -> Triangulation p
  deriving (Show)


triangulationVertices :: Eq p => Triangulation p -> [p]
triangulationVertices (Triangulation sComplex) = nub $ simplexVertices =<< sComplex
    
-- deriving instance Eq (Triangulation p)

-- This is not particularly efficient at the moment: 'fmap' obviously
-- works on vertices in the end, but every vertex is an edge of multiple
-- simplices, which is not specially taken account for, i.e. the function
-- will be called multiple times on each vertex.
-- It might be a good idea to refactor 'Triangulation' to use a \"vertex pool\"
-- and only have the simplices /refer/ to the vertices therein. Alternatively,
-- 'fmap' could first trim out duplicates (would require a 'FastNub' GADT
-- constraint) and re-map them; that would make 'fmap' rather expensive
-- by itself, but as with stream fusion rewrite rules of the functor laws
-- the mapped function should typically become few and reasonably complex
-- this should not be much of a problem.
instance Functor Triangulation where
  fmap f(Triangulation c) = Triangulation(map(fmap f)c)


data IndexedVert p = IndexedVert {indexedVertex::p, vertexIndex::Int}
instance Eq (IndexedVert p) where {(==) = (==)`on`vertexIndex}
instance Ord (IndexedVert p) where {compare = compare`on`vertexIndex}

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
r `ballAround`p = fmap ((^+^p) . l₁tol₂) $ Triangulation orthoplex
 where orthoplex
        | [] <- vDecomp  = [Simplex0 p]
        | otherwise      = orthSides
         
       vDecomp = decompose p
       vBasis = map fst vDecomp
       n = length $ vDecomp
       
       orthSides = map (affineSimplex . (p:)) orthVertices
       
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

affineSimplex :: EuclidSpace v => [v] -> Simplex v
affineSimplex [v] = Simplex0 v
affineSimplex vs  = result
 where sides      = map affineSimplex . orientate $ omit1s vs
       result = SimplexN sides subdivided
       subdivided = Triangulation . map snd . snd $ subdivide result
       
       subdivide (Simplex0 v)    = (v, [([v],Simplex0 v)])
       subdivide (SimplexN vs _) = orq $ map subdivide vs
        where
              orq ps = ( b, map((\vs -> (vs, affineSimplex vs)) . (b:) )
                             . orientate . concat $ map (map fst . snd) ps )
               where b = midBetween $ map fst ps
               
              midBetween :: EuclidSpace v => [v] -> v
              midBetween vs = sumV vs ^/ (fromIntegral $ length vs)
       
       orientate = zipWith($) $ cycle [reverse, id]


data ManifoldFromTriangltn a tSpc = ManifoldFromTriangltn
         { manifoldTriangulation :: Triangulation a
         , triangltnFocus :: [Int]                  }


              
edgeSimplex2subdiv =              
 Triangulation {simplicialComplex = [ SimplexN [ SimplexN [ Simplex0(Space2D 3.0 0.0), Simplex0(Space2D 1.5 1.5)] undefined
                                               , SimplexN [ Simplex0(Space2D 1.5 1.5), Simplex0(Space2D 1.0 1.0)] undefined
                                               , SimplexN [ Simplex0(Space2D 1.0 1.0), Simplex0(Space2D 3.0 0.0)] undefined ] undefined
                                    , SimplexN [ SimplexN [ Simplex0(Space2D 1.5 1.5), Simplex0(Space2D 0.0 3.0)] undefined
                                               , SimplexN [ Simplex0(Space2D 0.0 3.0), Simplex0(Space2D 1.0 1.0)] undefined
                                               , SimplexN [ Simplex0(Space2D 1.0 1.0), Simplex0(Space2D 1.5 1.5)] undefined ] undefined
                                    , SimplexN [ SimplexN [ Simplex0(Space2D 0.0 3.0), Simplex0(Space2D 0.0 1.5)] undefined
                                               , SimplexN [ Simplex0(Space2D 0.0 1.5), Simplex0(Space2D 1.0 1.0)] undefined
                                               , SimplexN [ Simplex0(Space2D 1.0 1.0), Simplex0(Space2D 0.0 3.0)] undefined ] undefined
                                    , SimplexN [ SimplexN [ Simplex0(Space2D 0.0 1.5), Simplex0(Space2D 0.0 0.0)] undefined
                                               , SimplexN [ Simplex0(Space2D 0.0 0.0), Simplex0(Space2D 1.0 1.0)] undefined
                                               , SimplexN [ Simplex0(Space2D 1.0 1.0), Simplex0(Space2D 0.0 1.5)] undefined ] undefined
                                    , SimplexN [ SimplexN [ Simplex0(Space2D 0.0 0.0), Simplex0(Space2D 1.5 0.0)] undefined
                                               , SimplexN [ Simplex0(Space2D 1.5 0.0), Simplex0(Space2D 1.0 1.0)] undefined
                                               , SimplexN [ Simplex0(Space2D 1.0 1.0), Simplex0(Space2D 0.0 0.0)] undefined ] undefined
                                    , SimplexN [ SimplexN [ Simplex0(Space2D 1.5 0.0), Simplex0(Space2D 3.0 0.0)] undefined
                                               , SimplexN [ Simplex0(Space2D 3.0 0.0), Simplex0(Space2D 1.0 1.0)] undefined
                                               , SimplexN [ Simplex0(Space2D 1.0 1.0), Simplex0(Space2D 1.5 0.0)] undefined ] undefined ]}
edgeSimplex3 =
 SimplexN [ SimplexN [ SimplexN [ Simplex0(Space3D 0.0 3.0 0.0), Simplex0(Space3D 3.0 0.0 0.0)] undefined
                     , SimplexN [ Simplex0(Space3D 3.0 0.0 0.0), Simplex0(Space3D 0.0 0.0 3.0)] undefined
                     , SimplexN [ Simplex0(Space3D 0.0 0.0 3.0), Simplex0(Space3D 0.0 3.0 0.0)] undefined ] undefined
          , SimplexN [ SimplexN [ Simplex0(Space3D 0.0 3.0 0.0), Simplex0(Space3D 0.0 0.0 3.0)] undefined
                     , SimplexN [ Simplex0(Space3D 0.0 0.0 3.0), Simplex0(Space3D 0.0 0.0 0.0)] undefined
                     , SimplexN [ Simplex0(Space3D 0.0 0.0 0.0), Simplex0(Space3D 0.0 3.0 0.0)] undefined ] undefined
          , SimplexN [ SimplexN [ Simplex0(Space3D 3.0 0.0 0.0), Simplex0(Space3D 0.0 0.0 0.0)] undefined
                     , SimplexN [ Simplex0(Space3D 0.0 0.0 0.0), Simplex0(Space3D 0.0 0.0 3.0)] undefined
                     , SimplexN [ Simplex0(Space3D 0.0 0.0 3.0), Simplex0(Space3D 3.0 0.0 0.0)] undefined ] undefined
          , SimplexN [ SimplexN [ Simplex0(Space3D 3.0 0.0 0.0), Simplex0(Space3D 0.0 3.0 0.0)] undefined
                     , SimplexN [ Simplex0(Space3D 0.0 3.0 0.0), Simplex0(Space3D 0.0 0.0 0.0)] undefined
                     , SimplexN [ Simplex0(Space3D 0.0 0.0 0.0), Simplex0(Space3D 3.0 0.0 0.0)] undefined ] undefined ] undefined
 



omit1s :: [a] -> [[a]]
omit1s [] = []
omit1s [_] = [[]]
omit1s (v:vs) = vs : map(v:) (omit1s vs)
 
mapOnNth :: (a->a) -> Int -> [a] -> [a]
mapOnNth f 0 (l:ls) = f l : ls
mapOnNth f n (l:ls) = l : mapOnNth f (n-1) ls
mapOnNth _ _   []   = []

mapExceptOnNth :: (a->a) -> Int -> [a] -> [a]
mapExceptOnNth f 0 (l:ls) = l : map f ls
mapExceptOnNth f n (l:ls) = f l : mapOnNth f (n-1) ls
mapExceptOnNth _ _   []   = []

coordMap :: HasBasis v => ([Scalar v] -> [Scalar v]) -> v -> v
coordMap f = recompose .  dcmap . decompose
 where dcmap dc = let b=map fst dc
                      c=map snd dc
                  in zip b $ f c

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
