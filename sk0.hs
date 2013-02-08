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

import Control.Monad
import Control.Monad.Trans.Maybe

type VSpace v = (InnerSpace v, EqFloating(Scalar v))

-- | A chart is a homeomorphism from a connected, open subset /Q/ ⊂ /M/ of
-- an /n/-manifold /M/ to either the open unit disk /Dⁿ/ ⊂ /V/ ≃ ℝ/ⁿ/, or
-- the half-disk /Hⁿ/ = {/x/ ∊ /Dⁿ/: x₀≥0}. In e.g. the former case, 'chartInMap'
-- is thus defined ∀ /v/ ∊ /V/ : |/v/| < 1, while 'chartOutMap p' will yield @Just x@
-- with /x/ ∊ /Dⁿ/ provided /p/ is in /Q/, and @Nothing@ otherwise.
-- Obviously, @fromJust . 'chartOutMap' . 'chartInMap'@ should be equivalent to @id@
-- on /Dⁿ/, and @'chartInMap' . fromJust . 'chartOutMap'@ to @id@ on /Q/.
data Chart manifold tangentspace where
  Chart :: VSpace v =>
        { chartInMap :: v -> m
        , chartOutMap :: m -> Maybe v
        , chartKind :: ChartKind      } -> Chart m v
data ChartKind = LandlockedChart  -- ^ A /M/ ⇆ /Dⁿ/ chart, for ordinary manifolds
               | RimChart         -- ^ A /M/ ⇆ /Hⁿ/ chart, for manifolds with a rim

isInUpperHemi :: VSpace v => v -> Bool
isInUpperHemi v = (snd . head) (decompose v) >= 0

rimGuard :: VSpace v => ChartKind -> v -> Maybe v
rimGuard LandlockedChart v = Just v
rimGuard RimChart v
 | isInUpperHemi v = Just v
 | otherwise       = Nothing

chartEnv :: Manifold m => Chart m (TangentSpace m)
               -> (TangentSpace m->TangentSpace m)
               -> m -> Maybe m
chartEnv (Chart inMap outMap chKind) f 
   = fmap inMap . (>>=rimGuard chKind) . fmap f . outMap

chartEnv' :: (Manifold m, Monad f) => Chart m (TangentSpace m)
               -> (TangentSpace m->f(TangentSpace m))
               -> m -> MaybeT f m
chartEnv' (Chart inMap outMap chKind) f x
  = MaybeT $ case outMap x of
              Just w -> liftM (fmap inMap . rimGuard chKind) $ f w
              Nothing -> return Nothing
   

 

type Atlas m v = [Chart m v]

type EqFloating f = (Eq f, Floating f)

class (HasBasis(TangentSpace m), EqFloating(Scalar(TangentSpace m)))
         => Manifold m where
  type TangentSpace m :: *
  
  triangulation :: m -> Triangulation m
  triangulation = autoTriangulation
  
  localAtlas :: m -> Atlas m (TangentSpace m)




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


class (Functor s) => Simplex s where
  type LowerDim s p :: *
  lowerDimSimplices :: s p -> [LowerDim s p]
  simplexVertices :: FastNub p => s p -> [p]
  barycentricSubdiv :: s p -> Triangulation p

newtype Simplex0 p = Simplex0 p deriving (Eq)
data SimplexN lowerDim p
   = SimplexN { simplexNLDBounds :: [lowerDim p]
              , simplexNBarycentricSD :: Triangulation p
              } 
--               deriving(Eq)

instance Functor Simplex0 where {fmap f(Simplex0 p) = Simplex0(f p)}

instance (Simplex ld) => Functor (SimplexN ld) where
  fmap f(SimplexN lds subdiv) = SimplexN (map(fmap f) lds) (fmap f subdiv)

instance Simplex Simplex0 where
  type LowerDim Simplex0 p = ()
  lowerDimSimplices _ = []
  simplexVertices (Simplex0 point) = [point]
  barycentricSubdiv p = triangPoint
   where triangPoint = Triangulation [p] triangPoint

instance (Simplex lowerDim) => Simplex (SimplexN lowerDim) where
  type LowerDim (SimplexN lowerDim) p = lowerDim p
  lowerDimSimplices (SimplexN lds _) = lds
  simplexVertices (SimplexN lds _) = fastNub $ lds>>=simplexVertices
  barycentricSubdiv (SimplexN _ sd) = sd

data Triangulation p where
  Triangulation :: Simplex s => 
    { simplicialComplex :: [s p]
    , barycentricSubdivision :: Triangulation p } -> Triangulation p
    
-- deriving instance Eq (Triangulation p)

instance Functor Triangulation where
  fmap f(Triangulation c bcs) = Triangulation(map(fmap f)c) (fmap f bcs)


data IndexedVert p = IndexedVert {indexedVertex::p, vertexIndex::Int}
instance Eq (IndexedVert p) where {(==) = (==)`on`vertexIndex}
instance Ord (IndexedVert p) where {compare = compare`on`vertexIndex}

autoTriangulation :: forall m . Manifold m => m -> Triangulation m
autoTriangulation m = undefined -- Triangulation
 where 
       basisChart = head $ localAtlas m
       
       expandablyRim :: Chart m (TangentSpace m) -> [m] -> [m]
       expandablyRim (Chart inMap outMap chKind) = 
       
       basisSimplexVerts :: [m]
       basisSimplexVerts = liftM fromJust . runMaybeT $ chartEnv' basisChart spread m
       
       spread :: TangentSpace m -> [TangentSpace m]
       spread v = map recompose $
                   zeroP : map dimSingP decomp'
        where zeroP = map (\(b, _) -> (b,0)) decomp
              dimSingP(n,_) = map z decomp'
               where z(n',(b,q))
                      | n'/=n          = (b,0)
                      | q'<-signum q
                      , q'/=0          = (b, q'*0.9)
                      | otherwise      = (b, 0.9)
              decomp = decompose v
              decomp' = zip [0..] decomp
              
              
              
 
mapOnNth :: (a->a) -> Int -> [a] -> [a]
mapOnNth f 0 (l:ls) = f l : ls
mapOnNth f n (l:ls) = l : mapOnNth f (n-1) ls
mapOnNth _ _ [] = []