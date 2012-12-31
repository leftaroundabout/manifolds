{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE ConstraintKinds          #-}

import Data.List
import Data.Function

import Data.VectorSpace
import Data.Basis

import Control.Monad

-- | A chart is a homeomorphism from a connected, open subset /Q/ ⊂ /M/ of
-- an /n/-manifold /M/ to either the open unit disk /Dⁿ/ ⊂ /V/ ≃ ℝ/ⁿ/, or
-- the half-disk /Hⁿ/ = {/x/ ∊ /Dⁿ/: x₀≥0}. In e.g. the former case, 'chartInMap'
-- is thus defined ∀ /v/ ∊ /V/ : |/v/| < 1, while 'chartOutMap p' will yield @Just x@
-- with /x/ ∊ /Dⁿ/ provided /p/ is in /Q/, and @Nothing@ otherwise.
-- Obviously, @fromJust . 'chartOutMap' . 'chartInMap'@ should be equivalent to @id@
-- on /Dⁿ/, and @'chartInMap' . fromJust . 'chartOutMap'@ to @id@ on /Q/.
data Chart manifold tangentspace where
  Chart :: InnerSpace v =>
        { chartInMap :: v -> m
        , chartOutMap :: m -> Maybe v
        , chartKind :: ChartKind      } -> Chart m v
data ChartKind = LandlockedChart  -- ^ A /M/ ⇆ /Dⁿ/ chart, for ordinary manifolds
               | RimChart         -- ^ A /M/ ⇆ /Hⁿ/ chart, for manifolds with a rim

type Atlas m v = [Chart m v]


class (HasBasis(TangentSpace m)) => Manifold m where
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
   | ϑ==0       = [ Chart (\(ϑ'ᵥ,φ'ᵥ) -> S2(ϑ'ᵥ*pi) (φ'ᵥ*2*pi) )
                          (\(S2 ϑ' φ') -> guard (ϑ'<pi) >> Just (ϑ'/pi, φ'/(2*pi)) )
                          LandlockedChart ]
   | ϑ==2*pi    = [ Chart (\(ϑ'ᵥ,φ'ᵥ) -> S2 ((1-ϑ'ᵥ)*pi) (φ'ᵥ*2*pi) )
                          (\(S2 ϑ' φ') -> guard (ϑ'>0) >> Just (1-ϑ'/pi, φ'/(2*pi)) )
                          LandlockedChart ]
   | otherwise  = localAtlas(S2 0 φ) ++ localAtlas(S2 (2*pi) φ)




-- data IsolenNil a = I
-- data IsolenCons l a = a :\ l

-- data Simplex lowerDim p = [(a, Triangulation a)]
type FastNub a = (Eq a, Ord a)

class (Functor s) => Simplex s where
  type LowerDim s p :: *
  lowerDimSimplices :: s p -> [LowerDim s p]
  simplexVertices :: FastNub p => s p -> [p]
  barycentricSubdiv :: s p -> Triangulation p

newtype Simplex0 p = Simplex0 p deriving (Eq)
data SimplexN lowerDim p
   = SimplexN { simplexNLDBounds :: [lowerDim p]
              , simplexNbarycentricSD :: Triangulation p
              } deriving(Eq)

instance Functor Simplex0 where {fmap f(Simplex0 p) = Simplex0(f p)}

instance (Simplex ld) => Functor (SimplexN ld) where
  fmap f(SimplexN lds) = SimplexN $ map(fmap f) lds

instance Simplex Simplex0 where
  type LowerDim Simplex0 p = ()
  lowerDimSimplices _ = []
  simplexVertices (Simplex0 point) = [point]
  barycentricSubdiv p = triangPoint
   where triangPoint = Triangulation [p] triangPoint

instance (Simplex lowerDim) => Simplex (SimplexN lowerDim) where
  type LowerDim (SimplexN lowerDim) p = lowerDim p
  lowerDimSimplices (SimplexN lds _) = lds
  simplexVertices (SimplexN lds _) = map head . group . sort $ lds>>=simplexVertices
  barycentricSubdiv (SimplexN _ sd) = sd

data Triangulation p where
  Triangulation :: Simplex s => 
    { simplicialComplex :: [s p]
    , barycentricSubdivision :: Triangulation p } -> Triangulation p

instance Functor Triangulation where
  fmap f(Triangulation c bcs) = Triangulation(map(fmap f)c) (fmap f bcs)


data IndexedVert p = IndexedVert {indexedVertex::p, vertexIndex::Int}
instance Eq (IndexedVert p) where {(==) = (==)`on`vertexIndex}
instance Ord (IndexedVert p) where {compare = compare`on`vertexIndex}

autoTriangulation :: Manifold m => m -> Triangulation m
autoTriangulation m = undefined -- Triangulation