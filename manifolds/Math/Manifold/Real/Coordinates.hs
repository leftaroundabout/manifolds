-- |
-- Module      : Math.Manifold.Real.Coordinates
-- Copyright   : (c) Justus Sagemüller 2018
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsagemue $ uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 

{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE Rank2Types             #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE UnicodeSyntax          #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE EmptyCase              #-}
{-# LANGUAGE StandaloneDeriving     #-}
{-# LANGUAGE CPP                    #-}
{-# LANGUAGE ScopedTypeVariables    #-}



module Math.Manifold.Real.Coordinates
         ( Coordinate, coordinate
         , HasCoordinates(..)
         -- * Vector space axes
         , HasXCoord(..), HasYCoord(..), HasZCoord(..)
         -- * Tangent space diffs
         , CoordDifferential(..)
         -- * Spherical coordinates
         , HasAzimuth(..)
         , HasZenithDistance(..)
         ) where


import Data.Manifold.Types.Primitive
import Data.Manifold.Types.Stiefel
import Data.Manifold.PseudoAffine
import Math.LinearMap.Category
import Data.VectorSpace

import Control.Lens hiding ((<.>))
import Data.List (intercalate, transpose)

import qualified Linear as Lin

import qualified Test.QuickCheck as QC
import qualified Test.QuickCheck.Gen as QC (unGen)
import qualified Test.QuickCheck.Random as QC (mkQCGen)
import Data.Maybe (fromJust, isJust)

import Numeric.IEEE (epsilon)

-- | To give a custom type coordinate axes, first define an instance of this class.
class HasCoordinates m where
  -- | A unique description of a coordinate axis.
  data CoordinateIdentifier m :: *
  -- | How to use a coordinate axis for points in the containing space.
  --   This is what 'coordinate' calls under the hood.
  coordinateAsLens :: CoordinateIdentifier m -> Lens' m ℝ
  -- | Delimiters for the possible values one may choose for a given coordinate,
  --   around a point on the manifold.
  --   For example, in spherical coordinates, the 'azimuth' generally has a range
  --   of @(-'pi', 'pi')@, except at the poles where it's @(0,0)@.
  validCoordinateRange :: CoordinateIdentifier m -> m -> (ℝ,ℝ)
  validCoordinateRange _ _ = (-1/0, 1/0)

class CoordinateIsh q m | q -> m where
  useCoordinate :: CoordinateIdentifier m -> q

instance CoordinateIsh (CoordinateIdentifier m) m where
  useCoordinate = id
instance (Functor f, HasCoordinates m, a ~ (ℝ -> f ℝ), b ~ (m -> f m))
          => CoordinateIsh (a -> b) m where
  useCoordinate = coordinateAsLens

coordinate :: CoordinateIdentifier m -> Coordinate m
coordinate = useCoordinate

-- | A coordinate is a function that can be used both to determine the position
-- of a point on a manifold along the one of some family of (possibly curved) axes on
-- which it lies, and for moving the point along that axis.
-- Basically, this is a 'Lens' and can indeed be used with the '^.', '.~' and '%~'
-- operators.
-- 
-- @
-- 'Coordinate' m ~ 'Lens'' m 'ℝ'
-- @
-- 
-- In addition, each type may also have a way of identifying particular coordinate
-- axes. This is done with 'CoordinateIdentifier', which is what should be used
-- for /defining/ given coordinate axes.
type Coordinate m = ∀ q . CoordinateIsh q m => q

instance HasCoordinates ℝ⁰ where
  data CoordinateIdentifier ℝ⁰
  coordinateAsLens b = case b of {}

instance HasCoordinates ℝ where
  data CoordinateIdentifier ℝ = RealCoord { realAxisTfmStretch :: !ℝ }
                      deriving (Eq,Show)
  coordinateAsLens (RealCoord μ) = iso (/μ) (*μ)
  {-# INLINE coordinateAsLens #-}

instance QC.Arbitrary (CoordinateIdentifier ℝ) where
  arbitrary = RealCoord . QC.getNonZero <$> QC.arbitrary
  shrink (RealCoord μ) = [ RealCoord ν | ν <- QC.shrink μ, ν/=0 ]

data OriginAxisCoord v = OriginAxisCoord
       { coordHeading :: !v             -- ^ Must be conjugate to heading, i.e.
       , coordSensor :: !(DualVector v) -- ^ @'coordSensor' <.>^ 'coordHeading' = 1@.
       }
deriving instance (Show v, Show (DualVector v)) => Show (OriginAxisCoord v)
deriving instance (Eq v, Eq (DualVector v)) => Eq (OriginAxisCoord v)

originAxisCoordAsLens :: LinearSpace v => OriginAxisCoord v -> Lens' v (Scalar v)
originAxisCoordAsLens (OriginAxisCoord v dv)
     = lens (dv<.>^)
            (\w c' -> w ^+^ (c' - dv<.>^w)*^v)
{-# INLINE originAxisCoordAsLens #-}

instance (QC.Arbitrary v, InnerSpace v, v ~ DualVector v, Scalar v ~ ℝ)
    => QC.Arbitrary (OriginAxisCoord v) where
  arbitrary = QC.arbitrary `suchThatMap` \v
   -> case magnitudeSq v of
       0 -> Nothing
       v² -> Just $ OriginAxisCoord v (v^/v²)
  shrink (OriginAxisCoord v _) = [ OriginAxisCoord w (w^/w²)
                                 | w <- QC.shrink v
                                 , let w² = magnitudeSq w
                                 , w² > 0 ]

instance HasCoordinates ℝ² where
  data CoordinateIdentifier ℝ² = ℝ²Coord !(OriginAxisCoord ℝ²) deriving (Eq,Show)
  coordinateAsLens (ℝ²Coord b) = originAxisCoordAsLens b
  {-# INLINE coordinateAsLens #-}

instance QC.Arbitrary ℝ² => QC.Arbitrary (CoordinateIdentifier ℝ²) where
  arbitrary = ℝ²Coord <$> QC.arbitrary
  shrink (ℝ²Coord q) = ℝ²Coord <$> QC.shrink q

instance HasCoordinates ℝ³ where
  data CoordinateIdentifier ℝ³ = ℝ³Coord !(OriginAxisCoord ℝ³) deriving (Eq,Show)
  coordinateAsLens (ℝ³Coord b) = originAxisCoordAsLens b
  {-# INLINE coordinateAsLens #-}

instance QC.Arbitrary ℝ³ => QC.Arbitrary (CoordinateIdentifier ℝ³) where
  arbitrary = ℝ³Coord <$> QC.arbitrary
  shrink (ℝ³Coord q) = ℝ³Coord <$> QC.shrink q

instance (HasCoordinates a, HasCoordinates b) => HasCoordinates (a,b) where
  data CoordinateIdentifier (a,b) = LSubspaceCoord (CoordinateIdentifier a)
                                  | RSubspaceCoord (CoordinateIdentifier b)
  coordinateAsLens (LSubspaceCoord ca) = _1 . coordinateAsLens ca
  coordinateAsLens (RSubspaceCoord cb) = _2 . coordinateAsLens cb
  {-# INLINE coordinateAsLens #-}

deriving instance (Eq (CoordinateIdentifier a), Eq (CoordinateIdentifier b))
            => Eq (CoordinateIdentifier (a,b))
deriving instance (Show (CoordinateIdentifier a), Show (CoordinateIdentifier b))
            => Show (CoordinateIdentifier (a,b))

instance (QC.Arbitrary (CoordinateIdentifier a), QC.Arbitrary (CoordinateIdentifier b))
    => QC.Arbitrary (CoordinateIdentifier (a,b)) where
  arbitrary = QC.oneof [LSubspaceCoord<$>QC.arbitrary, RSubspaceCoord<$>QC.arbitrary]
  shrink (LSubspaceCoord ba) = LSubspaceCoord <$> QC.shrink ba
  shrink (RSubspaceCoord bb) = RSubspaceCoord <$> QC.shrink bb

class HasCoordinates m => HasXCoord m where
  xCoord :: Coordinate m

instance HasXCoord ℝ where
  xCoord = coordinate (RealCoord 1)
  {-# INLINE xCoord #-}
instance HasXCoord ℝ² where
  xCoord = coordinate (ℝ²Coord $ OriginAxisCoord (Lin.V2 1 0) (Lin.V2 1 0))
  {-# INLINE xCoord #-}
instance HasXCoord ℝ³ where
  xCoord = coordinate (ℝ³Coord $ OriginAxisCoord (Lin.V3 1 0 0) (Lin.V3 1 0 0))
  {-# INLINE xCoord #-}
instance (HasXCoord v, HasCoordinates w) => HasXCoord (v,w) where
  xCoord = coordinate $ LSubspaceCoord xCoord

class HasYCoord m where
  yCoord :: Coordinate m

instance HasYCoord ℝ² where
  yCoord = coordinate (ℝ²Coord $ OriginAxisCoord (Lin.V2 0 1) (Lin.V2 0 1))
  {-# INLINE yCoord #-}
instance HasYCoord ℝ³ where
  yCoord = coordinate (ℝ³Coord $ OriginAxisCoord (Lin.V3 0 1 0) (Lin.V3 0 1 0))
  {-# INLINE yCoord #-}
instance HasCoordinates w => HasYCoord ((ℝ,ℝ),w) where
  yCoord = coordinate $ LSubspaceCoord yCoord
instance (HasXCoord w) => HasYCoord (ℝ,w) where
  yCoord = coordinate $ RSubspaceCoord xCoord

class HasZCoord m where
  zCoord :: Coordinate m

instance HasZCoord ℝ³ where
  zCoord = coordinate (ℝ³Coord $ OriginAxisCoord (Lin.V3 0 0 1) (Lin.V3 0 0 1))
  {-# INLINE zCoord #-}
instance HasXCoord w => HasZCoord ((ℝ,ℝ),w) where
  zCoord = coordinate $ RSubspaceCoord xCoord
instance (HasYCoord w) => HasZCoord (ℝ,w) where
  zCoord = coordinate $ RSubspaceCoord yCoord

instance (HasCoordinates (Interior b), HasCoordinates f)
              => HasCoordinates (FibreBundle b f) where
  data CoordinateIdentifier (FibreBundle b f)
           = BaseSpaceCoordinate (CoordinateIdentifier (Interior b))
           | FibreSpaceCoordinate (Interior b -> CoordinateIdentifier f)
  coordinateAsLens (BaseSpaceCoordinate b)
            = lens (\(FibreBundle p _) -> p)
                   (\(FibreBundle _ f) p -> FibreBundle p f)
                . coordinateAsLens b
  coordinateAsLens (FibreSpaceCoordinate b)
            = \φ pf@(FibreBundle p f) -> case coordinateAsLens $ b p of
                 fLens -> FibreBundle p <$> fLens φ f
  validCoordinateRange (BaseSpaceCoordinate b) (FibreBundle p _) = validCoordinateRange b p
  validCoordinateRange (FibreSpaceCoordinate bf) (FibreBundle p f)
                          = validCoordinateRange (bf p) f
  
instance ∀ b f . ( Show (CoordinateIdentifier (Interior b))
                 , Show (CoordinateIdentifier f)
                 , Eq (Interior b), Eq (CoordinateIdentifier f)
                 , QC.Arbitrary (Interior b), Show (Interior b) )
    => Show (CoordinateIdentifier (FibreBundle b f)) where
  showsPrec p (BaseSpaceCoordinate b)
      = showParen (p>9) $ ("BaseSpaceCoordinate "++) . showsPrec 10 b
  showsPrec p (FibreSpaceCoordinate bf)
      = showParen (p>0) $ \cont ->
          "BaseSpaceCoordinate $ \\case {"
          ++ intercalate "; " [ showsPrec 5 p . (" -> "++) . shows (bf p) $ ""
                              | p <- exampleArgs ]
          ++ "... }" ++ cont
   where exampleArgs :: [Interior b]
         exampleArgs = head $ go 1 0 2384148716156
          where go :: Int -> Int -> Int -> [[Interior b]]
                go n tries seed
                  | length candidate == n, allDifferent candidate
                  , (shrunk:_) <- filter (allDifferent . map bf)
                                     $ shrinkElems candidate ++ [candidate]
                  , [] <- take (5-n) $ go (n+1) 0 seed'
                                      = [shrunk]
                  | tries*(n-1) > 15  = []
                  | otherwise         = go n (tries+1) seed'
                 where candidate = take n $ generateFrom seed QC.arbitrary
                       seed' = generateFrom seed QC.arbitrary
         allDifferent (x:ys) = all (x/=) ys && allDifferent ys
         allDifferent [] = True

generateFrom :: QC.CoArbitrary s => s -> QC.Gen a -> a
generateFrom seed val = QC.unGen (QC.coarbitrary seed val) (QC.mkQCGen 256592) 110818

-- | Keep length of the list, but shrink the individual elements.
shrinkElems :: QC.Arbitrary a => [a] -> [[a]]
shrinkElems l = filter ((==length l) . length) . transpose $ map QC.shrink l


class HasCoordinates m => CoordDifferential m where
  -- | Observe local, small variations (in the tangent space) of a coordinate.
  delta :: CoordinateIdentifier m -> Coordinate (TangentBundle m)

instance ( CoordDifferential m, f ~ Needle m, m ~ Interior m
         , QC.Arbitrary m
         , QC.Arbitrary (CoordinateIdentifier m)
         , QC.Arbitrary (CoordinateIdentifier f) )
             => QC.Arbitrary (CoordinateIdentifier (FibreBundle m f)) where
  arbitrary = QC.oneof [ BaseSpaceCoordinate <$> QC.arbitrary
                       , delta <$> QC.arbitrary ]
  shrink (BaseSpaceCoordinate b) = BaseSpaceCoordinate <$> QC.shrink b
  shrink (FibreSpaceCoordinate bf) = FibreSpaceCoordinate . const
                     <$> QC.shrink (bf cRef)
   where cRef₀ = QC.unGen QC.arbitrary (QC.mkQCGen 534373) 57314
         cRef = head $ QC.shrink cRef₀ ++ [cRef₀]

instance CoordDifferential ℝ where
  delta ζ = coordinate . FibreSpaceCoordinate $ const ζ
instance CoordDifferential ℝ² where
  delta ζ = coordinate . FibreSpaceCoordinate $ const ζ
instance CoordDifferential ℝ³ where
  delta ζ = coordinate . FibreSpaceCoordinate $ const ζ

instance (CoordDifferential a, CoordDifferential b) => CoordDifferential (a,b) where
  delta (LSubspaceCoord ba) = coordinate $ case delta ba of
     FibreSpaceCoordinate bf -> FibreSpaceCoordinate $ \(δa,_) -> LSubspaceCoord $ bf δa
  delta (RSubspaceCoord bb) = coordinate $ case delta bb of
     FibreSpaceCoordinate bf -> FibreSpaceCoordinate $ \(_,δb) -> RSubspaceCoord $ bf δb

instance HasCoordinates S¹ where
  data CoordinateIdentifier S¹ = S¹Azimuth deriving (Eq,Show)
  coordinateAsLens S¹Azimuth = lens φParamS¹ (const S¹Polar)
  validCoordinateRange S¹Azimuth _ = (-pi, pi)

instance QC.Arbitrary (CoordinateIdentifier S¹) where
  arbitrary = return S¹Azimuth

class HasAzimuth m where
  azimuth :: Coordinate m

instance HasAzimuth S¹ where
  azimuth = coordinate S¹Azimuth

instance CoordDifferential S¹ where
  delta S¹Azimuth = coordinate . FibreSpaceCoordinate $ const xCoord
  
instance HasCoordinates S² where
  data CoordinateIdentifier S² = S²ZenithAngle | S²Azimuth deriving (Eq,Show)
  coordinateAsLens S²ZenithAngle = lens ϑParamS² (\(S²Polar _ φ) θ -> S²Polar θ φ)
  coordinateAsLens S²Azimuth = lens φParamS² (\(S²Polar θ _) φ -> S²Polar θ φ)
  validCoordinateRange S²ZenithAngle _ = (0, pi)
  validCoordinateRange S²Azimuth (S²Polar θ _)
    | θ>0 && θ<pi  = (-pi, pi)
    | otherwise    = (0, 0)

instance QC.Arbitrary (CoordinateIdentifier S²) where
  arbitrary = QC.elements [S²Azimuth, S²ZenithAngle]

instance HasAzimuth S² where
  azimuth = coordinate S²Azimuth
  
class HasZenithDistance m where
  zenithAngle :: Coordinate m

instance HasZenithDistance S² where
  zenithAngle = coordinate S²ZenithAngle

instance CoordDifferential S² where
  delta S²ZenithAngle = coordinate . FibreSpaceCoordinate
            $ \(S²Polar θ φ) -> let eθ
                                     | θ < pi/2   = embed . S¹Polar $  φ
                                     | otherwise  = embed . S¹Polar $ -φ
                                in ℝ²Coord $ OriginAxisCoord eθ eθ
  delta S²Azimuth = coordinate . FibreSpaceCoordinate
            $ \(S²Polar θ φ) -> let eφ
                                     | θ < pi/2   = embed . S¹Polar $ φ + pi/2
                                     | otherwise  = embed . S¹Polar $ pi/2 - φ
                                    sθ = sin θ + epsilon/2
                                      -- ^ Right at the poles, azimuthal movements
                                      --   become inexpressible, which manifests itself
                                      --   in giving infinite diffs. Moreover,
                                      --   we also can't retrieve tangent diffs we put
                                      --   in anymore. Arguably, this just expresses
                                      --   the fact that azimuthal changes are meaningless
                                      --   at the poles, however it violates the lens
                                      --   laws, so prevent the infinity by keeping
                                      --   sin θ very slightly above 0.
                                in ℝ²Coord $ OriginAxisCoord (eφ^*sθ) (eφ^/sθ)
                

suchThatMap :: QC.Gen a -> (a -> Maybe b) -> QC.Gen b
#if !MIN_VERSION_QuickCheck(2,11,0)
gen `suchThatMap` f =
  fmap fromJust $ fmap f gen `QC.suchThat` isJust
#else
suchThatMap = QC.suchThatMap
#endif
