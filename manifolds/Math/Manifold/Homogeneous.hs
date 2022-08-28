-- |
-- Module      : Math.Manifold.Homogeneous
-- Copyright   : (c) Justus Sagemüller 2022
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsag $ hvl.no
-- Stability   : experimental
-- Portability : portable
-- 

{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE UnicodeSyntax              #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE EmptyCase                  #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE TypeInType                 #-}
{-# LANGUAGE CPP                        #-}
{-# LANGUAGE TemplateHaskell            #-}


module Math.Manifold.Homogeneous
    ( LieGroup(..), LieAlgebra, ActsOn(..)
    , SO2(..), SO3(..)
    ) where

import Data.VectorSpace
import Data.AffineSpace
import Data.Basis

import Math.Manifold.Core.PseudoAffine
import Data.Manifold.PseudoAffine
import Math.Manifold.Core.Types
import Data.Manifold.Types.Primitive
import Math.Manifold.VectorSpace.ZeroDimensional
import Math.LinearMap.Category
import Math.VectorSpace.Dual
import Data.Complex as ℂ
import Linear (V0, V1, V2, V3(..), V4, Quaternion(..), cross)
import qualified Linear.Affine as LinAff
import Data.Monoid.Additive

import Prelude hiding (($), (^))
import Control.Arrow.Constrained ((<<<), ($))
import Control.Applicative

import Data.Semigroup hiding (Dual)

import qualified Test.QuickCheck as QC

import Data.Kind (Type)
import Data.Coerce
import Data.Type.Coercion


newtype LieAlgebra g
    = LieAlgebra { getLieNeedle :: Needle g }

copyNewtypeInstances [t| ∀ g . (Semimanifold g) => LieAlgebra g |]
    [''AdditiveGroup]



-- | Manifolds with a continuous group structure, whose 'Needle' space
--   is isomorphic to the associated Lie algebra.
--
--   Laws:
--
--   @
--   expMap zeroV ≡ mempty
--   lieBracket w v ≡ negateV (lieBracket v w)
--   ...
--   @
class (Semimanifold g, Monoid g) => LieGroup g where
  expMap :: LieAlgebra g -> g
  lieBracket :: Bilinear (LieAlgebra g) (LieAlgebra g) (LieAlgebra g)


type SO2 = SO2_ Double
newtype SO2_ r = SO2 { unitReprSO2 :: Complex r }
 deriving (Eq, Show)

instance (QC.Arbitrary r, Floating r) => QC.Arbitrary (SO2_ r) where
  arbitrary = SO2 . ℂ.cis <$> QC.arbitrary

instance RealFloat r => Semigroup (SO2_ r) where
  SO2 a <> SO2 b = SO2 $ a*b  -- perhaps should normalize?
instance RealFloat r => Monoid (SO2_ r) where
  mempty = SO2 1
  mappend = (<>)

instance RealFloat' r => Semimanifold (SO2_ r) where
  type Needle (SO2_ r) = r
  p .+~^ d = p <> expMap (LieAlgebra d)
  semimanifoldWitness = case linearManifoldWitness @r of
    LinearManifoldWitness -> SemimanifoldWitness

instance RealFloat' r => LieGroup (SO2_ r) where
  expMap = SO2 . cis . getLieNeedle
  lieBracket = zeroV


type SO3 = SO3_ Double
newtype SO3_ r = SO3 { unitReprSO3 :: Quaternion r }
 deriving (Eq, Show)

instance (QC.Arbitrary r, RealFloat r) => QC.Arbitrary (SO3_ r) where
  arbitrary = do
    (a,b,c,d) <- QC.arbitrary
    pure . SO3 $ case sqrt . sum $ (^2)<$>[a,b,c,d] of
      l | l>0       -> Quaternion (a/l) (V3 b c d ^/ l)
        | otherwise -> 1

instance RealFloat r => Semigroup (SO3_ r) where
  SO3 a <> SO3 b = SO3 $ a*b  -- perhaps should normalize?
instance RealFloat r => Monoid (SO3_ r) where
  mempty = SO3 1
  mappend = (<>)

instance RealFloat' r => Semimanifold (SO3_ r) where
  type Needle (SO3_ r) = V3 r
  p .+~^ d = p <> expMap (LieAlgebra d)
  semimanifoldWitness = case linearManifoldWitness @r of
    LinearManifoldWitness -> SemimanifoldWitness

instance ∀ r . RealFloat' r => LieGroup (SO3_ r) where
  expMap (LieAlgebra a) = SO3 . exp $ Quaternion 0 a
  lieBracket = coerce (cross :: V3 r -> V3 r -> V3 r)

embedPureImagUnitQuaternion :: RealFloat r => S²_ r -> Quaternion r
embedPureImagUnitQuaternion = Quaternion 0 . embed

projectPureImagUnitQuaternion :: RealFloat r => Quaternion r -> S²_ r
projectPureImagUnitQuaternion (Quaternion _ p) = coEmbed p

-- | Manifolds that are homogeneous with respect to action by a Lie group.
--   Laws:
--
--   @
--   action mempty ≡ id                  (Identity)
--   action (a<>b) ≡ action a . action b (Compatibility)
--   @
class (Semimanifold m, LieGroup g) => g `ActsOn` m where
  action :: g -> m -> m

instance RealFloat' r => SO2_ r`ActsOn`S¹_ r where
  action (SO2 β) p = p .+~^ ℂ.phase β

instance RealFloat' r => SO3_ r`ActsOn`S²_ r where
  action (SO3 γ) p = projectPureImagUnitQuaternion $ γ * α * recip γ
   where α = embedPureImagUnitQuaternion p

