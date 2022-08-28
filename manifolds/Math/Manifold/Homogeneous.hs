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
    , SO
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
import GHC.TypeLits (Nat)
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


data family SO_ (n :: Nat) (r :: Type)

type SO n = SO_ n Double

data instance SO_ 1 r = SO1Identity
 deriving (Eq, Show)

instance (QC.Arbitrary r, Floating r) => QC.Arbitrary (SO_ 1 r) where
  arbitrary = pure SO1Identity

instance Semigroup (SO_ 1 r) where
  SO1Identity <> SO1Identity = SO1Identity
instance Monoid (SO_ 1 r) where
  mempty = SO1Identity
  mappend = (<>)

instance RealFloat' r => Semimanifold (SO_ 1 r) where
  type Needle (SO_ 1 r) = ZeroDim r
  SO1Identity .+~^ Origin = SO1Identity
  semimanifoldWitness = case linearManifoldWitness @r of
    LinearManifoldWitness -> SemimanifoldWitness

newtype instance SO_ 2 r = SO2 { unitReprSO2 :: Complex r }
 deriving (Eq, Show)

instance (QC.Arbitrary r, Floating r) => QC.Arbitrary (SO_ 2 r) where
  arbitrary = SO2 . ℂ.cis <$> QC.arbitrary

instance RealFloat r => Semigroup (SO_ 2 r) where
  SO2 a <> SO2 b = SO2 $ a*b  -- perhaps should normalize?
instance RealFloat r => Monoid (SO_ 2 r) where
  mempty = SO2 1
  mappend = (<>)

instance RealFloat' r => Semimanifold (SO_ 2 r) where
  type Needle (SO_ 2 r) = r
  p .+~^ d = p <> expMap (LieAlgebra d)
  semimanifoldWitness = case linearManifoldWitness @r of
    LinearManifoldWitness -> SemimanifoldWitness

instance RealFloat' r => LieGroup (SO_ 2 r) where
  expMap = SO2 . cis . getLieNeedle
  lieBracket = zeroV


newtype instance SO_ 3 r = SO3 { unitReprSO3 :: Quaternion r }
 deriving (Eq, Show)

instance (QC.Arbitrary r, RealFloat r) => QC.Arbitrary (SO_ 3 r) where
  arbitrary = do
    (a,b,c,d) <- QC.arbitrary
    pure . SO3 $ case sqrt . sum $ (^2)<$>[a,b,c,d] of
      l | l>0       -> Quaternion (a/l) (V3 b c d ^/ l)
        | otherwise -> 1

instance RealFloat r => Semigroup (SO_ 3 r) where
  SO3 a <> SO3 b = SO3 $ a*b  -- perhaps should normalize?
instance RealFloat r => Monoid (SO_ 3 r) where
  mempty = SO3 1
  mappend = (<>)

instance RealFloat' r => Semimanifold (SO_ 3 r) where
  type Needle (SO_ 3 r) = V3 r
  p .+~^ d = p <> expMap (LieAlgebra d)
  semimanifoldWitness = case linearManifoldWitness @r of
    LinearManifoldWitness -> SemimanifoldWitness

instance ∀ r . RealFloat' r => LieGroup (SO_ 3 r) where
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

instance RealFloat' r => SO_ 2 r`ActsOn`S¹_ r where
  action (SO2 β) p = p .+~^ ℂ.phase β

instance RealFloat' r => SO_ 3 r`ActsOn`S²_ r where
  action (SO3 γ) p = projectPureImagUnitQuaternion $ γ * α * recip γ
   where α = embedPureImagUnitQuaternion p

