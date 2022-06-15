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


module Math.Manifold.Homogeneous where

import Data.VectorSpace
import Data.AffineSpace
import Data.Basis

import Math.Manifold.Core.PseudoAffine
import Data.Manifold.PseudoAffine
import Math.Manifold.Core.Types
import Data.Manifold.Types.Primitive
import Math.Manifold.VectorSpace.ZeroDimensional
import Math.LinearMap.Category
import Data.Complex
import Linear (V0, V1, V2, V3, V4, Quaternion(..), cross)
import qualified Linear.Affine as LinAff
import Data.Monoid.Additive

import Prelude hiding (($))
import Control.Arrow.Constrained ((<<<), ($))
import Control.Applicative

import Data.Semigroup

import Data.Kind (Type)
import Data.Coerce
import Data.Type.Coercion

import Data.CallStack (HasCallStack)


newtype LieAlgebra g = LieAlgebra { getLieNeedle :: Needle g }
deriving instance (AdditiveGroup (Needle g)) => AdditiveGroup (LieAlgebra g)
instance (VectorSpace (Needle g)) => VectorSpace (LieAlgebra g) where
  type Scalar (LieAlgebra g) = Scalar (Needle g)
  μ *^ LieAlgebra v = LieAlgebra $ μ *^ v
instance (AdditiveGroup (Needle g)) => AffineSpace (LieAlgebra g) where
  type Diff (LieAlgebra g) = LieAlgebra g
  (.-.) = (^-^)
  (.+^) = (^+^)

instance (AdditiveGroup (Needle g)) => Semimanifold (LieAlgebra g) where
  type Needle (LieAlgebra g) = LieAlgebra g
  (.+~^) = (^+^)
instance (AdditiveGroup (Needle g)) => PseudoAffine (LieAlgebra g) where
  (.-~.) = fmap pure <$> (^-^)
  (.-~!) = (^-^)

coerceTensor :: ∀ v v' w . Coercible (Tensor (Scalar v) v w) (Tensor (Scalar v) v' w)
                  => Tensor (Scalar v) v w -> Tensor (Scalar v) v' w
coerceTensor = coerce

coerceTensorLin :: ∀ v v' w . Coercible (Tensor (Scalar v) v w) (Tensor (Scalar v) v' w)
                  => Tensor (Scalar v) v w -+> Tensor (Scalar v) v' w
coerceTensorLin = LinearFunction coerceTensor


instance ∀ g . (TensorSpace (Needle g)) => TensorSpace (LieAlgebra g) where
  type TensorProduct (LieAlgebra g) w = TensorProduct (Needle g) w
  coerceFmapTensorProduct _ crc
         = Coercion <<< coerceFmapTensorProduct @(Needle g) [] crc
                    <<< Coercion
  scalarSpaceWitness = case scalarSpaceWitness @(Needle g) of
    ScalarSpaceWitness -> ScalarSpaceWitness
  linearManifoldWitness = case linearManifoldWitness @(Needle g) of
    LinearManifoldWitness -> LinearManifoldWitness
  toFlatTensor = coerce (toFlatTensor @(Needle g))
  fromFlatTensor = coerce (fromFlatTensor @(Needle g))
  tensorProduct = LinearFunction $ \(LieAlgebra v)
     -> coerceTensorLin @(Needle g) <<< (tensorProduct -+$> v)
  transposeTensor = tt
   where tt :: ∀ w . (TensorSpace w, Scalar w ~ Scalar (Needle g))
                 => (LieAlgebra g ⊗ w) -+> (w ⊗ LieAlgebra g)
         tt = LinearFunction $ \(Tensor t) -> Tensor
                ( coerceFmapTensorProduct @w @[] @(Needle g) @(LieAlgebra g) [] Coercion
                $ getTensorProduct
                $ transposeTensor @(Needle g) @w
                 -+$> Tensor t )
  fmapTensor = ft
   where ft :: ∀ w x . ( TensorSpace w, Scalar w ~ Scalar (Needle g)
                       , TensorSpace x, Scalar x ~ Scalar (Needle g) )
                 => Bilinear (LinearFunction (Scalar (Needle g)) w x)
                             (LieAlgebra g ⊗ w)
                             (LieAlgebra g ⊗ x)
         ft = coerce (fmapTensor @(Needle g) @w @x)
  fzipTensorWith = ft
   where ft :: ∀ u w x . ( TensorSpace w, Scalar w ~ Scalar (Needle g)
                         , TensorSpace x, Scalar x ~ Scalar (Needle g)
                         , TensorSpace u, Scalar u ~ Scalar (Needle g) )
                 => Bilinear (LinearFunction (Scalar (Needle g)) (w,x) u)
                             (LieAlgebra g ⊗ w, LieAlgebra g ⊗ x)
                             (LieAlgebra g ⊗ u)
         ft = coerce (fzipTensorWith @(Needle g) @u @w @x)
  zeroTensor = coerceTensor @(Needle g) zeroTensor 
  addTensors = at
   where at :: ∀ w . (TensorSpace w, Scalar w ~ Scalar (Needle g))
                 => (LieAlgebra g ⊗ w) -> (LieAlgebra g ⊗ w) -> (LieAlgebra g ⊗ w)
         at = coerce (addTensors @(Needle g) @w)
  subtractTensors = st
   where st :: ∀ w . (TensorSpace w, Scalar w ~ Scalar (Needle g))
                 => (LieAlgebra g ⊗ w) -> (LieAlgebra g ⊗ w) -> (LieAlgebra g ⊗ w)
         st = coerce (subtractTensors @(Needle g) @w)
  negateTensor = nt
   where nt :: ∀ w . (TensorSpace w, Scalar w ~ Scalar (Needle g))
                 => (LieAlgebra g ⊗ w) -+> (LieAlgebra g ⊗ w)
         nt = coerce (negateTensor @(Needle g) @w)
  scaleTensor = st
   where st :: ∀ w . (TensorSpace w, Scalar w ~ Scalar (Needle g))
                 => Bilinear (Scalar (Needle g)) (LieAlgebra g ⊗ w) (LieAlgebra g ⊗ w)
         st = coerce (scaleTensor @(Needle g) @w)
  wellDefinedVector (LieAlgebra v) = LieAlgebra <$> wellDefinedVector v
  wellDefinedTensor (Tensor t) = coerceTensor @(Needle g)
       <$> wellDefinedTensor (Tensor t)
  

-- newtype LieDual

-- instance ∀ g . (LinearSpace (Needle g)) => LinearSpace (LieAlgebra g) where
  -- type DualVector (LieAlgebra g) = 


-- | Manifolds with a continuous group structure, whose 'Needle' space
--   is isomorphic to the associated Lie algebra.
--
--   Laws:
--
--   @
--   expMap zeroV ≡ mempty
--   lieBracket v w ≡ negateV (lieBracket v w)
--   ...
--   @
class (Semimanifold g, Monoid g) => LieGroup g where
  expMap :: LieAlgebra g -> g
  lieBracket :: Bilinear (LieAlgebra g) (LieAlgebra g) (LieAlgebra g)


type SO2 r = SO2_ Double
data SO2_ r = SO2 { unitReprSO2 :: Complex r }

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


type SO3 r = SO3_ Double
data SO3_ r = SO3 { unitReprSO3 :: Quaternion r }

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


