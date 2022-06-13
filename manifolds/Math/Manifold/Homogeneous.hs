-- |
-- Module      : Math.Manifold.Homogeneous
-- Copyright   : (c) Justus Sagemüller 2022
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsag $ hvl.no
-- Stability   : experimental
-- Portability : portable
-- 

{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE UndecidableInstances     #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE DefaultSignatures        #-}
{-# LANGUAGE DeriveGeneric            #-}
{-# LANGUAGE StandaloneDeriving       #-}
{-# LANGUAGE ConstraintKinds          #-}
{-# LANGUAGE UnicodeSyntax            #-}
{-# LANGUAGE ScopedTypeVariables      #-}
{-# LANGUAGE AllowAmbiguousTypes      #-}
{-# LANGUAGE TypeApplications         #-}
{-# LANGUAGE RankNTypes               #-}
{-# LANGUAGE EmptyCase                #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE TypeInType               #-}
{-# LANGUAGE CPP                      #-}


module Math.Manifold.Homogeneous where

import Data.VectorSpace
import Data.AffineSpace
import Data.Basis

import Math.Manifold.Core.PseudoAffine
import Math.Manifold.Core.Types
import Data.Manifold.Types.Primitive
import Math.Manifold.VectorSpace.ZeroDimensional
import Data.Complex
import Linear (V0, V1, V2, V3, V4, Quaternion)
import qualified Linear.Affine as LinAff
import Data.Monoid.Additive

import Control.Applicative
import Control.Arrow

import Data.Kind (Type)

import Data.CallStack (HasCallStack)

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
  expMap :: Needle g -> g
  lieBracket :: Needle g -> Needle g -> Needle g


type SO2 r = SO2_ Double
data SO2_ r = SO2 { unitReprSO2 :: Complex r }

instance RealFloat r => Semigroup (SO2_ r) where
  SO2 a <> SO2 b = SO2 $ a*b  -- perhaps should normalize?
instance RealFloat r => Monoid (SO2_ r) where
  mempty = SO2 1

