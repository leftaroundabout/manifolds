-- |
-- Module      : Data.Manifold.Cone
-- Copyright   : (c) Justus Sagemüller 2015
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsag $ hvl.no
-- Stability   : experimental
-- Portability : portable
-- 

{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE UndecidableInstances     #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE FunctionalDependencies   #-}
{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE LiberalTypeSynonyms      #-}
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE RankNTypes               #-}
{-# LANGUAGE TupleSections            #-}
{-# LANGUAGE ConstraintKinds          #-}
{-# LANGUAGE PatternGuards            #-}
{-# LANGUAGE EmptyCase                #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE UnicodeSyntax            #-}
{-# LANGUAGE MultiWayIf               #-}
{-# LANGUAGE ScopedTypeVariables      #-}
{-# LANGUAGE RecordWildCards          #-}
{-# LANGUAGE CPP                      #-}


module Data.Manifold.Cone where
    


import qualified Data.Vector.Generic as Arr
import Data.Maybe

import Data.VectorSpace
import Data.Tagged
import Data.Manifold.Types.Primitive
import Math.Manifold.Core.Types
import Data.Manifold.WithBoundary
import Data.Manifold.Types.Stiefel
import Math.LinearMap.Category

import qualified Prelude
import qualified Control.Applicative as Hask

import Control.Category.Constrained.Prelude hiding ((^))
import Control.Arrow.Constrained
import Control.Monad.Constrained
import Data.Foldable.Constrained

import Data.Manifold.PseudoAffine

import Data.Kind (Type)



instance SemimanifoldWithBoundary (CD¹ ℝ⁰) where
  type Interior (CD¹ ℝ⁰) = ℝ
  type Boundary (CD¹ ℝ⁰) = S⁰
  type HalfNeedle (CD¹ ℝ⁰) = ℝay
  smfdWBoundWitness = SmfdWBoundWitness
  fromInterior l = CD¹ (bijectℝtoIntvplus l) Origin
  separateInterior (CD¹ 0 Origin) = Left NegativeHalfSphere
  separateInterior (CD¹ 1 Origin) = Left PositiveHalfSphere
  separateInterior (CD¹ ρ Origin) = Right $ bijectIntvplustoℝ ρ
  NegativeHalfSphere |+^ Cℝay a Origin = CD¹ (bijectℝplustoIntv a) Origin
  extendToBoundary l a
   | a<0        = Just NegativeHalfSphere
   | a>0        = Just PositiveHalfSphere
   | otherwise  = Nothing

instance SemimanifoldWithBoundary ℝay where
  type Interior ℝay = ℝ
  type Boundary ℝay = ℝ⁰
  type HalfNeedle ℝay = ℝay
  Cℝay ρ Origin .+^| w
   | ρ >= -w    = Right $ ρ+w
   | otherwise  = Left (Origin, (ρ+w)/w)
  fromInterior l = Cℝay (bijectℝtoℝplus l) Origin
  fromBoundary Origin = Cℝay 0 Origin
  separateInterior (Cℝay ρ Origin)
   | ρ>0        = Right $ bijectℝplustoℝ ρ
   | otherwise  = Left Origin
  Origin |+^ a = a
  extendToBoundary l a
   | a<0        = Just Origin
   | otherwise  = Nothing

instance SemimanifoldWithBoundary (Cℝay S⁰) where
  type Interior (Cℝay S⁰) = ℝ
  type Boundary (Cℝay S⁰) = EmptyMfd ℝ⁰
  type HalfNeedle (Cℝay S⁰) = ℝay
  fromInterior l
   | l<0        = Cℝay l PositiveHalfSphere
   | otherwise  = Cℝay (-l) NegativeHalfSphere
  separateInterior (Cℝay ρ PositiveHalfSphere) = Right ρ
  separateInterior (Cℝay ρ NegativeHalfSphere) = Right $ -ρ
  b |+^ _ = case b of {}
  extendToBoundary _ _ = Nothing 




                                      




-- Some essential homeomorphisms
bijectℝtoℝplus      , bijectℝplustoℝ
 , bijectIntvtoℝplus, bijectℝplustoIntv
 ,     bijectIntvtoℝ, bijectℝtoIntv
 , bijectIntvplustoℝ, bijectℝtoIntvplus
               :: RealFloat r => r -> r

bijectℝplustoℝ x = x - 1/x
bijectℝtoℝplus y = y/2 + sqrt(y^2/4 + 1)

-- [0, 1[ ↔ ℝ⁺
bijectℝplustoIntv y = 1 - recip (y+1)
bijectIntvtoℝplus x = recip(1-x) - 1

-- ]-1, 1[ ↔ ℝ  (Similar to 'tanh', but converges less quickly towards ±1.)
bijectℝtoIntv y | y>0        = -1/(2*y) + sqrt(1/(4*y^2) + 1)
                | y<0        = -1/(2*y) - sqrt(1/(4*y^2) + 1)
                | otherwise  = 0
                 -- 0 = x² + x/y - 1
                 -- x = -1/2y ± sqrt(1/4y² + 1)
bijectIntvtoℝ x = x / (1-x^2)

-- ]0, 1[ ↔ ℝ
bijectℝtoIntvplus y = (bijectℝtoIntv y + 1)/2
bijectIntvplustoℝ x = bijectIntvtoℝ $ x*2 - 1

embCℝayToCD¹ :: RealFloat (Scalar (Needle m)) => Cℝay m -> CD¹ m
embCℝayToCD¹ (Cℝay h m) = CD¹ (bijectℝplustoIntv h) m

projCD¹ToCℝay :: RealFloat (Scalar (Needle m)) => CD¹ m -> Cℝay m
projCD¹ToCℝay (CD¹ h m) = Cℝay (bijectIntvtoℝplus h) m


stiefel1Project :: LinearSpace v =>
             DualVector v       -- ^ Must be nonzero.
                 -> Stiefel1 v
stiefel1Project = Stiefel1

stiefel1Embed :: (HilbertSpace v, RealFloat (Scalar v)) => Stiefel1 v -> v
stiefel1Embed (Stiefel1 n) = normalized n
  

class (PseudoAffine v, InnerSpace v, NaturallyEmbedded (UnitSphere v) (DualVector v))
          => HasUnitSphere v where
  type UnitSphere v :: *
  stiefel :: UnitSphere v -> Stiefel1 v
  stiefel = Stiefel1 . embed
  unstiefel :: Stiefel1 v -> UnitSphere v
  unstiefel = coEmbed . getStiefel1N

instance HasUnitSphere ℝ  where type UnitSphere ℝ  = S⁰

instance HasUnitSphere ℝ² where type UnitSphere ℝ² = S¹

instance HasUnitSphere ℝ³ where type UnitSphere ℝ³ = S²




