-- |
-- Module      : Data.Manifold.Cone
-- Copyright   : (c) Justus Sagemüller 2015
-- License     : GPL v3
-- 
-- Maintainer  : (@) sagemueller $ geo.uni-koeln.de
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
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE UnicodeSyntax            #-}
{-# LANGUAGE MultiWayIf               #-}
{-# LANGUAGE ScopedTypeVariables      #-}
{-# LANGUAGE RecordWildCards          #-}
{-# LANGUAGE CPP                      #-}


module Data.Manifold.Cone where
    


import qualified Data.Vector.Generic as Arr
import Data.Maybe
import Data.Semigroup

import Data.VectorSpace
import Data.Tagged
import Data.Manifold.Types.Primitive
import Data.Manifold.Types.Stiefel
import Math.LinearMap.Category

import Data.CoNat

import qualified Prelude
import qualified Control.Applicative as Hask

import Control.Category.Constrained.Prelude hiding ((^))
import Control.Arrow.Constrained
import Control.Monad.Constrained
import Data.Foldable.Constrained

import Data.Manifold.PseudoAffine



newtype ConeVecArr m = ConeVecArr {getConeVecArr :: CℝayInterior m}
type ConeNeedle m = Needle (ConeVecArr m)
data SConn'dConeVecArr m = SConn'dConeVecArr ℝ (Interior m)


class ( Semimanifold m, Semimanifold (Interior (Interior m))
      , Semimanifold (ConeVecArr m)
      , Interior (ConeVecArr m) ~ ConeVecArr m )
           => ConeSemimfd m where
  {-# MINIMAL (fromCℝayInterior | fromCD¹Interior)
            , (toCℝayInterior | toCD¹Interior) #-}
  type CℝayInterior m :: *
  
  fromCℝayInterior :: ConeVecArr m -> Cℝay m
  fromCℝayInterior = projCD¹ToCℝay . fromCD¹Interior
  fromCD¹Interior :: ConeVecArr m -> CD¹ m
  fromCD¹Interior = embCℝayToCD¹ . fromCℝayInterior
  
  toCℝayInterior :: Cℝay m -> Option (ConeVecArr m)
  toCℝayInterior = toCD¹Interior . embCℝayToCD¹
  toCD¹Interior :: CD¹ m -> Option (ConeVecArr m)
  toCD¹Interior = toCℝayInterior . projCD¹ToCℝay

  



instance (ConeSemimfd m) => Semimanifold (Cℝay m) where
  type Needle (Cℝay m) = ConeNeedle m
  type Interior (Cℝay m) = ConeVecArr m
  fromInterior = fromCℝayInterior
  toInterior = toCℝayInterior
  translateP = ctp
   where ctp :: Tagged (Cℝay m) (ConeVecArr m -> ConeNeedle m -> ConeVecArr m)
         ctp = Tagged ctp'
          where Tagged ctp' = translateP
                  :: Tagged (ConeVecArr m) (ConeVecArr m -> ConeNeedle m -> ConeVecArr m)
  
instance (ConeSemimfd m) => Semimanifold (CD¹ m) where
  type Needle (CD¹ m) = ConeNeedle m
  type Interior (CD¹ m) = ConeVecArr m
  fromInterior = fromCD¹Interior
  toInterior = toCD¹Interior
  translateP = ctp
   where ctp :: Tagged (CD¹ m) (ConeVecArr m -> ConeNeedle m -> ConeVecArr m)
         ctp = Tagged ctp'
          where Tagged ctp' = translateP
                  :: Tagged (ConeVecArr m) (ConeVecArr m -> ConeNeedle m -> ConeVecArr m)




                                      




-- Some essential homeomorphisms
bijectℝtoℝplus      , bijectℝplustoℝ
 , bijectIntvtoℝplus, bijectℝplustoIntv
 ,     bijectIntvtoℝ, bijectℝtoIntv
               :: ℝ -> ℝ

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

embCℝayToCD¹ :: Cℝay m -> CD¹ m
embCℝayToCD¹ (Cℝay h m) = CD¹ (bijectℝplustoIntv h) m

projCD¹ToCℝay :: CD¹ m -> Cℝay m
projCD¹ToCℝay (CD¹ h m) = Cℝay (bijectIntvtoℝplus h) m


stiefel1Project :: LinearManifold v =>
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




