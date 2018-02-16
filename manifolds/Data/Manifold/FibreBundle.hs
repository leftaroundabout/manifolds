-- |
-- Module      : Data.Manifold.FibreBundle
-- Copyright   : (c) Justus Sagemüller 2018
-- License     : GPL v3
-- 
-- Maintainer  : (@) sagemueller $ geo.uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 

{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE UnicodeSyntax              #-}


module Data.Manifold.FibreBundle where


import Data.AdditiveGroup

import Data.Manifold.Types.Primitive
import Data.Manifold.PseudoAffine
    
import qualified Prelude as Hask

import Control.Category.Constrained.Prelude
import Control.Arrow.Constrained

import Data.Tagged


class (PseudoAffine m, m ~ Interior m, v ~ Needle m)
           => ParallelTransporting m v f | m -> v where
  parallelTransport :: m -> v -> f -> f

instance ParallelTransporting ℝ ℝ ℝ where
  parallelTransport _ _ x = x

instance (ParallelTransporting a va fa, ParallelTransporting b vb fb)
              => ParallelTransporting (a,b) (va,vb) (fa,fb) where
  parallelTransport (pa,pb) (va,vb) (xa,xb)
       = (parallelTransport pa va xa, parallelTransport pb vb xb)

instance (ParallelTransporting a v f, ParallelTransporting a v g)
              => ParallelTransporting a v (f,g) where
  parallelTransport p v (x,y)
       = (parallelTransport p v x, parallelTransport p v y)


instance (ParallelTransporting m v f, AdditiveGroup m, AdditiveGroup f)
                => AdditiveGroup (FibreBundle m f)

instance ∀ m v f .
         ( ParallelTransporting m v (Interior f), Semimanifold f
         , ParallelTransporting v (Needle v) (Needle f) )
                => Semimanifold (FibreBundle m f) where
  type Interior (FibreBundle m f) = FibreBundle m (Interior f)
  type Needle (FibreBundle m f) = FibreBundle (Needle m) (Needle f)
  toInterior (FibreBundle p f) = FibreBundle p <$> toInterior f
  translateP = Tagged $ case ( translateP :: Tagged m (Interior m -> Needle m -> Interior m)
                             , semimanifoldWitness :: SemimanifoldWitness f) of
      (Tagged tpm, SemimanifoldWitness BoundarylessWitness)
           -> \(FibreBundle p f) (FibreBundle v δf)
                   -> FibreBundle (tpm p v) (parallelTransport p v f.+~^δf)
  semimanifoldWitness = case ( semimanifoldWitness :: SemimanifoldWitness m
                             , semimanifoldWitness :: SemimanifoldWitness f ) of
         (SemimanifoldWitness BoundarylessWitness, SemimanifoldWitness BoundarylessWitness)
           -> SemimanifoldWitness BoundarylessWitness
  FibreBundle p f .+~^ FibreBundle v δf
      = FibreBundle (p.+~^v) (parallelTransport p v f.+~^δf)
