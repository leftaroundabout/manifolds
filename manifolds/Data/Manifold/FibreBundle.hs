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
import Data.VectorSpace

import Data.Manifold.Types.Primitive
import Data.Manifold.PseudoAffine
    
import qualified Prelude as Hask

import Control.Category.Constrained.Prelude
import Control.Arrow.Constrained

import Data.Tagged


class (PseudoAffine m, m ~ Interior m, Category k)
           => ParallelTransporting k m f where
  parallelTransport :: m -> Needle m -> k f f

instance (PseudoAffine m, m ~ Interior m, s ~ (Scalar (Needle m)))
      => ParallelTransporting (->) m (ZeroDim s) where
  parallelTransport _ _ Origin = Origin

instance ParallelTransporting (->) ℝ ℝ where
  parallelTransport _ _ x = x

instance ParallelTransporting (->) S⁰ ℝ⁰ where
  parallelTransport _ _ x = x
instance ParallelTransporting (->) S¹ ℝ where
  parallelTransport _ _ x = x
instance ParallelTransporting (->) S² ℝ² where
  parallelTransport p@(S² θ₀ φ₀) v x = case p.+~^v of
      S² θ₁ φ₁ -> undefined

instance (ParallelTransporting (->) a fa, ParallelTransporting (->) b fb)
              => ParallelTransporting (->) (a,b) (fa,fb) where
  parallelTransport (pa,pb) (va,vb) (xa,xb)
       = (parallelTransport pa va xa, parallelTransport pb vb xb)

instance (ParallelTransporting (->) a f, ParallelTransporting (->) a g)
              => ParallelTransporting (->) a (f,g) where
  parallelTransport p v (x,y)
       = (parallelTransport p v x, parallelTransport p v y)


instance (ParallelTransporting (->) m f, AdditiveGroup m, AdditiveGroup f)
                => AdditiveGroup (FibreBundle m f)

instance ∀ m f .
         ( ParallelTransporting (->) m (Interior f), Semimanifold f
         , ParallelTransporting (->) (Needle m) (Needle f) )
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

instance ∀ m f .
         ( ParallelTransporting (->) m f, ParallelTransporting (->) m (Interior f)
         , PseudoAffine f
         , ParallelTransporting (->) (Needle m) (Needle f) )
                => PseudoAffine (FibreBundle m f) where
  pseudoAffineWitness = case ( pseudoAffineWitness :: PseudoAffineWitness m
                             , pseudoAffineWitness :: PseudoAffineWitness f ) of
     ( PseudoAffineWitness (SemimanifoldWitness BoundarylessWitness)
      ,PseudoAffineWitness (SemimanifoldWitness BoundarylessWitness) )
         -> PseudoAffineWitness (SemimanifoldWitness BoundarylessWitness)
  FibreBundle p f .-~. FibreBundle q g = case p.-~.q of
      Nothing -> Nothing
      Just v  -> FibreBundle v <$> f .-~. parallelTransport p v g
