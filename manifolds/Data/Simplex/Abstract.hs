-- |
-- Module      : Data.Simplex.Abstract
-- Copyright   : (c) Justus Sagemüller 2018
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsagemue $ uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 

{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE StandaloneDeriving       #-}
{-# LANGUAGE DeriveFunctor            #-}
{-# LANGUAGE DeriveFoldable           #-}
{-# LANGUAGE DeriveTraversable        #-}
{-# LANGUAGE UndecidableInstances     #-}
{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE FlexibleInstances        #-}

module Data.Simplex.Abstract where

import Data.Manifold.Types.Primitive
import Math.Manifold.Core.PseudoAffine
import Data.Manifold.PseudoAffine

import Math.LinearMap.Category (spanVariance, dualNorm', (<$|), (<.>^), SimpleSpace)

import Data.Foldable (toList)
import Data.Traversable (Traversable)

import GHC.Generics

data family AbstractSimplex v x

data instance AbstractSimplex ℝ⁰ x = ℝ⁰Simplex !x
 deriving (Functor, Foldable, Traversable)
instance Applicative (AbstractSimplex ℝ⁰) where
  pure = ℝ⁰Simplex
  ℝ⁰Simplex p <*> ℝ⁰Simplex q = ℝ⁰Simplex $ p q

data instance AbstractSimplex ℝ  x = ℝSimplex !x !x
 deriving (Functor, Foldable, Traversable)
data instance AbstractSimplex ℝ¹ x = ℝ¹Simplex !x !x
 deriving (Functor, Foldable, Traversable)

data instance AbstractSimplex ℝ² x = ℝ²Simplex !x !x !x
 deriving (Functor, Foldable, Traversable)

data instance AbstractSimplex ℝ³ x = ℝ³Simplex !x !x !x !x
 deriving (Functor, Foldable, Traversable)

data instance AbstractSimplex ℝ⁴ x = ℝ⁴Simplex !x !x !x !x !x
 deriving (Functor, Foldable, Traversable)

data instance AbstractSimplex (ℝ, v) x = ConeSimplex !x !(AbstractSimplex v x)
deriving instance (Functor (AbstractSimplex v)) => Functor (AbstractSimplex (ℝ,v))
deriving instance (Foldable (AbstractSimplex v)) => Foldable (AbstractSimplex (ℝ,v))
deriving instance (Traversable (AbstractSimplex v)) => Traversable (AbstractSimplex (ℝ,v))

newtype instance AbstractSimplex (GenericNeedle m) x
       = GenericSimplex (AbstractSimplex (Rep m ()) x)
deriving instance (Functor (AbstractSimplex (Rep m ())))
         => Functor (AbstractSimplex (GenericNeedle m))
deriving instance (Foldable (AbstractSimplex (Rep m ())))
         => Foldable (AbstractSimplex (GenericNeedle m))
deriving instance (Traversable (AbstractSimplex (Rep m ())))
         => Traversable (AbstractSimplex (GenericNeedle m))

newtype instance AbstractSimplex (NeedleProductSpace f g p) x
         = GenProdSimplex (AbstractSimplex (Needle (f p), Needle (g p)) x)
deriving instance (Functor (AbstractSimplex (Needle (f p), Needle (g p))))
         => Functor (AbstractSimplex (NeedleProductSpace f g p))
deriving instance (Foldable (AbstractSimplex (Needle (f p), Needle (g p))))
         => Foldable (AbstractSimplex (NeedleProductSpace f g p))
deriving instance (Traversable (AbstractSimplex (Needle (f p), Needle (g p))))
         => Traversable (AbstractSimplex (NeedleProductSpace f g p))


type Simplex m = AbstractSimplex (Needle m) m


seenFromOneVertex :: (WithField ℝ Manifold m, Foldable (AbstractSimplex (Needle m)))
       => Simplex m -> (m, [Needle m])
seenFromOneVertex s = case toList s of
      (p₀:ps) -> (p₀, [ case p.-~.p₀ of
                         Just v -> v
                         Nothing -> error "A simplex must always be path-connected."
                      | p <- ps ])
      [] -> error "A simplex type must contain at least one value!"     

toBarycentric :: ( WithField ℝ Manifold m
                 , Foldable (AbstractSimplex (Needle m))
                 , SimpleSpace (Needle m) )
       => Simplex m -> m -> [ℝ]
toBarycentric s = case seenFromOneVertex s of
     (p₀, vs) -> let v's = (dualNorm' (spanVariance vs)<$|) <$> vs
                 in \q -> case q.-~.p₀ of
                           Just w -> let vws = (<.>^w) <$> v's
                                     in (1 - sum vws) : vws
                           Nothing -> []

simplicesIntersect :: (WithField ℝ Manifold m) => Simplex m -> Simplex m -> Bool
simplicesIntersect = undefined
