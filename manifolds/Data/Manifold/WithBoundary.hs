-- |
-- Module      : Data.Manifold.WithBoundary
-- Copyright   : (c) Justus Sagemüller 2020
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
{-# LANGUAGE UnicodeSyntax            #-}
{-# LANGUAGE ScopedTypeVariables      #-}
{-# LANGUAGE AllowAmbiguousTypes      #-}
{-# LANGUAGE TypeApplications         #-}
{-# LANGUAGE EmptyCase                #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE TypeInType               #-}


module Data.Manifold.WithBoundary where

import Data.VectorSpace
import Data.AffineSpace
import Data.Basis

import Math.Manifold.Core.PseudoAffine
import Math.Manifold.Core.Types
import Data.Manifold.Types.Primitive
import Math.Manifold.VectorSpace.ZeroDimensional

import Control.Applicative
import Control.Arrow

import qualified GHC.Generics as Gnrx
import GHC.Generics (Generic, (:*:)(..))
import Data.Kind (Type)

import Data.CallStack (HasCallStack)


class AdditiveMonoid h where
  zeroHV :: h
  addHVs :: h -> h -> h

class (AdditiveMonoid h, VectorSpace (FullSubspace h)) => HalfSpace h where
  type FullSubspace h :: Type
  scaleNonNeg :: ℝay -> h -> h
  fromFullSubspace :: FullSubspace h -> h
  projectToFullSubspace :: h -> FullSubspace h

instance AdditiveMonoid (ZeroDim k) where
  zeroHV = Origin
  addHVs Origin Origin = Origin
instance HalfSpace (ZeroDim k) where
  type FullSubspace (ZeroDim k) = ZeroDim k
  scaleNonNeg _ Origin = Origin
  fromFullSubspace _ = Origin
  projectToFullSubspace Origin = Origin

instance AdditiveMonoid ℝay where
  zeroHV = Cℝay 0 Origin
  addHVs (Cℝay a Origin) (Cℝay b Origin) = Cℝay (a+b) Origin
instance HalfSpace ℝay where
  type FullSubspace ℝay = ℝ⁰
  scaleNonNeg (Cℝay μ Origin) (Cℝay l Origin) = Cℝay (μ*l) Origin
  fromFullSubspace o = Cℝay 0 o
  projectToFullSubspace (Cℝay _ o) = o

class ( Semimanifold (Interior m), Semimanifold (Boundary m)
      , HalfSpace (HalfNeedle m), FullSubspace (HalfNeedle m) ~ Needle (Boundary m)
      ) => SemimanifoldWithBoundary m where
  type Interior m :: Type
  type Boundary m :: Type
  type HalfNeedle m :: Type
  (|+^) :: Boundary m -> HalfNeedle m -> m
  (.+^|) :: m
         -- ^ Starting point @p@
         -> Needle (Interior m)
         -- ^ Displacement @v@
         -> Either (Boundary m, Scalar (Needle (Interior m)))
                   (Interior m)
         -- ^ If @v@ is enough to leave @m@, yield the point where it does and what
         --   fraction of the length is still left (i.e. how much of @v@ “pokes out
         --   of the space). If it stays within the space, just give back the result.
  fromInterior :: Interior m -> m
  fromBoundary :: Boundary m -> m
  separateInterior :: m -> Either (Boundary m) (Interior m)
  separateInterior p = case p .+^| zeroV of
    Left (b,_) -> Left b 
    Right i -> Right i
  toInterior :: m -> Maybe (Interior m)
  toInterior p = case separateInterior p of
    Right i -> Just i
    Left _  -> Nothing
  extendToBoundary :: Interior m -> Needle (Interior m) -> Maybe (Boundary m)
  default extendToBoundary :: ( VectorSpace (Needle (Interior m))
                              , Num (Scalar (Needle (Interior m))) )
           => Interior m -> Needle (Interior m) -> Maybe (Boundary m)
  extendToBoundary p dir = case fromInterior @m p .+^| dir of
    Right _ -> extendToBoundary @m p $ dir^*2
    Left (p, _) -> Just p

class (SemimanifoldWithBoundary m, PseudoAffine (Interior m), PseudoAffine (Boundary m))
          => PseudoAffineWithBoundary m where
  (.-|) :: m -> Boundary m -> Maybe (HalfNeedle m)
  p.-|b = Just $ p!-|b
  (!-|) :: m -> Boundary m -> HalfNeedle m
  (.--.) :: m -> m -> Maybe (Needle (Interior m))
  p.--.q = Just $ p.--!q
  (.--!) :: m -> m -> Needle (Interior m)

class PseudoAffineWithBoundary m => ProjectableBoundary m where
  projectToBoundary :: m
                    -- ^ Point @p@ to project
                    -> Boundary m 
                    -- ^ Intended “course region” representative @r@ on boundary – we
                    --   seek a point that is reachable from there.
                    -> Maybe ( Needle (Boundary m)
                             , Scalar (Needle (Interior m)) )
                    -- ^ Needle @δr@ connecting @r@ to projection of the @p@, and
                    --   a measure @d@ of normal-distance such that
                    --   @'marginFromBoundary' (r.+~^δr) d == p@.
  marginFromBoundary :: Boundary m -> Scalar (Needle (Interior m)) -> m

instance SemimanifoldWithBoundary (ZeroDim k) where
  type Interior (ZeroDim k) = ZeroDim k
  type Boundary (ZeroDim k) = EmptyMfd (ZeroDim k)
  type HalfNeedle (ZeroDim k) = ZeroDim k
  fromInterior = id
  fromBoundary b = case b of {}
  separateInterior = Right
  p|+^_ = case p of {}
  Origin .+^| Origin = Right Origin
  extendToBoundary _ _ = Nothing

instance PseudoAffineWithBoundary (ZeroDim k) where
  _.-|p = case p of {}
  Origin .--! Origin = Origin

instance SemimanifoldWithBoundary ℝ where
  type Interior ℝ = ℝ
  type Boundary ℝ = EmptyMfd ℝ⁰
  type HalfNeedle ℝ = ℝay
  fromInterior = id
  fromBoundary b = case b of {}
  separateInterior = Right
  p|+^_ = case p of {}
  a.+^|b = Right $ a+b
  extendToBoundary _ _ = Nothing

instance PseudoAffineWithBoundary ℝ where
  _!-|p = case p of {}
  (.--!) = (-)

data ProductBoundary a b
  = BoundOfL !(Boundary a) !(Interior b)
  | BoundOfR !(Interior a) !(Boundary b)

data ProductBoundaryNeedle a b
  = ZeroProductBoundaryNeedle
  | NBoundOfL !(Needle (Boundary a)) !(Needle (Interior b))
  | NBoundOfR !(Needle (Interior a)) !(Needle (Boundary b))

instance ( AdditiveGroup (Needle (Boundary a)), AdditiveGroup (Needle (Interior b))
         , AdditiveGroup (Needle (Interior a)), AdditiveGroup (Needle (Boundary b)) )
    => AdditiveGroup (ProductBoundaryNeedle a b) where
  zeroV = ZeroProductBoundaryNeedle
  ZeroProductBoundaryNeedle ^+^ n = n
  n ^+^ ZeroProductBoundaryNeedle = n
  NBoundOfL x y ^+^ NBoundOfL ξ υ = NBoundOfL (x^+^ξ) (y^+^υ)
  NBoundOfR x y ^+^ NBoundOfR ξ υ = NBoundOfR (x^+^ξ) (y^+^υ)
  negateV ZeroProductBoundaryNeedle = ZeroProductBoundaryNeedle
  negateV (NBoundOfL x y) = NBoundOfL (negateV x) (negateV y)
  negateV (NBoundOfR x y) = NBoundOfR (negateV x) (negateV y)

instance ( VectorSpace (Needle (Boundary a)), VectorSpace (Needle (Interior b))
         , VectorSpace (Needle (Interior a)), VectorSpace (Needle (Boundary b))
         , Scalar (Needle (Interior b)) ~ Scalar (Needle (Boundary a))
         , Scalar (Needle (Interior a)) ~ Scalar (Needle (Boundary a))
         , Scalar (Needle (Boundary b)) ~ Scalar (Needle (Boundary a))
         )
    => VectorSpace (ProductBoundaryNeedle a b) where
  type Scalar (ProductBoundaryNeedle a b) = Scalar (Needle (Boundary a))
  _ *^ ZeroProductBoundaryNeedle = ZeroProductBoundaryNeedle
  μ *^ NBoundOfL x y = NBoundOfL (μ*^x) (μ*^y)
  μ *^ NBoundOfR x y = NBoundOfR (μ*^x) (μ*^y)

instance ( VectorSpace (Needle (Boundary a)), VectorSpace (Needle (Interior b))
         , VectorSpace (Needle (Interior a)), VectorSpace (Needle (Boundary b))
         , Scalar (Needle (Interior b)) ~ Scalar (Needle (Boundary a))
         , Scalar (Needle (Interior a)) ~ Scalar (Needle (Boundary a))
         , Scalar (Needle (Boundary b)) ~ Scalar (Needle (Boundary a))
         )
    => Semimanifold (ProductBoundaryNeedle a b) where
  type Needle (ProductBoundaryNeedle a b) = ProductBoundaryNeedle a b
  (.+~^) = (^+^)
  semimanifoldWitness = SemimanifoldWitness
  

instance ∀ a b . ( ProjectableBoundary a, ProjectableBoundary b
                 , VectorSpace (Needle (Boundary a)), VectorSpace (Needle (Interior b))
                 , VectorSpace (Needle (Interior a)), VectorSpace (Needle (Boundary b))
                 , Scalar (Needle (Interior b)) ~ Scalar (Needle (Boundary a))
                 , Scalar (Needle (Interior a)) ~ Scalar (Needle (Boundary a))
                 , Scalar (Needle (Boundary b)) ~ Scalar (Needle (Boundary a))
                 )
   => Semimanifold (ProductBoundary a b) where
  type Needle (ProductBoundary a b) = ProductBoundaryNeedle a b
--ProductBoundary x y.+~^(δx, δy)
--     = case (separateInterior x, separateInterior y) of
-- (Left bx, Right _) -> case y .+^| δy of
--            Right iy' -> undefined
  (.+~^) = undefined
  semimanifoldWitness = case ( semimanifoldWitness @(Interior a)
                             , semimanifoldWitness @(Interior b) ) of
    (SemimanifoldWitness, SemimanifoldWitness)
       -> SemimanifoldWitness

instance ∀ a b . ( ProjectableBoundary a, ProjectableBoundary b
                 , VectorSpace (Needle (Boundary a)), VectorSpace (Needle (Interior b))
                 , VectorSpace (Needle (Interior a)), VectorSpace (Needle (Boundary b))
                 , Scalar (Needle (Interior b)) ~ Scalar (Needle (Boundary a))
                 , Scalar (Needle (Interior a)) ~ Scalar (Needle (Boundary a))
                 , Scalar (Needle (Boundary b)) ~ Scalar (Needle (Boundary a))
                 , Num (Scalar (Needle (Boundary b)))
                 )
   => PseudoAffine (ProductBoundary a b) where
  (.-~.) = case ( pseudoAffineWitness @(Interior a)
                , pseudoAffineWitness @(Interior b) ) of
   (PseudoAffineWitness SemimanifoldWitness, PseudoAffineWitness SemimanifoldWitness)
    -> let BoundOfL bx y − BoundOfL bξ υ
             = case (bx.-~.bξ, fromInterior @b y.--.fromInterior υ) of
                 (Just δbx, Just δy) -> Just $ NBoundOfL δbx δy
                 (_, Nothing) -> Nothing
           BoundOfL bx y − BoundOfR ξ bυ
             = case ( fromBoundary @a bx.--.fromInterior ξ
                    , projectToBoundary (fromInterior @b y) bυ ) of
                 (Just δbx, Just (δby, dy))
                    -> Just $ NBoundOfR (δbx^*(1+dy)) δby 
                 _ -> Nothing
       in (−)
  pseudoAffineWitness = case ( pseudoAffineWitness @(Interior a)
                             , pseudoAffineWitness @(Interior b) ) of
    (PseudoAffineWitness SemimanifoldWitness
     , PseudoAffineWitness SemimanifoldWitness)
       -> undefined {- PseudoAffineWitness SemimanifoldWitness -}

data ProductHalfNeedle a b
  = ProductHalfNeedle !(Needle a) !(Needle b)

instance AdditiveMonoid (ProductHalfNeedle a b)
instance ( VectorSpace (Needle (Boundary a)), VectorSpace (Needle (Interior b))
         , VectorSpace (Needle (Interior a)), VectorSpace (Needle (Boundary b))
         , Scalar (Needle (Interior b)) ~ Scalar (Needle (Boundary a))
         , Scalar (Needle (Interior a)) ~ Scalar (Needle (Boundary a))
         , Scalar (Needle (Boundary b)) ~ Scalar (Needle (Boundary a))
         , Num (Scalar (Needle (Boundary b)))
         ) => HalfSpace (ProductHalfNeedle a b) where
  type FullSubspace (ProductHalfNeedle a b) = ProductBoundaryNeedle a b

instance ( ProjectableBoundary a, ProjectableBoundary b
         , VectorSpace (Needle (Boundary a)), VectorSpace (Needle (Interior b))
         , VectorSpace (Needle (Interior a)), VectorSpace (Needle (Boundary b))
         , Scalar (Needle (Interior b)) ~ Scalar (Needle (Boundary a))
         , Scalar (Needle (Interior a)) ~ Scalar (Needle (Boundary a))
         , Scalar (Needle (Boundary b)) ~ Scalar (Needle (Boundary a))
         , Num (Scalar (Needle (Boundary b)))
         ) => SemimanifoldWithBoundary (a,b) where
  type Interior (a,b) = (Interior a, Interior b)
  type Boundary (a,b) = ProductBoundary a b
  type HalfNeedle (a,b) = ProductHalfNeedle a b
  extendToBoundary = undefined
