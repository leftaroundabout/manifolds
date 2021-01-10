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
{-# LANGUAGE ConstraintKinds          #-}
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
import Math.LinearMap.Category (Tensor(..), TensorSpace(..), LinearSpace(..), Num')
import Math.VectorSpace.Dual
import Math.VectorSpace.MiscUtil.MultiConstraints (SameScalar)

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

instance (AdditiveMonoid a, AdditiveGroup b) => AdditiveMonoid (a,b) where
  zeroHV = (zeroHV, zeroV)
  addHVs (a,b) (α,β) = (addHVs a α, b^+^β)
instance (HalfSpace a, VectorSpace b, Scalar (FullSubspace a) ~ Scalar b)
            => HalfSpace (a,b) where
  type FullSubspace (a,b) = (FullSubspace a, b)

instance AdditiveMonoid ℝay where
  zeroHV = Cℝay 0 Origin
  addHVs (Cℝay a Origin) (Cℝay b Origin) = Cℝay (a+b) Origin
instance HalfSpace ℝay where
  type FullSubspace ℝay = ℝ⁰
  scaleNonNeg (Cℝay μ Origin) (Cℝay l Origin) = Cℝay (μ*l) Origin
  fromFullSubspace o = Cℝay 0 o
  projectToFullSubspace (Cℝay _ o) = o

type OpenManifold m nb = ( SemimanifoldWithBoundary m
                         , Interior m ~ m
                         , Boundary m ~ EmptyMfd nb
                         )

data SmfdWBoundWitness m where
  OpenManifoldWitness :: ∀ m nb . OpenManifold m nb
              => SmfdWBoundWitness m
  SmfdWBoundWitness :: ∀ m nb ne .
         ( OpenManifold (Interior m) nb, OpenManifold (Boundary m) ne
         , FullSubspace (HalfNeedle m) ~ Needle (Boundary m) )
              => SmfdWBoundWitness m

class ( Semimanifold (Interior m), Semimanifold (Boundary m), HalfSpace (HalfNeedle m)
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
  smfdWBoundWitness :: SmfdWBoundWitness m
  default smfdWBoundWitness 
              :: ( OpenManifold (Interior m) (Needle (Boundary m))
                 , OpenManifold (Boundary m) (Needle (Boundary (Boundary m)))
                 , FullSubspace (HalfNeedle m) ~ Needle (Boundary m) )
                   => SmfdWBoundWitness m
  smfdWBoundWitness = SmfdWBoundWitness @m
                           @(Needle (Boundary m)) @(Needle (Boundary (Boundary m)))

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

instance LinearSpace k => SemimanifoldWithBoundary (EmptyMfd k) where
  type Interior (EmptyMfd k) = EmptyMfd k
  type Boundary (EmptyMfd k) = EmptyMfd k
  type HalfNeedle (EmptyMfd k) = ZeroDim (Scalar k)
  smfdWBoundWitness = OpenManifoldWitness @(EmptyMfd k) @k

instance Num' k => SemimanifoldWithBoundary (ZeroDim k) where
  type Interior (ZeroDim k) = ZeroDim k
  type Boundary (ZeroDim k) = EmptyMfd (ZeroDim k)
  type HalfNeedle (ZeroDim k) = ZeroDim k
  fromInterior = id
  fromBoundary b = case b of {}
  separateInterior = Right
  p|+^_ = case p of {}
  Origin .+^| Origin = Right Origin
  extendToBoundary _ _ = Nothing
  smfdWBoundWitness = SmfdWBoundWitness

instance Num' k => PseudoAffineWithBoundary (ZeroDim k) where
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

data ProductBoundaryNeedleT (dn :: Dualness) a b v
  = ZeroProductBoundaryNeedle
  | NBoundOfL !(dn`Space`Needle (Boundary a)) !(dn`Space`Needle (Interior b)) !v
  | NBoundOfR !(dn`Space`Needle (Interior a)) !(dn`Space`Needle (Boundary b)) !v
type ProductBoundaryNeedle a b = ProductBoundaryNeedleT Vector a b
                                     (Scalar (Needle (Interior a)))

instance ( AdditiveGroup (dn`Space`Needle (Boundary a))
         , AdditiveGroup (dn`Space`Needle (Interior b))
         , AdditiveGroup (dn`Space`Needle (Interior a))
         , AdditiveGroup (dn`Space`Needle (Boundary b))
         , AdditiveGroup v
         , ValidDualness dn )
    => AffineSpace (ProductBoundaryNeedleT dn a b v) where
  type Diff (ProductBoundaryNeedleT dn a b v) = ProductBoundaryNeedleT dn a b v
  ZeroProductBoundaryNeedle .+^ n = n
  n .+^ ZeroProductBoundaryNeedle = n
  NBoundOfL x y v .+^ NBoundOfL ξ υ β = NBoundOfL (x^+^ξ) (y^+^υ) (v^+^β)
  NBoundOfR x y v .+^ NBoundOfR ξ υ β = NBoundOfR (x^+^ξ) (y^+^υ) (v^+^β)
  n .-. ZeroProductBoundaryNeedle = n
  NBoundOfL x y v .-. NBoundOfL ξ υ β = NBoundOfL (x^-^ξ) (y^-^υ) (v^-^β)
  NBoundOfR x y v .-. NBoundOfR ξ υ β = NBoundOfR (x^-^ξ) (y^-^υ) (v^-^β)

instance ( AdditiveGroup (dn`Space`Needle (Boundary a))
         , AdditiveGroup (dn`Space`Needle (Interior b))
         , AdditiveGroup (dn`Space`Needle (Interior a))
         , AdditiveGroup (dn`Space`Needle (Boundary b))
         , AdditiveGroup v
         , ValidDualness dn )
    => AdditiveGroup (ProductBoundaryNeedleT dn a b v) where
  zeroV = ZeroProductBoundaryNeedle
  (^+^) = (.+^)
  negateV ZeroProductBoundaryNeedle = ZeroProductBoundaryNeedle
  negateV (NBoundOfL x y v) = NBoundOfL (negateV x) (negateV y) (negateV v)
  negateV (NBoundOfR x y v) = NBoundOfR (negateV x) (negateV y) (negateV v)

instance ( SameScalar VectorSpace
           '[ v
            , dn`Space`Needle (Boundary a), dn`Space`Needle (Interior b)
            , dn`Space`Needle (Interior a), dn`Space`Needle (Boundary b) ]
         , ValidDualness dn )
    => VectorSpace (ProductBoundaryNeedleT dn a b v) where
  type Scalar (ProductBoundaryNeedleT dn a b v) = Scalar v
  _ *^ ZeroProductBoundaryNeedle = ZeroProductBoundaryNeedle
  μ *^ NBoundOfL x y v = NBoundOfL (μ*^x) (μ*^y) (μ*^v)
  μ *^ NBoundOfR x y v = NBoundOfR (μ*^x) (μ*^y) (μ*^v)

instance ( SameScalar LinearSpace
           '[ v
            , dn`Space`Needle (Boundary a), dn`Space`Needle (Interior b)
            , dn`Space`Needle (Interior a), dn`Space`Needle (Boundary b) ]
         , ValidDualness dn )
    => TensorSpace (ProductBoundaryNeedleT dn a b v) where
  type TensorProduct (ProductBoundaryNeedleT dn a b v) w
          = ProductBoundaryNeedleT dn a b (v⊗w)
  wellDefinedVector ZeroProductBoundaryNeedle = Just ZeroProductBoundaryNeedle
  wellDefinedTensor t@(Tensor ZeroProductBoundaryNeedle) = Just t
  
instance ( SameScalar LinearSpace
            '[ v
             , dn`Space`Needle (Boundary a), dn`Space`Needle (Interior b)
             , dn`Space`Needle (Interior a), dn`Space`Needle (Boundary b) ]
         , ValidDualness dn
         )
    => LinearSpace (ProductBoundaryNeedleT dn a b v) where
  type DualVector (ProductBoundaryNeedleT dn a b v)
         = ProductBoundaryNeedleT (Dual dn) a b (DualVector v)
  

instance ( SameScalar LinearSpace
            '[ v
             , dn`Space`Needle (Boundary a), dn`Space`Needle (Interior b)
             , dn`Space`Needle (Interior a), dn`Space`Needle (Boundary b) ]
         , ValidDualness dn
         )
    => Semimanifold (ProductBoundaryNeedleT dn a b v) where
  type Needle (ProductBoundaryNeedleT dn a b v) = ProductBoundaryNeedleT dn a b v
  (.+~^) = (^+^)
  semimanifoldWitness = SemimanifoldWitness
  
instance ( SameScalar LinearSpace
            '[ v
             , dn`Space`Needle (Boundary a), dn`Space`Needle (Interior b)
             , dn`Space`Needle (Interior a), dn`Space`Needle (Boundary b) ]
         , ValidDualness dn
         )
    => PseudoAffine (ProductBoundaryNeedleT dn a b v) where
  

instance ∀ a b . ( ProjectableBoundary a, ProjectableBoundary b
                 , SameScalar LinearSpace
                    '[ Needle (Boundary a), Needle (Interior b)
                     , Needle (Interior a), Needle (Boundary b) ]
                 , Num' (Scalar (Needle (Interior a)))
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
       -> undefined -- SemimanifoldWitness

instance ∀ a b . ( ProjectableBoundary a, ProjectableBoundary b
                 , SameScalar LinearSpace
                    '[ Needle (Boundary a), Needle (Interior b)
                     , Needle (Interior a), Needle (Boundary b) ]
                 , Num' (Scalar (Needle (Interior a)))
                 )
   => PseudoAffine (ProductBoundary a b) where
  (.-~.) = case ( pseudoAffineWitness @(Interior a)
                , pseudoAffineWitness @(Interior b) ) of
   (PseudoAffineWitness SemimanifoldWitness, PseudoAffineWitness SemimanifoldWitness)
    -> let BoundOfL bx y − BoundOfL bξ υ
             = case (bx.-~.bξ, fromInterior @b y.--.fromInterior υ) of
                 (Just δbx, Just δy) -> Just $ NBoundOfL δbx δy 1
                 (_, Nothing) -> Nothing
           BoundOfL bx y − BoundOfR ξ bυ
             = case ( fromBoundary @a bx.--.fromInterior ξ
                    , projectToBoundary (fromInterior @b y) bυ ) of
                 (Just δbx, Just (δby, dy))
                    -> Just $ NBoundOfR (δbx^*(1+dy)) δby 1
                 _ -> Nothing
       in (−)
  pseudoAffineWitness = case ( pseudoAffineWitness @(Interior a)
                             , pseudoAffineWitness @(Interior b) ) of
    (PseudoAffineWitness SemimanifoldWitness
     , PseudoAffineWitness SemimanifoldWitness)
       -> undefined {- PseudoAffineWitness SemimanifoldWitness -}

instance ∀ a b . ( ProjectableBoundary a, ProjectableBoundary b
                 , SameScalar LinearSpace
                    '[ Needle (Boundary a), Needle (Interior b)
                     , Needle (Interior a), Needle (Boundary b)
                     , FullSubspace (HalfNeedle a)
                     ]
                 , Num' (Scalar (Needle (Interior a)))
                 , Scalar (Scalar (Needle (Interior a))) ~ Scalar (Needle (Interior a))
                 )
   => SemimanifoldWithBoundary (ProductBoundary a b) where
  type Interior (ProductBoundary a b) = ProductBoundary a b
  type Boundary (ProductBoundary a b) = EmptyMfd (Needle (Boundary a), Needle (Boundary b))
  type HalfNeedle (ProductBoundary a b) = (HalfNeedle a, Needle (Boundary b))
  smfdWBoundWitness = OpenManifoldWitness

data ProductHalfNeedle a b
  = ProductHalfNeedle !(Needle a) !(Needle b)

instance AdditiveMonoid (ProductHalfNeedle a b)
instance ( SameScalar VectorSpace
            '[ Needle (Boundary a), Needle (Interior b)
             , Needle (Interior a), Needle (Boundary b) ]
         , Num' (Scalar (Needle (Interior a)))
         , Scalar (Scalar (Needle (Boundary a))) ~ Scalar (Needle (Boundary a))
         ) => HalfSpace (ProductHalfNeedle a b) where
  type FullSubspace (ProductHalfNeedle a b) = ProductBoundaryNeedle a b

data ProductInterior a b
  = ProductInterior !(Interior a) !(Interior b)

instance ∀ a b .
         (SemimanifoldWithBoundary a, SemimanifoldWithBoundary b)
         => Semimanifold (ProductInterior a b) where
  type Needle (ProductInterior a b) = (Needle (Interior a), Needle (Interior b))
  ProductInterior x y.+~^(δx,δy) = ProductInterior (x.+~^δx) (y.+~^δy)
  semimanifoldWitness = case (smfdWBoundWitness @a, smfdWBoundWitness @b) of
    (SmfdWBoundWitness, SmfdWBoundWitness)
      -> case (semimanifoldWitness @(Interior a), semimanifoldWitness @(Interior b)) of
          (SemimanifoldWitness, SemimanifoldWitness) -> SemimanifoldWitness
        
instance ∀ a b .
         ( Num' (Scalar (Needle (Interior a)))
         , Scalar (Needle (Interior a)) ~ Scalar (Scalar (Needle (Interior a))) -- ???
         , SemimanifoldWithBoundary a, SemimanifoldWithBoundary b
         , SameScalar LinearSpace
            '[ Needle (Interior a), Needle (Interior b)
             , Needle (Boundary a), Needle (Boundary b) ]
         ) => SemimanifoldWithBoundary (ProductInterior a b) where
  type Interior (ProductInterior a b) = ProductInterior a b
  type Boundary (ProductInterior a b) = EmptyMfd (ProductBoundaryNeedle a b)
  type HalfNeedle (ProductInterior a b) = ProductHalfNeedle a b

instance ∀ a b .
         ( ProjectableBoundary a, ProjectableBoundary b
         , VectorSpace (Needle (Boundary a)), VectorSpace (Needle (Interior b))
         , VectorSpace (Needle (Interior a)), VectorSpace (Needle (Boundary b))
         , SameScalar LinearSpace
            '[ Needle (Interior a), Needle (Interior b)
             , Needle (Boundary a), Needle (Boundary b) ]
         , Scalar (Needle (Interior a)) ~ Scalar (Scalar (Needle (Interior a))) -- ???
         , Num' (Scalar (Needle (Boundary b)))
         ) => SemimanifoldWithBoundary (a,b) where
  type Interior (a,b) = ProductInterior a b
  type Boundary (a,b) = ProductBoundary a b
  type HalfNeedle (a,b) = ProductHalfNeedle a b
  extendToBoundary = undefined
  smfdWBoundWitness = case (smfdWBoundWitness @a, smfdWBoundWitness @b) of
    -- (OpenManifoldWitness, OpenManifoldWitness) -> OpenManifoldWitness
    (SmfdWBoundWitness, SmfdWBoundWitness) -> SmfdWBoundWitness
