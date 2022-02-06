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
{-# LANGUAGE LambdaCase               #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE TypeInType               #-}
{-# LANGUAGE CPP                      #-}


module Data.Manifold.WithBoundary
        ( SemimanifoldWithBoundary(..), PseudoAffineWithBoundary(..)
        , SmfdWBoundWitness(..)
        , AdditiveMonoid(..), HalfSpace(..)
        ) where

import Data.Manifold.WithBoundary.Class

import Data.VectorSpace
import Data.AffineSpace
import Data.Basis

import Math.Manifold.Core.PseudoAffine
import Data.Manifold.PseudoAffine
import Math.Manifold.Core.Types
import Data.Manifold.Types.Primitive
import Math.Manifold.VectorSpace.ZeroDimensional
import Math.LinearMap.Category ( Tensor(..), TensorSpace(..)
                               , LinearMap(..), LinearFunction(..), LinearSpace(..)
                               , Num', closedScalarWitness, ClosedScalarWitness(..)
                               , DualSpaceWitness(..), ScalarSpaceWitness(..)
                               , LinearManifoldWitness(..)
                               )
import Math.VectorSpace.Dual
import Math.VectorSpace.MiscUtil.MultiConstraints (SameScalar)
import Linear (V0, V1, V2, V3, V4)
import qualified Linear.Affine as LinAff

import Control.Applicative
import Control.Arrow

import qualified GHC.Generics as Gnrx
import GHC.Generics (Generic, (:*:)(..))
import Data.Kind (Type)
import Proof.Propositional (Empty(..))

import Data.CallStack (HasCallStack)


instance (AdditiveMonoid a, AdditiveGroup b) => AdditiveMonoid (a,b) where
  zeroHV = (zeroHV, zeroV)
  addHVs (a,b) (α,β) = (addHVs a α, b^+^β)
instance ∀ a b . ( HalfSpace a, Ray a ~ ℝay_ (Scalar b), VectorSpace b
                 , RealFrac'' (Scalar b), Scalar (FullSubspace a) ~ Scalar b )
                    => HalfSpace (a,b) where
  type FullSubspace (a,b) = (FullSubspace a, b)
  type Ray (a,b) = ℝay_ (Scalar b)
  scaleNonNeg s@(Cℝay μ Origin) (v,w) = (scaleNonNeg s v, μ*^w)
  fromFullSubspace (v,w) = (fromFullSubspace v, w)
  projectToFullSubspace (v',w) = (projectToFullSubspace v', w)
  fullSubspaceIsVectorSpace q = fullSubspaceIsVectorSpace @a q

instance Num s => AdditiveMonoid (ℝay_ s) where
  zeroHV = Cℝay 0 Origin
  addHVs (Cℝay a Origin) (Cℝay b Origin) = Cℝay (a+b) Origin
instance Num s => HalfSpace (ℝay_ s) where
  type FullSubspace (ℝay_ s) = ZeroDim s
  type Ray (ℝay_ s) = ℝay_ s
  scaleNonNeg (Cℝay μ Origin) (Cℝay l Origin) = Cℝay (μ*l) Origin
  fromFullSubspace o = Cℝay 0 o
  projectToFullSubspace (Cℝay _ o) = o



#define VectorSpaceSansBoundary(v, s)                         \
instance (Num' (s), Eq (s), OpenManifold (s), ProjectableBoundary (s)) \
                   => SemimanifoldWithBoundary (v) where {      \
  type Interior (v) = v;                                 \
  type Boundary (v) = EmptyMfd (ZeroDim s);               \
  type HalfNeedle (v) = ℝay;                             \
  smfdWBoundWitness = OpenManifoldWitness;                \
  fromInterior = id;                                     \
  fromBoundary b = case b of {};                          \
  separateInterior = Right;                              \
  p|+^_ = case p of {};                                   \
  a.+^|b = Right $ a^+^b;                                \
  extendToBoundary _ _ = Nothing };                       \
instance (Num' (s), Eq (s), OpenManifold (s), ProjectableBoundary (s)) \
                  => PseudoAffineWithBoundary (v) where {\
  _!-|p = case p of {};                                   \
  (.--!) = (-) };                                        \
instance (Num' (s), Eq (s), OpenManifold (s), ProjectableBoundary (s)) \
                => ProjectableBoundary (v) where {              \
  projectToBoundary _ p = case p of {};                  \
  marginFromBoundary p = case p of {} }

VectorSpaceSansBoundary(ℝ,ℝ)
VectorSpaceSansBoundary(V0 s, s)
VectorSpaceSansBoundary(V1 s, s)
VectorSpaceSansBoundary(V2 s, s)
VectorSpaceSansBoundary(V3 s, s)
VectorSpaceSansBoundary(V4 s, s)

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

instance ∀ a b v dn .
         ( SemimanifoldWithBoundary a, SemimanifoldWithBoundary b
         , SameScalar VectorSpace
           '[ v, dn`Space`Needle (Interior a), dn`Space`Needle (Interior b) ]
         , AdditiveGroup (dn`Space`Needle (Boundary a))
         , AdditiveGroup (dn`Space`Needle (Boundary b))
         , ValidDualness dn )
    => VectorSpace (ProductBoundaryNeedleT dn a b v) where
  type Scalar (ProductBoundaryNeedleT dn a b v) = Scalar v
  (*^) = boundaryHasSameScalar @a (boundaryHasSameScalar @b (
            case (decideDualness @dn, smfdWBoundWitness @a, smfdWBoundWitness @b) of
     (VectorWitness, _, _) -> \μ -> \case
        ZeroProductBoundaryNeedle -> ZeroProductBoundaryNeedle
        NBoundOfL x y v -> NBoundOfL (μ*^x) (μ*^y) (μ*^v)
        NBoundOfR x y v -> NBoundOfR (μ*^x) (μ*^y) (μ*^v)
     (FunctionalWitness, SmfdWBoundWitness, SmfdWBoundWitness)
                       -> case ( dualSpaceWitness @(Needle (Interior a))
                               , dualSpaceWitness @(Needle (Boundary a))
                               , dualSpaceWitness @(Needle (Interior b))
                               , dualSpaceWitness @(Needle (Boundary b)) ) of
       (DualSpaceWitness, DualSpaceWitness, DualSpaceWitness, DualSpaceWitness)
            -> \μ -> \case
        ZeroProductBoundaryNeedle -> ZeroProductBoundaryNeedle
        NBoundOfL x y v -> NBoundOfL (μ*^x) (μ*^y) (μ*^v)
        NBoundOfR x y v -> NBoundOfR (μ*^x) (μ*^y) (μ*^v)
    ))

instance ( SemimanifoldWithBoundary a, SemimanifoldWithBoundary b
         , SameScalar LinearSpace
           '[ v, dn`Space`Needle (Interior a), dn`Space`Needle (Interior b) ]
         , AdditiveGroup (dn`Space`Needle (Boundary a))
         , AdditiveGroup (dn`Space`Needle (Boundary b))
         , ValidDualness dn )
    => TensorSpace (ProductBoundaryNeedleT dn a b v) where
  type TensorProduct (ProductBoundaryNeedleT dn a b v) w
          = ProductBoundaryNeedleT dn a b (v⊗w)
  wellDefinedVector ZeroProductBoundaryNeedle = Just ZeroProductBoundaryNeedle
  wellDefinedTensor t@(Tensor ZeroProductBoundaryNeedle) = Just t
  
instance ( SemimanifoldWithBoundary a, SemimanifoldWithBoundary b
         , SameScalar LinearSpace
            '[ v, dn`Space`Needle (Interior a), dn`Space`Needle (Interior b) ]
         , AdditiveGroup (dn`Space`Needle (Boundary a))
         , AdditiveGroup (dn`Space`Needle (Boundary b))
         , ValidDualness dn
         )
    => LinearSpace (ProductBoundaryNeedleT dn a b v) where
  type DualVector (ProductBoundaryNeedleT dn a b v)
         = ProductBoundaryNeedleT (Dual dn) a b (DualVector v)
  

instance ( SemimanifoldWithBoundary a, SemimanifoldWithBoundary b
         , SameScalar LinearSpace
            '[ v, dn`Space`Needle (Interior a), dn`Space`Needle (Interior b) ]
         , AdditiveGroup (dn`Space`Needle (Boundary a))
         , AdditiveGroup (dn`Space`Needle (Boundary b))
         , ValidDualness dn
         )
    => Semimanifold (ProductBoundaryNeedleT dn a b v) where
  type Needle (ProductBoundaryNeedleT dn a b v) = ProductBoundaryNeedleT dn a b v
  (.+~^) = (^+^)
  semimanifoldWitness = SemimanifoldWitness
  
instance ( SemimanifoldWithBoundary a, SemimanifoldWithBoundary b
         , SameScalar LinearSpace
            '[ v, dn`Space`Needle (Interior a), dn`Space`Needle (Interior b) ]
         , AdditiveGroup (dn`Space`Needle (Boundary a))
         , AdditiveGroup (dn`Space`Needle (Boundary b))
         , ValidDualness dn
         )
    => PseudoAffine (ProductBoundaryNeedleT dn a b v) where
  p.-~.q = pure (p^-^q)
  (.-~!) = (^-^)
  
instance ( SemimanifoldWithBoundary a, SemimanifoldWithBoundary b
         , SameScalar LinearSpace
            '[ v, dn`Space`Needle (Interior a), dn`Space`Needle (Interior b) ]
         , AdditiveGroup (dn`Space`Needle (Boundary a))
         , AdditiveGroup (dn`Space`Needle (Boundary b))
         , OpenManifold (Scalar v)
         , ValidDualness dn
         )
    => SemimanifoldWithBoundary (ProductBoundaryNeedleT dn a b v) where
  type Interior (ProductBoundaryNeedleT dn a b v) = ProductBoundaryNeedleT dn a b v
  type Boundary (ProductBoundaryNeedleT dn a b v) = EmptyMfd v
  type HalfNeedle (ProductBoundaryNeedleT dn a b v) = ℝay
  smfdWBoundWitness = OpenManifoldWitness

instance ∀ a b . ( ProjectableBoundary a, ProjectableBoundary b
                 , SameScalar LinearSpace
                    '[ Needle (Interior a), Needle (Interior b) ]
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
                    '[ Needle (Interior a), Needle (Interior b) ]
                 , Num' (Scalar (Needle (Interior a)))
                 )
   => PseudoAffine (ProductBoundary a b) where
  p.-~!q = case p.-~.q of
             Just v -> v
             Nothing -> error "No path found in product-space boundary."
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
                    '[ Needle (Interior a), Needle (Interior b)
                     , FullSubspace (HalfNeedle a)
                     ]
                 , RealFrac'' (Scalar (Needle (Interior a)))
                 )
   => SemimanifoldWithBoundary (ProductBoundary a b) where
  type Interior (ProductBoundary a b) = ProductBoundary a b
  type Boundary (ProductBoundary a b) = EmptyMfd (Needle (Boundary a), Needle (Boundary b))
  type HalfNeedle (ProductBoundary a b) = (HalfNeedle a, Needle (Boundary b))
  q|+^_ = case q of {}
  p.+^|q = Right $ p.+~^q
  fromInterior = id
  fromBoundary q = case q of {}
  smfdWBoundWitness = boundaryHasSameScalar @a
     (case closedScalarWitness @(Scalar (Needle (Interior a))) of
              ClosedScalarWitness -> OpenManifoldWitness)
  needleIsOpenMfd r = needleIsOpenMfd @a (needleIsOpenMfd @b
                        (case closedScalarWitness @(Scalar (Needle (Interior a))) of
                           ClosedScalarWitness -> r))
  extendToBoundary q = case q of {}
  scalarIsOpenMfd r = boundaryHasSameScalar @a
     (case closedScalarWitness @(Scalar (Needle (Interior a))) of
              ClosedScalarWitness -> r)
  boundaryHasSameScalar r = boundaryHasSameScalar @a (boundaryHasSameScalar @b
     (case closedScalarWitness @(Scalar (Needle (Interior a))) of
              ClosedScalarWitness -> r))

instance (Empty (Boundary a), Empty (Boundary b)) => Empty (ProductBoundary a b) where
  eliminate (BoundOfL ba _) = eliminate ba
  eliminate (BoundOfR _ bb) = eliminate bb

data ProductHalfNeedle a b
  = ProductHalfNeedle !(Needle (Interior a)) !(Needle (Interior b))

instance (AdditiveGroup (Needle (Interior a)), AdditiveGroup (Needle (Interior b)))
             => AdditiveMonoid (ProductHalfNeedle a b) where
  zeroHV = ProductHalfNeedle zeroV zeroV
  addHVs (ProductHalfNeedle v w) (ProductHalfNeedle ϋ ĥ)
            = ProductHalfNeedle (v^+^ϋ) (w^+^ĥ)
instance ( SemimanifoldWithBoundary a
         , SameScalar VectorSpace
            '[ Needle (Interior a), Needle (Interior b) ]
         , RealFrac'' (Scalar (Needle (Interior a)))
         ) => HalfSpace (ProductHalfNeedle a b) where
  type FullSubspace (ProductHalfNeedle a b) = ProductBoundaryNeedle a b
  type Ray (ProductHalfNeedle a b) = ℝay_ (Scalar (Needle (Interior a)))
  scaleNonNeg = case smfdWBoundWitness @a of
     SmfdWBoundWitness 
        -> boundaryHasSameScalar @a (\(Cℝay μ Origin) (ProductHalfNeedle v w)
         -> ProductHalfNeedle (μ*^v) (μ*^w))
  fromFullSubspace ZeroProductBoundaryNeedle = zeroHV
  fullSubspaceIsVectorSpace q = undefined
  -- projectToFullSubspace = undefined

instance ∀ a b .
         ( ProjectableBoundary a, ProjectableBoundary b
         , SameScalar LinearSpace
            '[ Needle (Interior a), Needle (Interior b)
             ]
         , RealFrac'' (Scalar (Needle (Interior a)))
         , ProjectableBoundary (Interior a), ProjectableBoundary (Interior b)
         ) => SemimanifoldWithBoundary (a,b) where
  type Interior (a,b) = (Interior a, Interior b)
  type Boundary (a,b) = ProductBoundary a b
  type HalfNeedle (a,b) = ProductHalfNeedle a b
  extendToBoundary = undefined
  smfdWBoundWitness = case (smfdWBoundWitness @a, smfdWBoundWitness @b) of
    (OpenManifoldWitness, OpenManifoldWitness)
        -> needleIsOpenMfd @a (needleIsOpenMfd @b (
             boundaryHasSameScalar @(Needle a) (boundaryHasSameScalar @(Needle b)
               (case (semimanifoldWitness @(Interior a), semimanifoldWitness @(Interior b))
                 of (SemimanifoldWitness, SemimanifoldWitness)
                        -> needleBoundaryIsTrivallyProjectible @a
                            (needleBoundaryIsTrivallyProjectible @b OpenManifoldWitness) )
            )))
    (SmfdWBoundWitness, SmfdWBoundWitness)
        -> boundaryHasSameScalar @a
            (boundaryHasSameScalar @b
              (needleIsOpenMfd @(Interior a)
                (needleIsOpenMfd @(Interior b)
                  (case ( semimanifoldWitness @(Interior a)
                        , semimanifoldWitness @(Interior b)
                        , closedScalarWitness @(Scalar (Needle (Interior a)))
                        )
                 of (SemimanifoldWitness, SemimanifoldWitness, ClosedScalarWitness)
                        -> needleBoundaryIsTrivallyProjectible @a
                            (needleBoundaryIsTrivallyProjectible @b
                              (boundaryHasSameScalar @(Needle (Interior a))
                                (boundaryHasSameScalar @(Needle (Interior b))
                                  SmfdWBoundWitness)))))))
  boundaryHasSameScalar q = undefined
  needleIsOpenMfd _ = undefined

instance ∀ a b .
         ( ProjectableBoundary a, ProjectableBoundary b
         , SameScalar LinearSpace
            '[ Needle (Interior a), Needle (Interior b)
             , Needle (Boundary a), Needle (Boundary b)
             ]
         , ProjectableBoundary (Interior a), ProjectableBoundary (Interior b)
         , RealFrac'' (Scalar (Needle (Interior a)))
         ) => PseudoAffineWithBoundary (a,b) where

instance ∀ a b .
         ( ProjectableBoundary a, ProjectableBoundary b
         , SameScalar LinearSpace
            '[ Needle (Interior a), Needle (Interior b)
             , Needle (Boundary a), Needle (Boundary b)
             ]
         , ProjectableBoundary (Interior a), ProjectableBoundary (Interior b)
         , RealFrac'' (Scalar (Needle (Interior a)))
         ) => ProjectableBoundary (a,b) where
  needleBoundaryIsTrivallyProjectible q
      = needleBoundaryIsTrivallyProjectible @a
         (needleBoundaryIsTrivallyProjectible @b
           (boundaryHasSameScalar @(Needle (Interior a))
             (boundaryHasSameScalar @(Needle (Interior b))
               (needleIsOpenMfd @a
                 (needleIsOpenMfd @b
                   (case (semimanifoldWitness @(Interior a), semimanifoldWitness @(Interior b))
                     of (SemimanifoldWitness, SemimanifoldWitness) -> q))))))

instance ∀ s . RealFloat'' s => SemimanifoldWithBoundary (S⁰_ s) where
  type Interior (S⁰_ s) = S⁰_ s
  type Boundary (S⁰_ s) = EmptyMfd (ZeroDim s)
  type HalfNeedle (S⁰_ s) = ZeroDim s
  fromInterior = id
  fromBoundary b = case b of {}
  separateInterior = Right
  p|+^_ = case p of {}
  NegativeHalfSphere .+^| Origin = Right NegativeHalfSphere
  PositiveHalfSphere .+^| Origin = Right PositiveHalfSphere
  extendToBoundary _ _ = Nothing
  smfdWBoundWitness = OpenManifoldWitness

instance ∀ s . RealFloat'' s => SemimanifoldWithBoundary (S¹_ s) where
  type Interior (S¹_ s) = (S¹_ s)
  type Boundary (S¹_ s) = EmptyMfd (ZeroDim s)
  type HalfNeedle (S¹_ s) = ℝay_ s
  fromInterior = id
  fromBoundary b = case b of {}
  separateInterior = Right
  p|+^_ = case p of {}
  _ .+^| p = case p of {}
  extendToBoundary _ _ = Nothing
  smfdWBoundWitness = case closedScalarWitness @s of ClosedScalarWitness -> OpenManifoldWitness
  scalarIsOpenMfd q = case closedScalarWitness @s of ClosedScalarWitness -> q
  boundaryHasSameScalar q = case closedScalarWitness @s of ClosedScalarWitness -> q

instance ∀ s . RealFloat'' s => PseudoAffineWithBoundary (S¹_ s) where
  _!-|p = case p of {}
  (.--!) = (.-~!)

instance ∀ s . RealFloat'' s => ProjectableBoundary (S¹_ s) where
  scalarBoundaryIsTrivallyProjectible q = case closedScalarWitness @s of
     ClosedScalarWitness -> q
  projectToBoundary _ p = case p of {}
  marginFromBoundary p = case p of {}

instance ∀ s . RealFloat'' s => SemimanifoldWithBoundary (S²_ s) where
  type Interior (S²_ s) = S²_ s
  type Boundary (S²_ s) = EmptyMfd s
  type HalfNeedle (S²_ s) = ℝay_ s
  fromInterior = id
  fromBoundary b = case b of {}
  separateInterior = Right
  p|+^_ = case p of {}
  _ .+^| p = case p of {}
  extendToBoundary _ _ = Nothing
  smfdWBoundWitness = case closedScalarWitness @s of ClosedScalarWitness -> OpenManifoldWitness
  scalarIsOpenMfd q = case closedScalarWitness @s of ClosedScalarWitness -> q
  boundaryHasSameScalar q = case closedScalarWitness @s of ClosedScalarWitness -> q

instance ∀ s . RealFloat'' s => PseudoAffineWithBoundary (S²_ s) where
  _!-|p = case p of {}
  (.--!) = (.-~!)

instance ∀ s . RealFloat'' s => ProjectableBoundary (S²_ s) where
  scalarBoundaryIsTrivallyProjectible q = case closedScalarWitness @s of
     ClosedScalarWitness -> q
  projectToBoundary _ p = case p of {}
  marginFromBoundary p = case p of {}


instance ∀ s . RealFloat'' s => SemimanifoldWithBoundary (D¹_ s) where
  type Interior (D¹_ s) = s
  type Boundary (D¹_ s) = (S⁰_ s)
  type HalfNeedle (D¹_ s) = ℝay_ s
  fromBoundary NegativeHalfSphere = D¹ (-1)
  fromBoundary PositiveHalfSphere = D¹ 1
  fromInterior = D¹ . tanh
  separateInterior (D¹ (-1)) = Left NegativeHalfSphere
  separateInterior (D¹ 1) = Left PositiveHalfSphere
  separateInterior (D¹ x) = Right $ atanh x
  NegativeHalfSphere|+^Cℝay l Origin = D¹ $ 1 - 4/(l+2)
  PositiveHalfSphere|+^Cℝay l Origin = D¹ $ 4/(l+2) - 1
  (.+^|) = case (linearManifoldWitness @s, closedScalarWitness @s) of
   (LinearManifoldWitness, ClosedScalarWitness) ->
    let addBD¹ (D¹ p) l
          | p' >= 1    = Left (PositiveHalfSphere, (p'-1) / l)
          | p' <= -1   = Left (NegativeHalfSphere, (p'+1) / l)
          | otherwise  = Right $ atanh p'
         where p' = p+l
    in addBD¹
  extendToBoundary = case (linearManifoldWitness @s, closedScalarWitness @s) of
   (LinearManifoldWitness, ClosedScalarWitness) ->
    let e2b _ dir
         | dir > 0    = Just PositiveHalfSphere
         | dir < 0    = Just NegativeHalfSphere
         | otherwise  = Nothing
    in e2b
  smfdWBoundWitness = case closedScalarWitness @s of ClosedScalarWitness -> SmfdWBoundWitness
  scalarIsOpenMfd q = case (closedScalarWitness @s, linearManifoldWitness @s) of
   (ClosedScalarWitness, LinearManifoldWitness) -> q
  boundaryHasSameScalar q = case (closedScalarWitness @s, linearManifoldWitness @s) of
   (ClosedScalarWitness, LinearManifoldWitness) -> q
  needleIsOpenMfd q = case (closedScalarWitness @s, linearManifoldWitness @s) of
   (ClosedScalarWitness, LinearManifoldWitness) -> q


instance ( Num' n, OpenManifold n, LinearManifold (a n)
         , Scalar (a n) ~ n, Needle (a n) ~ a n )
            => SemimanifoldWithBoundary (LinAff.Point a n) where
  type Boundary (LinAff.Point a n) = EmptyMfd (ZeroDim n)
  type Interior (LinAff.Point a n) = LinAff.Point a n
  type HalfNeedle (LinAff.Point a n) = ℝay
  smfdWBoundWitness = OpenManifoldWitness

instance ( LinearSpace v, LinearSpace w
         , s ~ Scalar v, s ~ Scalar w
         , Num' s, OpenManifold s
         ) => SemimanifoldWithBoundary (Tensor s v w) where
  type Interior (Tensor s v w) = (Tensor s v w)
  type Boundary (Tensor s v w) = EmptyMfd (ZeroDim s)
  type HalfNeedle (Tensor s v w) = ℝay_ s
  smfdWBoundWitness = OpenManifoldWitness
  fromInterior = id
  fromBoundary b = case b of {}
  separateInterior = Right
  p|+^_ = case p of {}
  a.+^|b = Right $ a^+^b
  extendToBoundary _ _ = Nothing

instance ( LinearSpace v, LinearSpace w
         , s ~ Scalar v, s ~ Scalar w
         , Num' s, OpenManifold s
         ) => PseudoAffineWithBoundary (Tensor s v w) where
  _!-|p = case p of {}
  (.--!) = (^-^)

instance ( LinearSpace v, LinearSpace w
         , s ~ Scalar v, s ~ Scalar w
         , Num' s, OpenManifold s
         ) => SemimanifoldWithBoundary (LinearMap s v w) where
  type Interior (LinearMap s v w) = (LinearMap s v w)
  type Boundary (LinearMap s v w) = EmptyMfd (ZeroDim s)
  type HalfNeedle (LinearMap s v w) = ℝay
  smfdWBoundWitness = OpenManifoldWitness
  fromInterior = id
  fromBoundary b = case b of {}
  separateInterior = Right
  p|+^_ = case p of {}
  a.+^|b = Right $ a^+^b
  extendToBoundary _ _ = Nothing

instance ( LinearSpace v, LinearSpace w
         , s ~ Scalar v, s ~ Scalar w
         , Num' s, OpenManifold s, ProjectableBoundary s
         ) => ProjectableBoundary (LinearMap s v w) where
  projectToBoundary _ p = case p of {}
  marginFromBoundary p = case p of {}

instance ( LinearSpace v, LinearSpace w
         , s ~ Scalar v, s ~ Scalar w
         , Num' s, OpenManifold s
         ) => PseudoAffineWithBoundary (LinearMap s v w) where
  _!-|p = case p of {}
  (.--!) = (^-^)

instance ( LinearSpace v, LinearSpace w
         , s ~ Scalar v, s ~ Scalar w
         , Num' s, OpenManifold s
         ) => SemimanifoldWithBoundary (LinearFunction s v w) where
  type Interior (LinearFunction s v w) = (LinearFunction s v w)
  type Boundary (LinearFunction s v w) = EmptyMfd (ZeroDim s)
  type HalfNeedle (LinearFunction s v w) = ℝay
  smfdWBoundWitness = OpenManifoldWitness
  fromInterior = id
  fromBoundary b = case b of {}
  separateInterior = Right
  p|+^_ = case p of {}
  a.+^|b = Right $ a^+^b
  extendToBoundary _ _ = Nothing

instance ( LinearSpace v, LinearSpace w
         , s ~ Scalar v, s ~ Scalar w
         , Num' s, OpenManifold s
         ) => PseudoAffineWithBoundary (LinearFunction s v w) where
  _!-|p = case p of {}
  (.--!) = (^-^)
