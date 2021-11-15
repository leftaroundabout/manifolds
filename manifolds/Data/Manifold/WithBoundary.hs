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
{-# LANGUAGE CPP                      #-}


module Data.Manifold.WithBoundary where

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
                               , Num'
                               )
import Math.VectorSpace.Dual
import Math.VectorSpace.MiscUtil.MultiConstraints (SameScalar)
import Linear (V0, V1, V2, V3, V4)

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
instance (HalfSpace a, VectorSpace b, Scalar (FullSubspace a) ~ ℝ, Scalar b ~ ℝ)
            => HalfSpace (a,b) where
  type FullSubspace (a,b) = (FullSubspace a, b)
  scaleNonNeg s@(Cℝay μ Origin) (v,w) = (scaleNonNeg s v, μ*^w)
  fromFullSubspace (v,w) = (fromFullSubspace v, w)
  projectToFullSubspace (v',w) = (projectToFullSubspace v', w)

instance AdditiveMonoid ℝay where
  zeroHV = Cℝay 0 Origin
  addHVs (Cℝay a Origin) (Cℝay b Origin) = Cℝay (a+b) Origin
instance HalfSpace ℝay where
  type FullSubspace ℝay = ℝ⁰
  scaleNonNeg (Cℝay μ Origin) (Cℝay l Origin) = Cℝay (μ*l) Origin
  fromFullSubspace o = Cℝay 0 o
  projectToFullSubspace (Cℝay _ o) = o



#define VectorSpaceSansBoundary(v, s)                    \
instance Num (s) => SemimanifoldWithBoundary (v) where {  \
  type Interior (v) = v;                                 \
  type Boundary (v) = EmptyMfd ℝ⁰;                        \
  type HalfNeedle (v) = ℝay;                             \
  smfdWBoundWitness = OpenManifoldWitness;                \
  fromInterior = id;                                     \
  fromBoundary b = case b of {};                          \
  separateInterior = Right;                              \
  p|+^_ = case p of {};                                   \
  a.+^|b = Right $ a^+^b;                                \
  extendToBoundary _ _ = Nothing };                       \
instance Num (s) => PseudoAffineWithBoundary (v) where { \
  _!-|p = case p of {};                                   \
  (.--!) = (-) };                                        \
instance Num (s) => ProjectableBoundary (v) where {       \
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
  (.-~!) = (^-^)
  

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
                 , Scalar (Needle (Interior a)) ~ ℝ
                 )
   => SemimanifoldWithBoundary (ProductBoundary a b) where
  type Interior (ProductBoundary a b) = ProductBoundary a b
  type Boundary (ProductBoundary a b) = EmptyMfd (Needle (Boundary a), Needle (Boundary b))
  type HalfNeedle (ProductBoundary a b) = (HalfNeedle a, Needle (Boundary b))
  q|+^_ = case q of {}
  p.+^|q = Right $ p.+~^q
  fromInterior = id
  fromBoundary q = case q of {}
  smfdWBoundWitness = OpenManifoldWitness

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
instance ( SameScalar VectorSpace
            '[ Needle (Boundary a), Needle (Interior b)
             , Needle (Interior a), Needle (Boundary b) ]
         , Scalar (Needle (Boundary a)) ~ ℝ
         ) => HalfSpace (ProductHalfNeedle a b) where
  type FullSubspace (ProductHalfNeedle a b) = ProductBoundaryNeedle a b
  scaleNonNeg (Cℝay μ Origin) (ProductHalfNeedle v w)
         = ProductHalfNeedle (μ*^v) (μ*^w)
  fromFullSubspace ZeroProductBoundaryNeedle = zeroHV
  -- projectToFullSubspace = undefined

instance ∀ a b .
         ( ProjectableBoundary a, ProjectableBoundary b
         , VectorSpace (Needle (Boundary a)), VectorSpace (Needle (Interior b))
         , VectorSpace (Needle (Interior a)), VectorSpace (Needle (Boundary b))
         , SameScalar LinearSpace
            '[ Needle (Interior a), Needle (Interior b)
             , Needle (Boundary a), Needle (Boundary b)
             , Needle (Boundary (Interior a)), Needle (Boundary (Interior b)) -- ??
             ]
         , ProjectableBoundary (Interior a), ProjectableBoundary (Interior b)
         , Scalar (Needle (Boundary b)) ~ ℝ
         ) => SemimanifoldWithBoundary (a,b) where
  type Interior (a,b) = (Interior a, Interior b)
  type Boundary (a,b) = ProductBoundary a b
  type HalfNeedle (a,b) = ProductHalfNeedle a b
  extendToBoundary = undefined
  smfdWBoundWitness = case (smfdWBoundWitness @a, smfdWBoundWitness @b) of
    (OpenManifoldWitness, OpenManifoldWitness) -> OpenManifoldWitness
    (SmfdWBoundWitness, SmfdWBoundWitness) -> SmfdWBoundWitness

instance SemimanifoldWithBoundary S⁰ where
  type Interior S⁰ = S⁰
  type Boundary S⁰ = EmptyMfd ℝ⁰
  type HalfNeedle S⁰ = ℝ⁰
  fromInterior = id
  fromBoundary b = case b of {}
  separateInterior = Right
  p|+^_ = case p of {}
  NegativeHalfSphere .+^| Origin = Right NegativeHalfSphere
  PositiveHalfSphere .+^| Origin = Right PositiveHalfSphere
  extendToBoundary _ _ = Nothing
  smfdWBoundWitness = OpenManifoldWitness

instance SemimanifoldWithBoundary S¹ where
  type Interior S¹ = S¹
  type Boundary S¹ = EmptyMfd ℝ
  type HalfNeedle S¹ = ℝay
  fromInterior = id
  fromBoundary b = case b of {}
  separateInterior = Right
  p|+^_ = case p of {}
  _ .+^| p = case p of {}
  extendToBoundary _ _ = Nothing
  smfdWBoundWitness = OpenManifoldWitness

instance SemimanifoldWithBoundary D¹ where
  type Interior D¹ = ℝ
  type Boundary D¹ = S⁰
  type HalfNeedle D¹ = ℝay
  fromBoundary NegativeHalfSphere = D¹ (-1)
  fromBoundary PositiveHalfSphere = D¹ 1
  fromInterior = D¹ . tanh
  separateInterior (D¹ (-1)) = Left NegativeHalfSphere
  separateInterior (D¹ 1) = Left PositiveHalfSphere
  separateInterior (D¹ x) = Right $ atanh x
  NegativeHalfSphere|+^Cℝay l Origin = D¹ $ 1 - 4/(l+2)
  PositiveHalfSphere|+^Cℝay l Origin = D¹ $ 4/(l+2) - 1
  D¹ p .+^| l
    | p' >= 1    = Left (PositiveHalfSphere, (p'-1) / l)
    | p' <= -1   = Left (NegativeHalfSphere, (p'+1) / l)
    | otherwise  = Right $ atanh p'
   where p' = p+l
  extendToBoundary _ dir
   | dir > 0    = Just PositiveHalfSphere
   | dir < 0    = Just NegativeHalfSphere
   | otherwise  = Nothing
  smfdWBoundWitness = SmfdWBoundWitness

-- Old instances prior to the library's boundary paradigm change:
-- instance Semimanifold D¹ where
--   type Needle D¹ = ℝ
--   type Interior D¹ = ℝ
--   toInterior (D¹ x) | abs x < 1  = return $ atanh x
                    -- | otherwise  = empty
--   translateP = Tagged (+)
-- instance PseudoAffine D¹ where
--   D¹ 1 .-~. _ = empty
--   D¹ (-1) .-~. _ = empty
--   D¹ x .-~. D¹ y
--     | abs x < 1, abs y < 1  = return $ atanh x - atanh y
--     | otherwise             = empty

instance ( TensorSpace v, TensorSpace w
         , s ~ Scalar v, s ~ Scalar w
         , Num s
         ) => SemimanifoldWithBoundary (Tensor s v w) where
  type Interior (Tensor s v w) = (Tensor s v w)
  type Boundary (Tensor s v w) = EmptyMfd ℝ
  type HalfNeedle (Tensor s v w) = ℝay
  smfdWBoundWitness = OpenManifoldWitness
  fromInterior = id
  fromBoundary b = case b of {}
  separateInterior = Right
  p|+^_ = case p of {}
  a.+^|b = Right $ a^+^b
  extendToBoundary _ _ = Nothing

instance ( LinearSpace v, TensorSpace w
         , s ~ Scalar v, s ~ Scalar w
         , Num s
         ) => SemimanifoldWithBoundary (LinearMap s v w) where
  type Interior (LinearMap s v w) = (LinearMap s v w)
  type Boundary (LinearMap s v w) = EmptyMfd ℝ
  type HalfNeedle (LinearMap s v w) = ℝay
  smfdWBoundWitness = OpenManifoldWitness
  fromInterior = id
  fromBoundary b = case b of {}
  separateInterior = Right
  p|+^_ = case p of {}
  a.+^|b = Right $ a^+^b
  extendToBoundary _ _ = Nothing

instance ( LinearSpace v, TensorSpace w
         , s ~ Scalar v, s ~ Scalar w
         , Num s
         ) => SemimanifoldWithBoundary (LinearFunction s v w) where
  type Interior (LinearFunction s v w) = (LinearFunction s v w)
  type Boundary (LinearFunction s v w) = EmptyMfd ℝ
  type HalfNeedle (LinearFunction s v w) = ℝay
  smfdWBoundWitness = OpenManifoldWitness
  fromInterior = id
  fromBoundary b = case b of {}
  separateInterior = Right
  p|+^_ = case p of {}
  a.+^|b = Right $ a^+^b
  extendToBoundary _ _ = Nothing
