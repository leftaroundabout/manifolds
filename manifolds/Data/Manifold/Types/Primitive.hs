-- |
-- Module      : Data.Manifold.Types.Primitive
-- Copyright   : (c) Justus Sagemüller 2015
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsag $ hvl.no
-- Stability   : experimental
-- Portability : portable
-- 
-- Several low-dimensional manifolds, represented in some simple way as Haskell
-- data types. All these are in the 'PseudoAffine' class.
-- 
-- Also included in this module are some misc helper constraints etc., which don't really
-- belong here.


{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE UndecidableInstances     #-}
{-# LANGUAGE ExplicitNamespaces       #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE FunctionalDependencies   #-}
{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE RankNTypes               #-}
{-# LANGUAGE TupleSections            #-}
{-# LANGUAGE ConstraintKinds          #-}
{-# LANGUAGE PatternGuards            #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE ScopedTypeVariables      #-}
{-# LANGUAGE RecordWildCards          #-}
{-# LANGUAGE PatternSynonyms          #-}
{-# LANGUAGE LambdaCase               #-}


module Data.Manifold.Types.Primitive (
        -- * Index / ASCII names
          Real0, Real1, RealPlus, Real2, Real3
        , Sphere0, Sphere1, Sphere2
        , Projective0, Projective1, Projective2
        , Disk1, Disk2, Cone, OpenCone
        , FibreBundle(..), TangentBundle
        -- * Trivial manifolds
        , EmptyMfd(..), ZeroDim(..)
        -- * Linear manifolds
        , ℝ, ℝ⁰, ℝ¹, ℝ², ℝ³, ℝ⁴
        -- * Hyperspheres
        , S⁰, S⁰_(..), otherHalfSphere, S¹, S¹_(..), pattern S¹, S², S²_(..), pattern S²
        -- * Projective spaces
        , ℝP⁰, ℝP⁰_(..), ℝP¹, ℝP¹_(..), pattern ℝP¹,  ℝP²,  ℝP²_(..), pattern ℝP²
        -- * Intervals\/disks\/cones
        , D¹, D¹_(..), fromIntv0to1, D², D²_(..), pattern D²
        , ℝay, ℝay_
        , CD¹(..), Cℝay(..)
        -- * Tensor products
        , type (⊗)(..)
        -- * Utility (deprecated)
        , NaturallyEmbedded(..)
        , GraphWindowSpec(..), Endomorphism, (^), (^.), EqFloating
        , empty
   ) where


import Math.Manifold.Core.Types
import Math.Manifold.Core.PseudoAffine (FibreBundle(..), TangentBundle, Semimanifold(..))

import Data.VectorSpace
import Data.VectorSpace.Free
import Linear.V2
import Linear.V3
import Math.VectorSpace.ZeroDimensional
import Data.AffineSpace
import Data.Basis
import Data.Void
import Data.Monoid
import Data.Fixed (mod')
import Math.LinearMap.Category (type (⊗)())

import Control.Applicative (Const(..), Alternative(..))

import Control.Lens ((^.))

import Data.Binary

import qualified Prelude

import Control.Category.Constrained.Prelude hiding ((^))
import Control.Arrow.Constrained

import Data.Embedding

import qualified Test.QuickCheck as QC
import qualified Test.QuickCheck.Function as QC (Function (..), functionMap)
import qualified Text.Show.Pragmatic as SP




type EqFloating f = (Eq f, Ord f, Floating f)



data GraphWindowSpec = GraphWindowSpec {
    lBound, rBound, bBound, tBound :: Double
  , xResolution, yResolution :: Int
  }








class NaturallyEmbedded m v where
  embed :: m -> v
  coEmbed :: v -> m
  

instance (VectorSpace y) => NaturallyEmbedded x (x,y) where
  embed x = (x, zeroV)
  coEmbed (x,_) = x
instance (VectorSpace y, VectorSpace z) => NaturallyEmbedded x ((x,y),z) where
  embed x = (embed x, zeroV)
  coEmbed (x,_) = coEmbed x

instance NaturallyEmbedded ℝ⁰ ℝ⁰ where embed = id; coEmbed = id
instance NaturallyEmbedded ℝ  ℝ  where embed = id; coEmbed = id
instance NaturallyEmbedded ℝ² ℝ² where embed = id; coEmbed = id
instance NaturallyEmbedded ℝ³ ℝ³ where embed = id; coEmbed = id
instance NaturallyEmbedded ℝ⁴ ℝ⁴ where embed = id; coEmbed = id

instance NaturallyEmbedded S⁰ ℝ where
  embed PositiveHalfSphere = 1
  embed NegativeHalfSphere = -1
  coEmbed x | x>=0       = PositiveHalfSphere
            | otherwise  = NegativeHalfSphere
instance NaturallyEmbedded S¹ ℝ² where
  embed (S¹Polar φ) = V2 (cos φ) (sin φ)
  coEmbed (V2 x y) = S¹Polar $ atan2 y x
instance NaturallyEmbedded S² ℝ³ where
  embed (S²Polar ϑ φ) = V3 (cos φ * sϑ) (sin φ * sϑ) (cos ϑ)
   where sϑ = sin ϑ
  {-# INLINE embed #-}
  coEmbed (V3 x y z) = S²Polar (atan2 rxy z) (atan2 y x)
   where rxy = sqrt $ x^2 + y^2
  {-# INLINE coEmbed #-}
 
instance NaturallyEmbedded ℝP² ℝ³ where
  embed (HemisphereℝP²Polar θ φ) = V3 (cθ * cos φ) (cθ * sin φ) (sin θ)
   where cθ = cos θ
  coEmbed (V3 x y z) = HemisphereℝP²Polar (atan2 rxy z) (atan2 y x)
   where rxy = sqrt $ x^2 + y^2

instance NaturallyEmbedded D¹ ℝ where
  embed = xParamD¹
  coEmbed = D¹ . max (-1) . min 1

instance (Real s, NaturallyEmbedded x p, s ~ Scalar (Needle x))
            => NaturallyEmbedded (Cℝay x) (p, s) where
  embed (Cℝay h p) = (embed p, h)
  coEmbed (v,z) = Cℝay (max 0 z) (coEmbed v)



type Endomorphism a = a->a


type ℝ¹ = V1 ℝ
type ℝ² = V2 ℝ
type ℝ³ = V3 ℝ
type ℝ⁴ = V4 ℝ


-- | Better known as &#x211d;&#x207a; (which is not a legal Haskell name), the ray
--   of positive numbers (including zero, i.e. closed on one end).
type ℝay = Cℝay ℝ⁰

type ℝay_ r = Cℝay (ZeroDim r)




type Real0 = ℝ⁰
type Real1 = ℝ
type RealPlus = ℝay
type Real2 = ℝ²
type Real3 = ℝ³

type Sphere0 = S⁰
type Sphere1 = S¹
type Sphere2 = S²

type Projective0 = ℝP⁰
type Projective1 = ℝP¹
type Projective2 = ℝP²

type Disk1 = D¹
type Disk2 = D²

type Cone = CD¹ 
type OpenCone = Cℝay




infixr 8 ^

(^) :: Num a => a -> Int -> a
(^) = (Prelude.^)



instance QC.Arbitrary S⁰ where
  arbitrary = (\hsph -> if hsph then PositiveHalfSphere else NegativeHalfSphere)
               <$> QC.arbitrary
instance QC.CoArbitrary S⁰ where
  coarbitrary PositiveHalfSphere = QC.coarbitrary (2255841931547 :: Int)
  coarbitrary NegativeHalfSphere = QC.coarbitrary (1710032008738 :: Int)
instance QC.Function S⁰ where
  function = QC.functionMap (\case {PositiveHalfSphere->True; NegativeHalfSphere->False})
                            (\case {True->PositiveHalfSphere; False->NegativeHalfSphere})
instance SP.Show S⁰ where
  showsPrec = showsPrec

instance QC.Arbitrary S¹ where
  arbitrary = S¹Polar . (pi-) . (`mod'`(2*pi))
               <$> QC.arbitrary
  shrink (S¹Polar φ) = S¹Polar . (pi/12*) <$> QC.shrink (φ*12/pi)
instance QC.CoArbitrary S¹ where
  coarbitrary (S¹Polar φ) = QC.coarbitrary φ
instance QC.Function S¹ where
  function = QC.functionMap (\(S¹Polar φ) -> tan $ φ/2) (S¹Polar . (*2) . atan)
instance SP.Show S¹ where
  showsPrec p (S¹Polar φ) = showParen (p>9) $ ("S¹Polar "++) . SP.showsPrec 10 φ

instance QC.Arbitrary S² where
  arbitrary = ( \θ φ -> S²Polar (θ`mod'`pi) (pi - (φ`mod'`(2*pi))) )
               <$> QC.arbitrary<*>QC.arbitrary
  shrink (S²Polar θ φ) = uncurry S²Polar . (pi/12*^) <$> QC.shrink (θ*12/pi, φ*12/pi)
instance QC.CoArbitrary S² where
  coarbitrary (S²Polar 0 φ) = QC.coarbitrary (544317577041 :: Int)
  coarbitrary (S²Polar θ φ)
   | θ < pi                 = QC.coarbitrary (θ,φ)
   | otherwise              = QC.coarbitrary (1771964485166 :: Int)
instance QC.Function S² where
  function = QC.functionMap (\(S²Polar θ φ) -> (cos φ, sin φ)^*tan (θ/2))
                            (\(x,y) -> S²Polar (2 * (atan . sqrt $ x^2 + y^2)) (atan2 y x))
instance SP.Show S² where
  showsPrec p (S²Polar θ φ) = showParen (p>9) $ ("S²Polar "++)
                           . SP.showsPrec 10 θ . (' ':) . SP.showsPrec 10 φ

instance QC.Arbitrary ℝP⁰ where
  arbitrary = pure ℝPZero

instance QC.Arbitrary ℝP¹ where
  arbitrary = ( \θ -> HemisphereℝP¹Polar (pi/2 - (θ`mod'`pi)) ) <$> QC.arbitrary
  shrink (HemisphereℝP¹Polar θ) = HemisphereℝP¹Polar . (pi/6*) <$> QC.shrink (θ*6/pi)

instance QC.Arbitrary ℝP² where
  arbitrary = ( \θ φ -> HemisphereℝP²Polar (θ`mod'`pi/2) (pi - (φ`mod'`(2*pi))) )
               <$> QC.arbitrary<*>QC.arbitrary
  shrink (HemisphereℝP²Polar θ φ) = [ HemisphereℝP²Polar (θ'*pi/6) (φ'*pi/12)
                                    | θ' <- QC.shrink (θ*6/pi)
                                    , φ' <- QC.shrink (φ*12/pi) ]

instance QC.Arbitrary D¹ where
  arbitrary = D¹ . (\x -> (x`mod'`2) - 1) <$> QC.arbitrary
  shrink (D¹ p) = D¹ . (\x -> (x`mod'`2) - 1) <$> QC.shrink p
instance QC.Arbitrary D² where
  arbitrary = D²Polar . (\x -> x`mod'`1) <$> QC.arbitrary
               <*> (φParamS¹ <$> QC.arbitrary)
  shrink (D²Polar r φ) = D²Polar . (\x -> (x`mod'`2) - 1) <$> QC.shrink r
               <*> (φParamS¹ <$> QC.shrink (S¹Polar φ))

instance (SP.Show m, SP.Show f) => SP.Show (FibreBundle m f) where
  showsPrec p (FibreBundle m v) = showParen (p>9)
                $ ("FibreBundle "++) . SP.showsPrec 10 m
                            . (' ':) . SP.showsPrec 10 v
instance (QC.Arbitrary m, QC.Arbitrary f) => QC.Arbitrary (FibreBundle m f) where
  arbitrary = FibreBundle <$> QC.arbitrary <*> QC.arbitrary
  shrink (FibreBundle m v) = [ FibreBundle m' v'
                             | m' <- QC.shrink m
                             , v' <- QC.shrink v ]


instance Binary (ZeroDim a) where
  put Origin = return ()
  get = return Origin
instance Binary S⁰
instance Binary S¹
instance Binary S²
instance Binary ℝP⁰
instance Binary ℝP¹
instance Binary ℝP²
instance Binary D¹
instance Binary D²
instance (Binary y, Binary (Scalar (Needle y))) => Binary (CD¹ y)
instance (Binary y, Binary (Scalar (Needle y))) => Binary (Cℝay y)
