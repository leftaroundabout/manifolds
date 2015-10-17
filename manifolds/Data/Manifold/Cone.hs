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
    


import Data.List
import qualified Data.Vector.Generic as Arr
import qualified Data.Vector
import Data.Maybe
import Data.Semigroup
import Data.Function (on)
import Data.Fixed

import Data.VectorSpace
import Data.LinearMap
import Data.LinearMap.HerMetric
import Data.MemoTrie (HasTrie(..))
import Data.AffineSpace
import Data.Basis
import Data.Complex hiding (magnitude)
import Data.Void
import Data.Tagged
import Data.Manifold.Types.Primitive

import Data.CoNat
import Data.VectorSpace.FiniteDimensional

import qualified Numeric.LinearAlgebra.HMatrix as HMat

import qualified Prelude
import qualified Control.Applicative as Hask

import Control.Category.Constrained.Prelude hiding ((^))
import Control.Arrow.Constrained
import Control.Monad.Constrained
import Data.Foldable.Constrained

import Data.Manifold.PseudoAffine
import Data.Embedding



type ConeVecArr m = FinVecArrRep Cℝay (CℝayInterior m) (Scalar (Needle m))
type ConeNeedle m = Needle (ConeVecArr m)
type SConn'dConeVecArr m = FinVecArrRep Cℝay (ℝ, Interior m) ℝ


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


instance ConeSemimfd ℝ where
  type CℝayInterior ℝ = ℝ²
  fromCℝayInterior (FinVecArrRep qb) = Cℝay (q'+b') (q'-b')
   where [q', b'] = HMat.toList $ HMat.cmap ((/2) . bijectℝtoℝplus) qb
  toCℝayInterior (Cℝay 0 _) = Hask.empty
  toCℝayInterior (Cℝay h x) = pure . FinVecArrRep 
                              . HMat.cmap bijectℝplustoℝ $ HMat.fromList [h+x, h-x]
  fromCD¹Interior (FinVecArrRep qb) = CD¹ (bijectℝplustoIntv $ q'+b') (q'-b')
   where [q', b'] = HMat.toList $ HMat.cmap ((/2) . bijectℝtoℝplus) qb
  toCD¹Interior (CD¹ h x) = pure . FinVecArrRep
                              . HMat.cmap bijectℝplustoℝ $ HMat.fromList [h'+x, h'-x]
   where h' = bijectIntvtoℝplus h

instance PseudoAffine (Cℝay ℝ) where p.-~.i = (.-~.i) =<< toInterior p
instance PseudoAffine (CD¹ ℝ) where p.-~.i = (.-~.i) =<< toInterior p

instance ConeSemimfd S⁰ where
  type CℝayInterior S⁰ = ℝ
  fromCℝayInterior xa | x>0        = Cℝay x PositiveHalfSphere
                      | otherwise  = Cℝay (-x) NegativeHalfSphere
   where x = getFinVecArrRep xa HMat.! 0
  toCℝayInterior (Cℝay x PositiveHalfSphere) = return . FinVecArrRep $ HMat.scalar x
  toCℝayInterior (Cℝay x NegativeHalfSphere) = return . FinVecArrRep . HMat.scalar $ -x
  fromCD¹Interior xa | x>0        = CD¹ (bijectℝtoIntv x) PositiveHalfSphere
                     | otherwise  = CD¹ (-bijectℝtoIntv x) NegativeHalfSphere
   where x = getFinVecArrRep xa HMat.! 0
  toCD¹Interior (CD¹ 1 _) = Hask.empty
  toCD¹Interior (CD¹ x PositiveHalfSphere)
        = return . FinVecArrRep . HMat.scalar $ bijectIntvtoℝ x
  toCD¹Interior (CD¹ x NegativeHalfSphere)
        = return . FinVecArrRep . HMat.scalar $ -bijectℝtoIntv x

instance PseudoAffine (Cℝay S⁰) where p.-~.i = (.-~.i) =<< toInterior p
instance PseudoAffine (CD¹ S⁰) where p.-~.i = (.-~.i) =<< toInterior p

instance ConeSemimfd S¹ where
  type CℝayInterior S¹ = ℝ²
  fromCℝayInterior (FinVecArrRep xy) = Cℝay r (S¹ $ atan2 y x)
   where r = HMat.norm_2 xy
         [x,y] = HMat.toList xy
  toCℝayInterior (Cℝay r (S¹ φ)) = return . FinVecArrRep
                    . HMat.scale r $ HMat.fromList [cos φ, sin φ]
  fromCD¹Interior (FinVecArrRep xy) = CD¹ (bijectℝtoIntv r) (S¹ $ atan2 y x)
   where r = HMat.norm_2 xy
         [x,y] = HMat.toList xy
  toCD¹Interior (CD¹ 1 _) = Hask.empty
  toCD¹Interior (CD¹ r (S¹ φ)) = return . FinVecArrRep
                    . HMat.scale r' $ HMat.fromList [cos φ, sin φ]
   where r' = bijectIntvtoℝ r

instance PseudoAffine (Cℝay S¹) where p.-~.i = (.-~.i) =<< toInterior p
instance PseudoAffine (CD¹ S¹) where
  p.-~.i = (.-~.i) =<< toInterior p
                                      


-- | Products of simply connected spaces.
instance ( PseudoAffine x, PseudoAffine y
         , WithField ℝ HilbertSpace (Interior x), WithField ℝ HilbertSpace (Interior y)
         , LinearManifold (FinVecArrRep Cℝay (ℝ, (Interior x, Interior y)) ℝ)
         ) => ConeSemimfd (x,y) where
  type CℝayInterior (x,y) = (ℝ, (Interior x, Interior y))
  fromCℝayInterior = simplyCncted_fromCℝayInterior
  toCℝayInterior = simplyCncted_toCℝayInterior

instance ( PseudoAffine x, PseudoAffine y
         , WithField ℝ HilbertSpace (Interior x), WithField ℝ HilbertSpace (Interior y)
         , LinearManifold (FinVecArrRep Cℝay (ℝ, (Interior x, Interior y)) ℝ)
         ) => PseudoAffine (Cℝay(x,y)) where
  p.-~.i = (.-~.i) =<< toInterior p
instance ( PseudoAffine x, PseudoAffine y
         , WithField ℝ HilbertSpace (Interior x), WithField ℝ HilbertSpace (Interior y)
         , LinearManifold (FinVecArrRep Cℝay (ℝ, (Interior x, Interior y)) ℝ)
         ) => PseudoAffine (CD¹(x,y)) where
  p.-~.i = (.-~.i) =<< toInterior p

  
instance ( WithField ℝ ConeSemimfd x, PseudoAffine (Cℝay x)
         , HilbertSpace (CℝayInterior x)
         , HilbertSpace (FinVecArrRep Cℝay (CℝayInterior x) ℝ)
         ) => ConeSemimfd (Cℝay x) where
  type CℝayInterior (Cℝay x) = (ℝ, ConeVecArr x)
  fromCℝayInterior = simplyCncted_fromCℝayInterior
  toCℝayInterior = simplyCncted_toCℝayInterior
  
instance ( WithField ℝ ConeSemimfd x, PseudoAffine (Cℝay x)
         , HilbertSpace (CℝayInterior x)
         , HilbertSpace (FinVecArrRep Cℝay (CℝayInterior x) ℝ)
         ) => PseudoAffine (Cℝay (Cℝay x)) where
  p.-~.i = (.-~.i) =<< toInterior p
instance ( WithField ℝ ConeSemimfd x, PseudoAffine (Cℝay x)
         , HilbertSpace (CℝayInterior x)
         , HilbertSpace (FinVecArrRep Cℝay (CℝayInterior x) ℝ)
         ) => PseudoAffine (CD¹ (Cℝay x)) where
  p.-~.i = (.-~.i) =<< toInterior p
  
simplyCncted_fromCℝayInterior :: (PseudoAffine x, WithField ℝ HilbertSpace (Interior x))
        => SConn'dConeVecArr x -> Cℝay x
simplyCncted_fromCℝayInterior (FinVecArrRep ri) = Cℝay h . fromInterior . fromPackedVector
                         $ subtract (h/n) `Arr.map` Arr.tail cmps
   where h = Arr.sum cmps
         cmps = bijectℝtoℝplus `HMat.cmap` ri
         n = fromIntegral $ Arr.length cmps
  
simplyCncted_toCℝayInterior :: (PseudoAffine x, WithField ℝ HilbertSpace (Interior x))
        => Cℝay x -> Option (SConn'dConeVecArr x)
simplyCncted_toCℝayInterior (Cℝay h v) | h/=0, Option (Just vi) <- toInterior v 
   = let cmps'' = asPackedVector vi
         cmps' = (+ h/n) `HMat.cmap` cmps''
         cmps = (h - Arr.sum cmps') `Arr.cons` cmps
         n = fromIntegral $ Arr.length cmps
     in return $ FinVecArrRep (bijectℝplustoℝ `Arr.map` cmps)
simplyCncted_toCℝayInterior (Cℝay _ _) = Hask.empty


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

-- instance (WithScalar ℝ PseudoAffine m) => Semimanifold (Cℝay m) where
--   type Needle (Cℝay m) = (Needle m, ℝ)
--   type Interior (Cℝay m) = (Interior m, ℝ)
-- 
--   fromInterior (im, d)
--      | d>38       = Cℝay m d  -- from 38 on, the +1 is numerically
--                               -- insignificant against the exponential.
--      | otherwise  = cℝay m (log $ exp d + 1)
--                -- note that (for the same reason we can shortcut above 38)
--                -- such negative arguments will actually yield the value zero.
--                -- This means we're actually reaching the “infinitely far”
--                -- rim rather quickly. This might be a problem, but normally
--                -- shouldn't really matter much.
--                -- It would perhaps be better to have homeomorphism that
--                -- approaches -1/x in the negative limit, but such a
--                -- function doesn't seem as easy to come by.
--    where m = fromInterior im
--   toInterior (Cℝay m q)
--      | q>38       = fmap (,q) im
--      | q>0        = fmap (, log $ exp d - 1) im
--      | otherwise  = Hask.empty
--    where im = toInterior m

stiefel1Project :: LinearManifold v =>
             DualSpace v       -- ^ Must be nonzero.
                 -> Stiefel1 v
stiefel1Project = Stiefel1

stiefel1Embed :: HilbertSpace v => Stiefel1 v -> v
stiefel1Embed (Stiefel1 n) = normalized n
  

class (PseudoAffine v, InnerSpace v, NaturallyEmbedded (UnitSphere v) (DualSpace v))
          => HasUnitSphere v where
  type UnitSphere v :: *
  stiefel :: UnitSphere v -> Stiefel1 v
  stiefel = Stiefel1 . embed
  unstiefel :: Stiefel1 v -> UnitSphere v
  unstiefel = coEmbed . getStiefel1N

instance HasUnitSphere ℝ  where type UnitSphere ℝ  = S⁰
instance HasUnitSphere (FinVecArrRep t ℝ ℝ) where type UnitSphere (FinVecArrRep t ℝ ℝ)   = S⁰

instance HasUnitSphere ℝ² where type UnitSphere ℝ² = S¹
instance HasUnitSphere (FinVecArrRep t ℝ² ℝ) where type UnitSphere (FinVecArrRep t ℝ² ℝ) = S¹

instance HasUnitSphere ℝ³ where type UnitSphere ℝ³ = S²
instance HasUnitSphere (FinVecArrRep t ℝ³ ℝ) where type UnitSphere (FinVecArrRep t ℝ³ ℝ) = S²

-- instance (HasUnitSphere v, v ~ DualSpace v) => NaturallyEmbedded (Stiefel1 v) v where
--   embed = embed . unstiefel
--   coEmbed = stiefel . coEmbed




