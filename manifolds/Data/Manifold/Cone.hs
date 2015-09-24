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


module Data.Manifold.Cone  where
    


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

import qualified Numeric.LinearAlgebra.HMatrix as HMat

import qualified Prelude
import qualified Control.Applicative as Hask

import Control.Category.Constrained.Prelude hiding ((^))
import Control.Arrow.Constrained
import Control.Monad.Constrained
import Data.Foldable.Constrained

import Data.Manifold.PseudoAffine
import Data.Embedding

type ConeNeedle m = (ℝ, Needle m)

class ( Semimanifold m, Semimanifold (CℝayInterior m)
      , Interior (CℝayInterior m) ~ CℝayInterior m )
           => ConeSemimfd m where
  {-# MINIMAL fromCℝayInterior, fromCD¹Interior
            , toCℝayInterior  , toCD¹Interior  , coneNeedle #-}
  type CℝayInterior m :: *
  
  fromCℝayInterior :: CℝayInterior m -> Cℝay m
  fromCD¹Interior :: CℝayInterior m -> CD¹ m
  toCℝayInterior :: Cℝay m -> Option (CℝayInterior m)
  toCD¹Interior :: CD¹ m -> Option (CℝayInterior m)
  
  coneNeedle :: Tagged m ( Isomorphism (->) (Needle (CℝayInterior m)) (ConeNeedle m) )
  
  cℝayTranslateP :: Tagged (Cℝay m)
        (CℝayInterior m -> ConeNeedle m -> CℝayInterior m)
  cℝayTranslateP = cpt
   where cpt :: ∀ m . ConeSemimfd m => Tagged (Cℝay m)
                   (CℝayInterior m -> ConeNeedle m -> CℝayInterior m)
         cpt = Tagged $ \ri cn -> ri .+~^ (cni $<-$ cn)
          where Tagged cni = coneNeedle :: Tagged m
                                 (Isomorphism (->) (Needle (CℝayInterior m)) (ConeNeedle m))
                Tagged trp = translateP :: Tagged (CℝayInterior m)
                                 (CℝayInterior m -> Needle (CℝayInterior m) -> CℝayInterior m)
  cD¹TranslateP :: Tagged (CD¹ m)
        (CℝayInterior m -> ConeNeedle m -> CℝayInterior m)
  cD¹TranslateP = cpt
   where cpt :: ∀ m . ConeSemimfd m => Tagged (CD¹ m)
                   (CℝayInterior m -> ConeNeedle m -> CℝayInterior m)
         cpt = Tagged $ \ri cn -> ri .+~^ (cni $<-$ cn)
          where Tagged cni = coneNeedle :: Tagged m
                                 (Isomorphism (->) (Needle (CℝayInterior m)) (ConeNeedle m))
                Tagged trp = translateP :: Tagged (CℝayInterior m)
                                 (CℝayInterior m -> Needle (CℝayInterior m) -> CℝayInterior m)



instance (ConeSemimfd m) => Semimanifold (Cℝay m) where
  type Needle (Cℝay m) = ConeNeedle m
  type Interior (Cℝay m) = CℝayInterior m
  fromInterior = fromCℝayInterior
  toInterior = toCℝayInterior
  translateP = cℝayTranslateP

instance (ConeSemimfd m) => Semimanifold (CD¹ m) where
  type Needle (CD¹ m) = ConeNeedle m
  type Interior (CD¹ m) = CℝayInterior m
  fromInterior = fromCD¹Interior
  toInterior = toCD¹Interior
  translateP = cD¹TranslateP


instance ConeSemimfd ℝ where
  type CℝayInterior ℝ = ℝ²
  coneNeedle = Tagged id
  fromCℝayInterior (q,b) = Cℝay (q'+b') (q'-b')
   where [q', b'] = bijectℝtoℝplus <$> [q,b]
  toCℝayInterior (Cℝay h x) = pure (q,b)
   where [q, b] = (bijectℝplustoℝ . (/2)) <$> [h+x, h-x]
  fromCD¹Interior (q,b) = CD¹ (bijectℝplustoIntv $ q'+b') (q'-b')
   where [q', b'] = bijectℝtoℝplus <$> [q,b]
  toCD¹Interior (CD¹ h x) = pure (q,b)
   where [q, b] = (bijectℝplustoℝ . (/2)) <$> [h+x, h-x]
         h' = bijectIntvtoℝplus h
  cℝayTranslateP = Tagged (^+^)

instance ConeSemimfd S⁰ where
  type CℝayInterior S⁰ = ℝ
  coneNeedle = Tagged isoAttachZeroDim
  fromCℝayInterior x | x>0        = Cℝay x PositiveHalfSphere
                     | otherwise  = Cℝay (-x) NegativeHalfSphere
  toCℝayInterior (Cℝay x PositiveHalfSphere) = return x
  toCℝayInterior (Cℝay x NegativeHalfSphere) = return $ -x
  fromCD¹Interior x | x>0        = CD¹ (bijectℝtoIntv x) PositiveHalfSphere
                    | otherwise  = CD¹ (-bijectℝtoIntv x) NegativeHalfSphere
  toCD¹Interior (CD¹ 1 _) = Hask.empty
  toCD¹Interior (CD¹ x PositiveHalfSphere) = return $ bijectIntvtoℝ x
  toCD¹Interior (CD¹ x NegativeHalfSphere) = return $ -bijectℝtoIntv x

-- instance ConeSemimfd S¹ where
--   type CℝayInterior S¹ = ℝ²
--   fromCℝayInterior (x,y) = Cℝay r (S¹ $ atan2 y x)
--    where r = sqrt (x^2 + y^2)
--   toCℝayInterior (Cℝay r (S¹ φ)) = return (r * cos φ, r * sin φ)
--   fromCD¹Interior x | x>0        = CD¹ (bijectℝtoIntv x) PositiveHalfSphere
--                     | otherwise  = CD¹ (-bijectℝtoIntv x) NegativeHalfSphere
--   toCD¹Interior (CD¹ 1 _) = Hask.empty
--   toCD¹Interior (CD¹ x PositiveHalfSphere) = return $ bijectIntvtoℝ x
--   toCD¹Interior (CD¹ x NegativeHalfSphere) = return $ -bijectℝtoIntv x

-- instance (ConeSemimfd a, ConeSemimfd b) => ConeSemimfd (a,b) where
--   type CℝayInterior (a,b) = (CℝayInterior 
--   fromCℝayInterior (q,b) = Cℝay (q'+b') (q'-b')
--    where [q', b'] = bijectℝtoℝplus <$> [q,b]
--   toCℝayInterior (Cℝay h x) = pure (q,b)
--    where [q, b] = (bijectℝplustoℝ . (/2)) <$> [h+x, h-x]
--   fromCD¹Interior (q,b) = CD¹ (bijectℝplustoIntv $ q'+b') (q'-b')
--    where [q', b'] = bijectℝtoℝplus <$> [q,b]
--   toCD¹Interior (CD¹ h x) = pure (q,b)
--    where [q, b] = (bijectℝplustoℝ . (/2)) <$> [h+x, h-x]
--          h' = bijectIntvtoℝplus h
--   cℝayTranslateP = Tagged (^+^)


bijectℝtoℝplus      , bijectℝplustoℝ
 , bijectIntvtoℝplus, bijectℝplustoIntv
 ,     bijectIntvtoℝ, bijectℝtoIntv
               :: ℝ -> ℝ

bijectℝplustoℝ x = x - 1/x
bijectℝtoℝplus y = y/2 + sqrt(y^2/4 + 1)

-- ]0, 1[ ↔ ℝ⁺
bijectℝplustoIntv y = 1 - recip (y+1)
bijectIntvtoℝplus x = recip(1-x) - 1

-- ]-1, 1[ ↔ ℝ  (Similar to 'tanh', but converges less quickly towards ±1.)
bijectℝtoIntv y | y>0        = -1/(2*y) + sqrt(1/(4*y^2) + 1)
                | y<0        = -1/(2*y) - sqrt(1/(4*y^2) + 1)
                | otherwise  = 0
                 -- 0 = x² + x/y - 1
                 -- x = -1/2y ± sqrt(1/4y² + 1)
bijectIntvtoℝ x = x / (1-x^2)

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




