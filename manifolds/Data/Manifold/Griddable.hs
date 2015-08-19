-- |
-- Module      : Data.Manifold.Griddable
-- Copyright   : (c) Justus Sagemüller 2015
-- License     : GPL v3
-- 
-- Maintainer  : (@) sagemueller $ geo.uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE ParallelListComp           #-}
{-# LANGUAGE UnicodeSyntax              #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE PatternGuards              #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE LiberalTypeSynonyms        #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE DataKinds                  #-}


module Data.Manifold.Griddable (GridAxis(..), Griddable(..)) where


import Data.List hiding (filter, all, elem, sum)
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Vector as Arr
import Data.List.NonEmpty (NonEmpty(..))
import Data.List.FastNub
import qualified Data.List.NonEmpty as NE
import Data.Semigroup

import Data.VectorSpace
import Data.LinearMap
import Data.LinearMap.HerMetric
import Data.LinearMap.Category
import Data.AffineSpace
import Data.Basis
import Data.Complex hiding (magnitude)
import Data.Void
import Data.Tagged
import Data.Proxy

import Data.SimplicialComplex
import Data.Manifold.Types
import Data.Manifold.Types.Primitive ((^), (^.))
import Data.Manifold.PseudoAffine
import Data.Manifold.TreeCover (Shade(..), fullShade, shadeCtr, shadeExpanse)
    
import Data.Embedding
import Data.CoNat

import qualified Prelude as Hask hiding(foldl, sum, sequence)
import qualified Control.Applicative as Hask
import qualified Control.Monad       as Hask hiding(forM_, sequence)
import Data.Functor.Identity
import Control.Monad.Trans.State
import Control.Monad.Trans.Writer
import Control.Monad.Trans.Class
import qualified Data.Foldable       as Hask
import Data.Foldable (all, elem, toList, sum)
import qualified Data.Traversable as Hask
import Data.Traversable (forM)

import qualified Numeric.LinearAlgebra.HMatrix as HMat

import Control.Category.Constrained.Prelude hiding
     ((^), all, elem, sum, forM, Foldable(..), Traversable)
import Control.Arrow.Constrained
import Control.Monad.Constrained hiding (forM)
import Data.Foldable.Constrained

import Text.Printf
import GHC.Generics (Generic)


data GridAxis m g = GridAxInterval (Shade m)
                  | GridAxCons (Shade m) g (GridAxis m g)
                  | GridAxisClosed g (GridAxis m g)
             deriving (Hask.Functor)

gshmap :: (Shade m -> Shade n) -> GridAxis m g -> GridAxis n g
gshmap f (GridAxInterval i) = GridAxInterval $ f i
gshmap f (GridAxCons i g ax) = GridAxCons (f i) g $ gshmap f ax
gshmap f (GridAxisClosed g ax) = GridAxisClosed g $ gshmap f ax

axisEnumFromStepTo :: (ℝ->a) -> ℝ -> ℝ -> ℝ -> GridAxis ℝ a
axisEnumFromStepTo f l st r
    | l' > r   = GridAxInterval $ intvl2Shade (Interval l l')
    | otherwise  = GridAxCons (intvl2Shade $ Interval l l')
                              (f l') $ axisEnumFromStepTo f l' st r
 where l' = l+st

axisGrLength :: GridAxis m a -> Int
axisGrLength (GridAxInterval _) = 0
axisGrLength (GridAxCons _ _ ax) = 1 + axisGrLength ax
axisGrLength (GridAxisClosed _ ax) = axisGrLength ax

class (WithField ℝ Manifold m) => Griddable m g where
  data GriddingParameters m g :: *
  mkGridding :: GriddingParameters m g -> Int -> Shade m -> [GridAxis m g]


instance Griddable ℝ String where
  data GriddingParameters ℝ String = ℝGridParam
  mkGridding ℝGridParam n (Shade c expa') = [ax]
   where l = c - expa
         r = c + expa
         
         expa = metric'AsLength expa'
         
         (Just ax) = find ((>=n) . axisGrLength)
                $ [ let qe = 10^^lqe' * nb
                    in axisEnumFromStepTo (prettyFloatShow lqe')
                         ( qe * fromIntegral (floor $ l / qe) ) qe r
                  | lqe' <- [lqe - 1, lqe - 2 ..], nb <- [5, 2, 1] ]
         
         lqe = lqef expa :: Int
         lqef n | n > 0      = floor $ lg   n
                | n < 0      = floor $ lg (-n)


instance (Griddable m a, Griddable n a) => Griddable (m,n) a where
  data GriddingParameters (m,n) a = PairGriddingParameters {
               fstGriddingParams :: GriddingParameters m a
             , sndGriddingParams :: GriddingParameters n a }
  mkGridding (PairGriddingParameters p₁ p₂) n (Shade (c₁,c₂) e₁e₂)
          = gshmap ( uncurry fullShade . (                  (,c₂).(^.shadeCtr)
                                         &&& (`productMetric'`e₂).(^.shadeExpanse)) )
              <$> g₁s
         ++ gshmap ( uncurry fullShade . (                  (c₁,).(^.shadeCtr)
                                         &&& ( productMetric' e₁).(^.shadeExpanse)) )
              <$> g₂s
   where g₁s = mkGridding p₁ n $ fullShade c₁ e₁
         g₂s = mkGridding p₂ n $ fullShade c₂ e₂
         (e₁,e₂) = factoriseMetric' e₁e₂ 

prettyFloatShow :: Int -> Double -> String
prettyFloatShow _ 0 = "0"
prettyFloatShow preci x
    | preci >= 0, preci < 4  = show $ round x
    | preci < 0, preci > -2  = printf "%.1f" x
    | otherwise   = case ceiling (0.01 + lg (abs x/10^^(preci+1))) + preci of
                        0    | preci < 0  -> printf ("%."++show(-preci)++"f") x
                        expn | expn>preci -> printf ("%."++show(expn-preci)++"f*10^%i")
                                                      (x/10^^expn)                 expn
                             | otherwise  -> printf ("%i*10^%i")
                                                      (round $ x/10^^expn :: Int)  expn



data Interval = Interval { ivLBound, ivRBound :: ℝ }

shade2Intvl :: Shade ℝ -> Interval
shade2Intvl sh = Interval l r
 where c = sh ^. shadeCtr
       expa = metric'AsLength $ sh ^. shadeExpanse
       l = c - expa; r = c + expa

intvl2Shade :: Interval -> Shade ℝ
intvl2Shade (Interval l r) = fullShade c (projector' expa)
 where c = (l+r) / 2
       expa = (r-l) / 2
       

lg :: Floating a => a -> a
lg = logBase 10

