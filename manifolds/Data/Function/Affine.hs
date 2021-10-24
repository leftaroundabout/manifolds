-- |
-- Module      : Data.Function.Affine
-- Copyright   : (c) Justus Sagemüller 2015
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsag $ hvl.no
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
{-# LANGUAGE PatternSynonyms          #-}
{-# LANGUAGE ViewPatterns             #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE UnicodeSyntax            #-}
{-# LANGUAGE MultiWayIf               #-}
{-# LANGUAGE ScopedTypeVariables      #-}
{-# LANGUAGE RecordWildCards          #-}
{-# LANGUAGE CPP                      #-}


module Data.Function.Affine (
              Affine(..)
            , evalAffine
            , fromOffsetSlope
            -- * Misc
            , lensEmbedding, correspondingDirections
            ) where
    


import Data.Semigroup

import Data.MemoTrie
import Data.VectorSpace
import Data.AffineSpace
import Data.Tagged
import Data.Manifold.Types.Primitive
import Data.Manifold.PseudoAffine
import Data.Manifold.Atlas
import Data.Embedding

import qualified Prelude
import qualified Control.Applicative as Hask
import Data.Functor (($>))

import Control.Category.Constrained.Prelude hiding ((^))
import Control.Category.Constrained.Reified
import Control.Arrow.Constrained
import Control.Monad.Constrained
import Data.Foldable.Constrained

import Math.LinearMap.Category

import Control.Lens



data Affine s d c where
    Affine :: (ChartIndex d :->: (c, LinearMap s (Needle d) (Needle c)))
               -> Affine s d c

instance Category (Affine s) where
  type Object (Affine s) x = ( Manifold x
                             , Atlas x, LinearSpace (Needle x)
                             , Scalar (Needle x) ~ s, HasTrie (ChartIndex x) )
  id = Affine . trie $ chartReferencePoint >>> id &&& const id
  Affine f . Affine g = Affine . trie
      $ \ixa -> case untrie g ixa of
           (b, ða'b) -> case untrie f $ lookupAtlas b of
            (c, ðb'c) -> (c, ðb'c . ða'b)

instance ∀ s . Num' s => Cartesian (Affine s) where
  type UnitObject (Affine s) = ZeroDim s
  swap = Affine . trie $ chartReferencePoint >>> swap &&& const swap
  attachUnit = Affine . trie $ chartReferencePoint >>> \a -> ((a,Origin), attachUnit)
  detachUnit = Affine . trie $ chartReferencePoint
                 >>> \(a,Origin::ZeroDim s) -> (a, detachUnit)
  regroup = Affine . trie $ chartReferencePoint >>> regroup &&& const regroup
  regroup' = Affine . trie $ chartReferencePoint >>> regroup' &&& const regroup'

instance ∀ s . Num' s => Morphism (Affine s) where
  Affine f *** Affine g = Affine . trie
      $ \(ixα,ixβ) -> case (untrie f ixα, untrie g ixβ) of
            ((fα, ðα'f), (gβ,ðβ'g)) -> ((fα,gβ), ðα'f***ðβ'g)
  
instance ∀ s . Num' s => PreArrow (Affine s) where
  Affine f &&& Affine g = Affine . trie
      $ \ix -> case (untrie f ix, untrie g ix) of
            ((fα, ðα'f), (gβ,ðβ'g)) -> ((fα,gβ), ðα'f&&&ðβ'g)
  terminal = Affine . trie $ \_ -> (Origin, zeroV)
  fst = afst
   where afst :: ∀ x y . ( Atlas x, Atlas y
                         , LinearSpace (Needle x), LinearSpace (Needle y)
                         , Scalar (Needle x) ~ s, Scalar (Needle y) ~ s
                         , HasTrie (ChartIndex x), HasTrie (ChartIndex y) )
                   => Affine s (x,y) x
         afst = Affine . trie $ chartReferencePoint >>> \(x,_::y) -> (x, fst)
  snd = asnd
   where asnd :: ∀ x y . ( Atlas x, Atlas y
                         , LinearSpace (Needle x), LinearSpace (Needle y)
                         , Scalar (Needle x) ~ s, Scalar (Needle y) ~ s
                         , HasTrie (ChartIndex x), HasTrie (ChartIndex y) )
                   => Affine s (x,y) y
         asnd = Affine . trie $ chartReferencePoint >>> \(_::x,y) -> (y, snd)
  
instance ∀ s . Num' s => WellPointed (Affine s) where
  const x = Affine . trie $ const (x, zeroV)
  unit = Tagged Origin
  
instance EnhancedCat (->) (Affine s) where
  arr f = fst . evalAffine f
  
instance EnhancedCat (Affine s) (LinearMap s) where
  arr = alarr (linearManifoldWitness, linearManifoldWitness)
   where alarr :: ∀ x y . ( LinearSpace x, Atlas x, HasTrie (ChartIndex x)
                          , LinearSpace y
                          , Scalar x ~ s, Scalar y ~ s )
             => (LinearManifoldWitness x, LinearManifoldWitness y)
                  -> LinearMap s x y -> Affine s x y
         alarr (LinearManifoldWitness, LinearManifoldWitness) f
             = Affine . trie $ chartReferencePoint
                   >>> \x₀ -> let y₀ = f $ x₀
                              in (negateV y₀, f)

instance ( Atlas x, HasTrie (ChartIndex x), LinearSpace (Needle x), Scalar (Needle x) ~ s
         , Manifold y, Scalar (Needle y) ~ s )
              => Semimanifold (Affine s x y) where
  type Needle (Affine s x y) = Affine s x (Needle y)
  (.+~^) = case ( semimanifoldWitness :: SemimanifoldWitness y ) of
    (SemimanifoldWitness) -> \(Affine f) (Affine g)
      -> Affine . trie $ \ix -> case (untrie f ix, untrie g ix) of
          ((fx₀,f'), (gx₀,g')) -> (fx₀.+~^gx₀, f'^+^g')
  semimanifoldWitness = case semimanifoldWitness :: SemimanifoldWitness y of
    SemimanifoldWitness -> SemimanifoldWitness
instance ( Atlas x, HasTrie (ChartIndex x), LinearSpace (Needle x), Scalar (Needle x) ~ s
         , Manifold y, Scalar (Needle y) ~ s )
              => PseudoAffine (Affine s x y) where
  (.-~!) = case ( semimanifoldWitness :: SemimanifoldWitness y ) of
    (SemimanifoldWitness) -> \(Affine f) (Affine g)
      -> Affine . trie $ \ix -> case (untrie f ix, untrie g ix) of
          ((fx₀,f'), (gx₀,g')) -> (fx₀.-~!gx₀, f'^-^g')
  pseudoAffineWitness = case semimanifoldWitness :: SemimanifoldWitness y of
    SemimanifoldWitness -> PseudoAffineWitness (SemimanifoldWitness)
instance ( Atlas x, HasTrie (ChartIndex x), LinearSpace (Needle x), Scalar (Needle x) ~ s
         , Manifold y, Scalar (Needle y) ~ s )
              => AffineSpace (Affine s x y) where
  type Diff (Affine s x y) = Affine s x (Needle y)
  (.+^) = (.+~^); (.-.) = (.-~!)
instance ( Atlas x, HasTrie (ChartIndex x), LinearSpace (Needle x), Scalar (Needle x) ~ s
         , LinearSpace y, Scalar y ~ s, Num' s )
            => AdditiveGroup (Affine s x y) where
  zeroV = case linearManifoldWitness :: LinearManifoldWitness y of
       LinearManifoldWitness -> Affine . trie $ const (zeroV, zeroV)
  (^+^) = case ( linearManifoldWitness :: LinearManifoldWitness y
               , dualSpaceWitness :: DualSpaceWitness y ) of
      (LinearManifoldWitness, DualSpaceWitness) -> (.+~^)
  negateV = case linearManifoldWitness :: LinearManifoldWitness y of
       LinearManifoldWitness -> \(Affine f) -> Affine . trie $
             untrie f >>> negateV***negateV
instance ( Atlas x, HasTrie (ChartIndex x), LinearSpace (Needle x), Scalar (Needle x) ~ s
         , LinearSpace y, Scalar y ~ s, Num' s )
            => VectorSpace (Affine s x y) where
  type Scalar (Affine s x y) = s
  (*^) = case linearManifoldWitness :: LinearManifoldWitness y of
       LinearManifoldWitness -> \μ (Affine f) -> Affine . trie $
             untrie f >>> (μ*^)***(μ*^)

evalAffine :: ∀ s x y . ( Manifold x, Atlas x, HasTrie (ChartIndex x)
                        , Manifold y
                        , s ~ Scalar (Needle x), s ~ Scalar (Needle y) )
               => Affine s x y -> x -> (y, LinearMap s (Needle x) (Needle y))
evalAffine (Affine f) x = (fx₀.+~^(ðx'f $ v), ðx'f)
 where Just v = x .-~. chartReferencePoint chIx
       chIx = lookupAtlas x
       (fx₀, ðx'f) = untrie f chIx

fromOffsetSlope :: ∀ s x y . ( LinearSpace x, Atlas x, HasTrie (ChartIndex x)
                             , Manifold y
                             , s ~ Scalar x, s ~ Scalar (Needle y) )
               => y -> LinearMap s x (Needle y) -> Affine s x y
fromOffsetSlope = case ( linearManifoldWitness :: LinearManifoldWitness x ) of
   (LinearManifoldWitness)
       -> \y0 ðx'y -> Affine . trie $ chartReferencePoint
                    >>> \x₀ -> let δy = ðx'y $ x₀
                               in (y0.+~^δy, ðx'y)


instance EnhancedCat (Embedding (Affine s)) (Embedding (LinearMap s)) where
  arr (Embedding e p) = Embedding (arr e) (arr p)


lensEmbedding :: ∀ k s x c .
                 ( Num' s
                 , LinearSpace x, LinearSpace c, Object k x, Object k c
                 , Scalar x ~ s, Scalar c ~ s
                 , EnhancedCat k (LinearMap s) )
                  => Lens' x c -> Embedding k c x
lensEmbedding l = Embedding (arr $ (arr $ LinearFunction (\c -> zeroV & l .~ c)
                                     :: LinearMap s c x) )
                            (arr $ (arr $ LinearFunction (^.l)
                                     :: LinearMap s x c) )


correspondingDirections :: ∀ s x c t
                        . ( WithField s AffineManifold c
                          , WithField s AffineManifold x
                          , SemiInner (Needle c), SemiInner (Needle x)
                          , RealFrac' s
                          , Traversable t )
         => (c, x) -> t (Needle c, Needle x) -> Maybe (Embedding (Affine s) c x)
correspondingDirections (c₀, x₀) dirMap
   = freeEmbeddings $> Embedding (Affine . trie $ c2x)
                                 (Affine . trie $ x2c)
 where freeEmbeddings = fzip ( embedFreeSubspace $ fst<$>dirMap
                             , embedFreeSubspace $ snd<$>dirMap )
       c2t :: Lens' (Needle c) (t s)
       c2t = case freeEmbeddings of Just (Lens ct, _) -> ct
       x2t :: Lens' (Needle x) (t s)
       x2t = case freeEmbeddings of Just (_, Lens xt) -> xt
       c2x :: ChartIndex c -> (x, LinearMap s (Needle c) (Needle x))
       c2x ιc
              = ( x₀ .+~^ (zeroV & x2t .~ δc^.c2t)
                , arr . LinearFunction $ \dc -> zeroV & x2t .~ dc^.c2t )
        where Just δc = chartReferencePoint ιc .-~. c₀
       x2c :: ChartIndex x
                            -> (c, LinearMap s (Needle x) (Needle c))
       x2c ιx
              = ( c₀ .+~^ (zeroV & c2t .~ δx^.x2t)
                , arr . LinearFunction $ \dx -> zeroV & c2t .~ dx^.x2t )
        where Just δx = chartReferencePoint ιx .-~. x₀
