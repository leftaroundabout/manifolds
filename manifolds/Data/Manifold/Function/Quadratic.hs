-- |
-- Module      : Data.Manifold.Function.Quadratic
-- Copyright   : (c) Justus Sagemüller 2016
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsag $ hvl.no
-- Stability   : experimental
-- Portability : portable
-- 

{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE UndecidableInstances     #-}
{-# LANGUAGE LiberalTypeSynonyms      #-}
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE UnicodeSyntax            #-}
{-# LANGUAGE ScopedTypeVariables      #-}


module Data.Manifold.Function.Quadratic (
              Quadratic(..), evalQuadratic
            ) where



import Data.Semigroup
import qualified Data.List.NonEmpty as NE

import Data.MemoTrie
import Data.VectorSpace
import Data.AffineSpace
import Data.Tagged
import Data.Manifold.PseudoAffine
import Data.Manifold.Atlas
import Data.Manifold.Riemannian
import Data.Function.Affine

import Prelude                       hiding (id, ($), fmap, fst)
import Control.Category.Constrained.Prelude (id, ($), fmap, fst)
import Control.Arrow.Constrained ((>>>), (&&&), (***), second)

import Math.LinearMap.Category



data Quadratic s d c where
    Quadratic :: (ChartIndex d :->: ( c, ( LinearMap s (Needle d) (Needle c)
                                         , LinearMap s (SymmetricTensor s (Needle d))
                                                     (Needle c) ) )
                 )  -> Quadratic s d c

affineQuadratic :: (WithField s AffineManifold d, WithField s AffineManifold c)
        => Affine s d c -> Quadratic s d c
affineQuadratic (Affine f) = Quadratic . trie
                  $ untrie f >>> second (id &&& const zeroV)

instance ( Atlas x, HasTrie (ChartIndex x), Manifold y
         , LinearManifold (Needle x), Scalar (Needle x) ~ s
         , LinearManifold (Needle y), Scalar (Needle y) ~ s
         , Needle (Needle y) ~ Needle y
         ) => Semimanifold (Quadratic s x y) where
  type Needle (Quadratic s x y) = Quadratic s x (Needle y)
  (.+~^) = case ( semimanifoldWitness :: SemimanifoldWitness y ) of
    (SemimanifoldWitness) -> \(Quadratic f) (Quadratic g)
      -> Quadratic . trie $ \ix -> case (untrie f ix, untrie g ix) of
          ((fx₀,f'), (gx₀,g')) -> (fx₀.+~^gx₀, f'^+^g')
  semimanifoldWitness = case semimanifoldWitness :: SemimanifoldWitness y of
    SemimanifoldWitness -> SemimanifoldWitness
instance ( Atlas x, HasTrie (ChartIndex x), Manifold y
         , LinearManifold (Needle x), Scalar (Needle x) ~ s
         , LinearManifold (Needle y), Scalar (Needle y) ~ s
         , Needle (Needle y) ~ Needle y
         ) => PseudoAffine (Quadratic s x y) where
  p.-~.q = pure (p.-~!q)
  (.-~!) = case ( semimanifoldWitness :: SemimanifoldWitness y ) of
    (SemimanifoldWitness) -> \(Quadratic f) (Quadratic g)
      -> Quadratic . trie $ \ix -> case (untrie f ix, untrie g ix) of
          ((fx₀,f'), (gx₀,g')) -> (fx₀.-~!gx₀, f'^-^g')
  pseudoAffineWitness = case semimanifoldWitness :: SemimanifoldWitness y of
    SemimanifoldWitness -> PseudoAffineWitness (SemimanifoldWitness)
instance ( Atlas x, HasTrie (ChartIndex x), Manifold y
         , LinearManifold (Needle x), Scalar (Needle x) ~ s
         , LinearManifold (Needle y), Scalar (Needle y) ~ s
         , Needle (Needle y) ~ Needle y
         ) => AffineSpace (Quadratic s x y) where
  type Diff (Quadratic s x y) = Quadratic s x (Needle y)
  (.+^) = (.+~^); (.-.) = (.-~!)
instance ( Atlas x, HasTrie (ChartIndex x)
         , LinearManifold (Needle x), Scalar (Needle x) ~ s
         , LinearManifold y, Scalar y ~ s
         , Needle y ~ y
         ) => AdditiveGroup (Quadratic s x y) where
  zeroV = case linearManifoldWitness :: LinearManifoldWitness y of
       LinearManifoldWitness -> Quadratic . trie $ const (zeroV, zeroV)
  (^+^) = case ( linearManifoldWitness :: LinearManifoldWitness y
               , dualSpaceWitness :: DualSpaceWitness y ) of
      (LinearManifoldWitness, DualSpaceWitness) -> (.+~^)
  negateV = case linearManifoldWitness :: LinearManifoldWitness y of
       LinearManifoldWitness -> \(Quadratic f) -> Quadratic . trie $
             untrie f >>> negateV***negateV
instance ( Atlas x, HasTrie (ChartIndex x)
         , LinearManifold (Needle x), Scalar (Needle x) ~ s
         , LinearManifold y, Scalar y ~ s
         , Needle y ~ y
         ) => VectorSpace (Quadratic s x y) where
  type Scalar (Quadratic s x y) = s
  (*^) = case linearManifoldWitness :: LinearManifoldWitness y of
       LinearManifoldWitness -> \μ (Quadratic f) -> Quadratic . trie $
             untrie f >>> (μ*^)***(μ*^)

evalQuadratic :: ∀ x y s . ( Manifold x, Atlas x, HasTrie (ChartIndex x)
                           , Manifold y
                           , s ~ Scalar (Needle x), s ~ Scalar (Needle y) )
               => Quadratic s x y -> x
                    -> (y, ( LinearMap s (Needle x) (Needle y)
                           , LinearMap s (SymmetricTensor s (Needle x)) (Needle y) ))
evalQuadratic = ea
 where ea :: Quadratic s x y -> x -> (y, ( LinearMap s (Needle x) (Needle y)
                                            , LinearMap s (SymmetricTensor s (Needle x)) (Needle y) ))
       ea (Quadratic f) x = ( fx₀.+~^(ðx'f₀ $ v).+~^(ð²x'f $ squareV v)
                            , ( ðx'f₀ ^+^ 2*^((currySymBilin $ ð²x'f) $ v)
                              , ð²x'f
                              ) )
        where Just v = x .-~. chartReferencePoint chIx
              chIx = lookupAtlas x
              (fx₀, (ðx'f₀, ð²x'f)) = untrie f chIx


