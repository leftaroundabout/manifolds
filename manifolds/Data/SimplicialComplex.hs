-- |
-- Module      : Data.Manifold.TreeCover
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
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE DataKinds                  #-}


module Data.SimplicialComplex where



import Data.List hiding (filter, all, elem)
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Vector as Arr
import Data.List.NonEmpty (NonEmpty(..))
import Data.List.FastNub
import qualified Data.List.NonEmpty as NE
import Data.Semigroup
import Data.Ord (comparing)

import Data.VectorSpace
import Data.LinearMap
import Data.LinearMap.Category
import Data.Void
import Data.Tagged
import Data.Proxy

import Data.Manifold.Types
import Data.Manifold.Types.Primitive ((^))
import Data.Manifold.PseudoAffine
    
import Data.Embedding
import Data.CoNat

import qualified Prelude as Hask hiding(foldl)
import qualified Control.Applicative as Hask
import qualified Control.Monad       as Hask
import Control.Monad.Trans.List
import qualified Data.Foldable       as Hask
import Data.Foldable (all, elem)

import Data.Functor.Identity (runIdentity)

import Control.Category.Constrained.Prelude hiding ((^), all, elem)
import Control.Arrow.Constrained
import Control.Monad.Constrained
import Data.Foldable.Constrained

import GHC.Generics (Generic)


-- | An /n/-simplex is a connection of /n/+1 points in a simply connected region of a manifold.
data Simplex :: Nat -> * -> * where
   ZeroSimplex :: !x -> Simplex Z x
   Simplex :: !x -> !(Simplex n x) -> Simplex (S n) x

instance Hask.Functor (Simplex n) where
  fmap f (ZeroSimplex x) = ZeroSimplex (f x)
  fmap f (Simplex x xs) = Simplex (f x) (fmap f xs)


makeSimplex :: ∀ x n . KnownNat n => x ^ S n -> Simplex n x
makeSimplex xs = case makeSimplex' $ Hask.toList xs of
     Option (Just s) -> s

makeSimplex' :: ∀ x n . KnownNat n => [x] -> Option (Simplex n x)
makeSimplex' [] = Option Nothing
makeSimplex' [x] = cozeroT $ ZeroSimplex x
makeSimplex' (x:xs) = fCosuccT (Simplex x <$> makeSimplex' xs)



type Array = Arr.Vector

data Triangulation n x where
        TriangSkeleton :: KnownNat n
                 => Triangulation n x  -- The lower-dimensional skeleton.
                 -> Array              -- Array of `S n`-simplices in this triangulation.
                       ( Int ^ S (S n)   -- “down link” – the subsimplices
                       , [Int]           -- “up link” – what higher simplices have
                       )                 --       this one as a subsimplex?
                 -> Triangulation (S n) x
        TriangVertices :: Array (x, [Int]) -> Triangulation Z x

-- | Combine two triangulations (assumed as disjoint) to a single, non-connected complex.
instance (KnownNat n) => Semigroup (Triangulation n x) where
  TriangVertices vs₁ <> TriangVertices vs₂ = TriangVertices $ vs₁ Arr.++ vs₂
  TriangSkeleton sk₁ sp₁ <> TriangSkeleton sk₂ sp₂
            = TriangSkeleton (sk₁ <> shiftUprefs (Arr.length sp₁) sk₂)
                             (sp₁ Arr.++ fmap (first $ fmap (+ nTopSplxs sk₁)) sp₂)
   where shiftUprefs :: Int -> Triangulation n' x -> Triangulation n' x
         shiftUprefs δn (TriangVertices vs)
                       = TriangVertices $ fmap (second $ fmap (+δn)) vs
         shiftUprefs δn (TriangSkeleton sk' vs)
                       = TriangSkeleton sk' $ fmap (second $ fmap (+δn)) vs
         nTopSplxs :: Triangulation n' x -> Int
         nTopSplxs (TriangVertices vs) = Arr.length vs
         nTopSplxs (TriangSkeleton _ vs) = Arr.length vs
instance (KnownNat n) => Monoid (Triangulation n x) where
  mappend = (<>)
  mempty = coInduceT (TriangVertices mempty) (`TriangSkeleton`mempty)

naïveTriangCone :: forall n x . x -> Triangulation n x -> Triangulation (S n) x
naïveTriangCone x (TriangVertices xs)
        = TriangSkeleton (TriangVertices $ Arr.imap (\j (x,_) -> (x,[j])) xs
                                             `Arr.snoc` (x, [0 .. nxs-1])      )
                         (Arr.imap (\j _ -> (freeTuple $ (nxs,j), [0])) xs)
 where nxs = Arr.length xs
naïveTriangCone x (TriangSkeleton skel skin) = case naïveTriangCone x skel of
     (TriangSkeleton sinew flesh) ->
      let bowels = Arr.imap (\j (sk,[]) -> (sk `freeSnoc` (j+nskel), [0])) skin 
          membranes = TriangSkeleton sinew $ flesh Arr.++ skin
          nskel = case sinew of
             TriangSkeleton _ fibre -> Arr.length fibre
             TriangVertices vs -> Arr.length vs
      in TriangSkeleton membranes bowels




 
-- | Universally-quantified-safe triangulation reader monad.
newtype TriangT t n x m y = TriangT {
            unsafeRunTriangT :: Triangulation n x -> m (y, Triangulation n x) }
   deriving (Hask.Functor)
instance (Hask.Functor m, Monad m (->))
             => Hask.Applicative (TriangT t n x m) where
  pure x = TriangT $ pure . (x,)
  TriangT fs <*> TriangT xs = TriangT $
      fs >=> \(f, t') -> fmap (first f) $ xs t'
instance (Hask.Functor m, Monad m (->)) => Hask.Monad (TriangT t n x m) where
  return x = TriangT $ pure . (x,)
  TriangT xs >>= f = TriangT $
      \t -> xs t >>= \(y,t') -> let (TriangT zs) = f y in zs t

type HaskMonad m = (Hask.Applicative m, Hask.Monad m)

triangReadT :: ∀ t n x m y . HaskMonad m => (Triangulation n x -> m y) -> TriangT t n x m y
triangReadT f = TriangT $ \t -> fmap (,t) $ f t

unsafeEvalTriangT :: ∀ n t x m y . HaskMonad m
                         => TriangT t n x m y -> Triangulation n x -> m y
unsafeEvalTriangT t = fmap fst . unsafeRunTriangT t

evalTriangT :: ∀ n x m y . HaskMonad m => (∀ t . TriangT t n x m y)
                  -> Triangulation n x -> m y
evalTriangT t = fmap fst . unsafeRunTriangT (t :: TriangT () n x m y)

runTriangT :: ∀ n x m y . (∀ t . TriangT t n x m y)
                  -> Triangulation n x -> m (y, Triangulation n x)
runTriangT t = unsafeRunTriangT (t :: TriangT () n x m y)

getEntireTriang :: ∀ t n x m . HaskMonad m => TriangT t n x m (Triangulation n x)
getEntireTriang = TriangT $ \t -> pure (t, t)

getTriang :: ∀ t n k x m . (HaskMonad m, KnownNat k, KnownNat n)
                   => TriangT t n x m (Triangulation k x)
getTriang = onSkeleton getEntireTriang

simplexAsTriangulation :: ∀ n x . Simplex n x -> Triangulation n x
simplexAsTriangulation (ZeroSimplex x) = TriangVertices $ pure (x,[])
simplexAsTriangulation (Simplex x xs) = naïveTriangCone x $ simplexAsTriangulation xs


forgetVolumes :: ∀ n x t m y . (KnownNat n, HaskMonad m)
                     => TriangT t n x m y -> TriangT t (S n) x m y
forgetVolumes (TriangT f) = TriangT $ \(TriangSkeleton l bk)
                             -> fmap (\(y, l') -> (y, TriangSkeleton l' bk)) $ f l

onSkeleton :: ∀ n k x t m y . (KnownNat k, KnownNat n, HaskMonad m) => TriangT t k x m y -> TriangT t n x m y
onSkeleton q@(TriangT qf) = case tryToMatchTTT forgetVolumes q of
    Option (Just q') -> q'
    _ -> TriangT $ \_ -> fmap (second $ const mempty) (qf mempty)


newtype SimplexIT (t :: *) (n :: Nat) (x :: *) = SimplexIT { tgetSimplexIT :: Int }
          deriving (Eq)

lookSplxFacesIT :: ∀ t m n k x . (HaskMonad m, KnownNat k, KnownNat n)
               => SimplexIT t (S k) x -> TriangT t n x m (SimplexIT t k x ^ S(S k))
lookSplxFacesIT = onSkeleton . lookSplxFacesIT'

lookSplxFacesIT' :: ∀ t m n x . (HaskMonad m, KnownNat n)
               => SimplexIT t (S n) x -> TriangT t (S n) x m (SimplexIT t n x ^ S(S n))
lookSplxFacesIT' (SimplexIT i) = triangReadT rc
 where rc (TriangSkeleton _ ssb) = return . fmap SimplexIT . fst $ ssb Arr.! i

lookSplxVerticesIT :: ∀ t m n k x . (HaskMonad m, KnownNat k, KnownNat n)
               => SimplexIT t k x -> TriangT t n x m (SimplexIT t Z x ^ S k)
lookSplxVerticesIT = onSkeleton . lookSplxVerticesIT'

lookSplxVerticesIT' :: ∀ t m n x . (HaskMonad m, KnownNat n)
               => SimplexIT t n x -> TriangT t n x m (SimplexIT t Z x ^ S n)
lookSplxVerticesIT' i = fmap 
       (\vs -> case freeVector vs of
          Option (Just vs') -> vs'
          _ -> error $ "Impossible number " ++ show (length vs) ++ " of vertices for "
                  ++ show n ++ "-simplex in `lookSplxVerticesIT'`."
       ) $ lookSplxsVerticesIT [i]
 where (Tagged n) = theNatN :: Tagged n Int
          

lookSplxsVerticesIT :: ∀ t m n x . HaskMonad m
               => [SimplexIT t n x] -> TriangT t n x m [SimplexIT t Z x]
lookSplxsVerticesIT is = triangReadT rc
 where rc (TriangVertices _) = return is
       rc (TriangSkeleton sk up) = unsafeEvalTriangT
              ( lookSplxsVerticesIT
                      $ SimplexIT <$> fastNub [ j | SimplexIT i <- is
                                                  , j <- Hask.toList . fst $ up Arr.! i ]
              ) sk

lookVertexIT :: ∀ t m n x . (HaskMonad m, KnownNat n)
                                => SimplexIT t Z x -> TriangT t n x m x
lookVertexIT = onSkeleton . lookVertexIT'

lookVertexIT' :: ∀ t m x . HaskMonad m => SimplexIT t Z x -> TriangT t Z x m x
lookVertexIT' (SimplexIT i) = triangReadT $ \(TriangVertices vs) -> return.fst $ vs Arr.! i

lookSimplex :: ∀ t m n k x . (HaskMonad m, KnownNat k, KnownNat n)
               => SimplexIT t k x -> TriangT t n x m (Simplex k x)
lookSimplex s = do 
       vis <- lookSplxVerticesIT s
       fmap makeSimplex $ mapM lookVertexIT vis

simplexITList :: ∀ t m n k x . (HaskMonad m, KnownNat k, KnownNat n)
               => TriangT t n x m [SimplexIT t k x]
simplexITList = onSkeleton simplexITList'

simplexITList' :: ∀ t m n x . (HaskMonad m, KnownNat n)
               => TriangT t n x m [SimplexIT t n x]
simplexITList' = triangReadT $ return . sil
 where sil :: Triangulation n x -> [SimplexIT t n x]
       sil (TriangVertices vs) = [ SimplexIT i | i <- [0 .. Arr.length vs - 1] ]
       sil (TriangSkeleton _ bk) = [ SimplexIT i | i <- [0 .. Arr.length bk - 1] ]


superSimplices :: ∀ t m n k j x . (HaskMonad m, KnownNat k, KnownNat j, KnownNat n)
                  => SimplexIT t k x -> TriangT t n x m [SimplexIT t j x]
superSimplices = runListT . defLstt . matchLevel . pure
 where lvlIt :: ∀ i . (KnownNat i, KnownNat n) => ListT (TriangT t n x m) (SimplexIT t i x)
                                        -> ListT (TriangT t n x m) (SimplexIT t (S i) x)
       lvlIt (ListT m) = ListT . fmap (fnubConcatBy $ comparing tgetSimplexIT)
                                    $ mapM superSimplices' =<< m
       matchLevel = ftorTryToMatchT lvlIt
       defLstt (Option (Just lt)) = lt
       defLstt _ = ListT $ return []

superSimplices' :: ∀ t m n k x . (HaskMonad m, KnownNat k, KnownNat n)
                  => SimplexIT t k x -> TriangT t n x m [SimplexIT t (S k) x]
superSimplices' = onSkeleton . superSimplices''

superSimplices'' :: ∀ t m n x . (HaskMonad m, KnownNat n)
                  => SimplexIT t n x -> TriangT t (S n) x m [SimplexIT t (S n) x]
superSimplices'' (SimplexIT i) = fmap
    ( \tr -> SimplexIT <$> case tr of TriangSkeleton _ tsps -> snd (tsps Arr.! i)
    ) getEntireTriang


triangulationBulk :: ∀ t m n k x . (HaskMonad m, KnownNat k, KnownNat n) => TriangT t n x m [Simplex k x]
triangulationBulk = simplexITList >>= mapM lookSimplex

withThisSubsimplex :: ∀ t m n k j x . (HaskMonad m, KnownNat j, KnownNat k, KnownNat n)
                   => SimplexIT t j x -> TriangT t n x m [SimplexIT t k x]
withThisSubsimplex s = do
      svs <- lookSplxVerticesIT s
      simplexITList >>= filterM (lookSplxVerticesIT >>> fmap`id`
                                      \s'vs -> all (`elem`s'vs) svs )

lookupSimplexCone :: ∀ t m n k x . ( HaskMonad m, KnownNat k, KnownNat n )
     => SimplexIT t Z x -> SimplexIT t k x -> TriangT t n x m (Option (SimplexIT t (S k) x))
lookupSimplexCone tip base = do
    tipSups  :: [SimplexIT t (S k) x] <- superSimplices tip
    baseSups :: [SimplexIT t (S k) x] <- superSimplices base
    return $ case intersect tipSups baseSups of
       (res:_) -> pure res
       _ -> Hask.empty
    




webinateTriang :: ∀ t m n x . (HaskMonad m, KnownNat n)
         => SimplexIT t Z x -> SimplexIT t n x -> TriangT t (S n) x m (SimplexIT t (S n) x)
webinateTriang ptt@(SimplexIT pt) bst@(SimplexIT bs) = do
  existsReady <- lookupSimplexCone ptt bst
  case existsReady of
   Option (Just ext) -> return ext
   _ -> TriangT $ \(TriangSkeleton sk cnn)
         -> let res = SimplexIT $ Arr.length cnn      :: SimplexIT t (S n) x
            in case sk of
             TriangVertices _ -> return
                   $ ( res, TriangSkeleton sk $ Arr.snoc cnn (freeTuple$->$(pt, bs), []) )
             TriangSkeleton _ cnn'
                   -> let (cnbs,_) = cnn' Arr.! bs
                      in do (cnws,sk') <- unsafeRunTriangT (
                              forM cnbs $ \j -> do
                                 kt@(SimplexIT k) <- webinateTriang ptt (SimplexIT j)
                                 onSkeleton $ addUplink' res kt
                                 return k
                             ) sk
                            let snocer = (freeSnoc cnws bs, [])
                            return $ (res, TriangSkeleton sk' $ Arr.snoc cnn snocer)
 where addUplink' :: SimplexIT t (S n) x -> SimplexIT t n x -> TriangT t (S n) x m ()
       addUplink' (SimplexIT i) (SimplexIT j) = TriangT $ \(TriangSkeleton sk cnn)
         -> let sk' = case sk of
                       TriangVertices vs
                           -> let (v,ul) = vs Arr.! j
                              in TriangVertices $ vs Arr.// [(j, (v, i:ul))]
                       TriangSkeleton skd us
                           -> let (b,tl) = us Arr.! j
                              in TriangSkeleton skd $ us Arr.// [(j, (b, i:tl))]
            in return ((), TriangSkeleton sk' cnn)
                                                    



introVertToTriang :: ∀ t m n x . (HaskMonad m, KnownNat n)
                  => x -> [SimplexIT t n x] -> TriangT t (S n) x m (SimplexIT t Z x)
introVertToTriang v glues = do
      j <- fmap SimplexIT . onSkeleton . TriangT $ return . tVertSnoc
      mapM_ (webinateTriang j) glues
      return j
 where tVertSnoc :: Triangulation Z x -> (Int, Triangulation Z x)
       tVertSnoc (TriangVertices vs)
           = (Arr.length vs, TriangVertices $ vs `Arr.snoc` (v,[]))
      



