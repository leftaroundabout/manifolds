-- |
-- Module      : Data.SimplicialComplex
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


module Data.SimplicialComplex (
        -- * Simplices
          Simplex(..)
        -- ** Construction
        , (.<.), makeSimplex, makeSimplex'
        -- ** Deconstruction
        , simplexVertices, simplexVertices'
        -- * Simplicial complexes
        , Triangulation
        , singleSimplex
        -- * Triangulation-builder monad
        , TriangT
        , evalTriangT, runTriangT, getTriang
        -- ** Subsimplex-references
        , SimplexIT, simplexITList, lookSimplex, tgetSimplexIT
        -- ** Building triangulations
        , disjointTriangulation
        , disjointSimplex
        , introVertToTriang
        , webinateTriang
        -- * Misc util
        , HaskMonad
        , Nat, Zero, One, Two, Three, Succ
        ) where



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
import Control.Monad.Trans.Class
import qualified Data.Foldable       as Hask
import Data.Foldable (all, elem)

import Data.Functor.Identity (Identity, runIdentity)

import Control.Category.Constrained.Prelude hiding ((^), all, elem)
import Control.Arrow.Constrained
import Control.Monad.Constrained
import Data.Foldable.Constrained

import GHC.Generics (Generic)

infixr 5 :<|, .<.

-- | An /n/-simplex is a connection of /n/+1 points in a simply connected region of a manifold.
data Simplex :: Nat -> * -> * where
   ZS :: !x -> Simplex Z x
   (:<|) :: KnownNat n => !x -> !(Simplex n x) -> Simplex (S n) x

deriving instance (Show x) => Show (Simplex n x)
instance Hask.Functor (Simplex n) where
  fmap f (ZS x) = ZS (f x)
  fmap f (x:<|xs) = f x :<| fmap f xs

-- | Use this together with ':<|' to easily build simplices, like you might construct lists.
--   E.g. @(0,0) ':<|' (1,0) '.<.' (0,1) :: 'Simplex' 'Two' ℝ²@.
(.<.) :: x -> x -> Simplex One x
x .<. y = x :<| ZS y


makeSimplex :: ∀ x n . KnownNat n => x ^ S n -> Simplex n x
makeSimplex xs = case makeSimplex' $ Hask.toList xs of
     Option (Just s) -> s

makeSimplex' :: ∀ x n . KnownNat n => [x] -> Option (Simplex n x)
makeSimplex' [] = Option Nothing
makeSimplex' [x] = cozeroT $ ZS x
makeSimplex' (x:xs) = fCosuccT ((x:<|) <$> makeSimplex' xs)

simplexVertices :: ∀ x n . Simplex n x -> x ^ S n
simplexVertices (ZS x) = pure x
simplexVertices (x :<| s) = freeCons x (simplexVertices s)

simplexVertices' :: ∀ x n . Simplex n x -> [x]
simplexVertices' (ZS x) = [x]
simplexVertices' (x :<| s) = x : simplexVertices' s


type Array = Arr.Vector

-- | An /n/-dimensional /abstract simplicial complex/ is a collection of /n/-simplices
--   which are &#x201c;glued together&#x201d; in some way. The preferred way to construct
--   such complexes is to run a 'TriangT' builder.
data Triangulation (n :: Nat) (x :: *) where
        TriangSkeleton :: KnownNat n
                 => Triangulation n x  -- The lower-dimensional skeleton.
                 -> Array              -- Array of `S n`-simplices in this triangulation.
                       ( Int ^ S (S n)   -- “down link” – the subsimplices
                       , [Int]           -- “up link” – what higher simplices have
                       )                 --       this one as a subsimplex?
                 -> Triangulation (S n) x
        TriangVertices :: Array (x, [Int]) -> Triangulation Z x
instance Hask.Functor (Triangulation n) where
  fmap f (TriangVertices vs) = TriangVertices $ first f <$> vs
  fmap f (TriangSkeleton sk vs) = TriangSkeleton (f<$>sk) vs
deriving instance (Show x) => Show (Triangulation n x)

-- | Consider a single simplex as a simplicial complex, consisting only of
--   this simplex and its faces.
singleSimplex :: ∀ n x . KnownNat n => Simplex n x -> Triangulation n x
singleSimplex (ZS x) = TriangVertices $ pure (x, [])
singleSimplex (x :<| s)
         = runIdentity . execTriangT insX $ TriangSkeleton (singleSimplex s) mempty
 where insX :: ∀ t . TriangT t n x Identity ()
       insX = introVertToTriang x [SimplexIT 0] >> return()

nTopSplxs :: Triangulation n' x -> Int
nTopSplxs (TriangVertices vs) = Arr.length vs
nTopSplxs (TriangSkeleton _ vs) = Arr.length vs


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
instance (KnownNat n) => Monoid (Triangulation n x) where
  mappend = (<>)
  mempty = coInduceT (TriangVertices mempty) (`TriangSkeleton`mempty)




 
-- | A &#x201c;conservative&#x201d; state monad containing a 'Triangulation'. It
--   can be extended by new simplices, which can then be indexed using 'SimplexIT'.
--   The universally-quantified @t@ argument ensures you can't index simplices that
--   don't actually exist in this triangulation.
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
      \t -> xs t >>= \(y,t') -> let (TriangT zs) = f y in zs t'

instance MonadTrans (TriangT t n x) where
  lift m = TriangT $ \tr -> Hask.liftM (,tr) m

type HaskMonad m = (Hask.Applicative m, Hask.Monad m)

triangReadT :: ∀ t n x m y . HaskMonad m => (Triangulation n x -> m y) -> TriangT t n x m y
triangReadT f = TriangT $ \t -> fmap (,t) $ f t

unsafeEvalTriangT :: ∀ n t x m y . HaskMonad m
                         => TriangT t n x m y -> Triangulation n x -> m y
unsafeEvalTriangT t = fmap fst . unsafeRunTriangT t

execTriangT :: ∀ n x m y . HaskMonad m => (∀ t . TriangT t n x m y)
                  -> Triangulation n x -> m (Triangulation n x)
execTriangT t = fmap snd . unsafeRunTriangT (t :: TriangT () n x m y)

evalTriangT :: ∀ n x m y . (KnownNat n, HaskMonad m) => (∀ t . TriangT t n x m y) -> m y
evalTriangT t = fmap fst (unsafeRunTriangT (t :: TriangT () n x m y) mempty)

runTriangT :: ∀ n x m y . (∀ t . TriangT t n x m y)
                  -> Triangulation n x -> m (y, Triangulation n x)
runTriangT t = unsafeRunTriangT (t :: TriangT () n x m y)

getEntireTriang :: ∀ t n x m . HaskMonad m => TriangT t n x m (Triangulation n x)
getEntireTriang = TriangT $ \t -> pure (t, t)

getTriang :: ∀ t n k x m . (HaskMonad m, KnownNat k, KnownNat n)
                   => TriangT t n x m (Option (Triangulation k x))
getTriang = onSkeleton getEntireTriang



forgetVolumes :: ∀ n x t m y . (KnownNat n, HaskMonad m)
                     => TriangT t n x m y -> TriangT t (S n) x m y
forgetVolumes (TriangT f) = TriangT $ \(TriangSkeleton l bk)
                             -> fmap (\(y, l') -> (y, TriangSkeleton l' bk)) $ f l

onSkeleton :: ∀ n k x t m y . (KnownNat k, KnownNat n, HaskMonad m)
                   => TriangT t k x m y -> TriangT t n x m (Option y)
onSkeleton q@(TriangT qf) = case tryToMatchTTT forgetVolumes q of
    Option (Just q') -> pure <$> q'
    _ -> return Hask.empty


newtype SimplexIT (t :: *) (n :: Nat) (x :: *) = SimplexIT { tgetSimplexIT' :: Int }
          deriving (Eq, Ord)

-- | A unique (for the given dimension) ID of a triagulation's simplex. It is the index
--   where that simplex can be found in the 'simplexITList'.
tgetSimplexIT :: SimplexIT t n x -> Int
tgetSimplexIT = tgetSimplexIT'

lookSplxFacesIT :: ∀ t m n k x . (HaskMonad m, KnownNat k, KnownNat n)
               => SimplexIT t (S k) x -> TriangT t n x m (SimplexIT t k x ^ S(S k))
lookSplxFacesIT = fmap (\(Option(Just r))->r) . onSkeleton . lookSplxFacesIT'

lookSplxFacesIT' :: ∀ t m n x . (HaskMonad m, KnownNat n)
               => SimplexIT t (S n) x -> TriangT t (S n) x m (SimplexIT t n x ^ S(S n))
lookSplxFacesIT' (SimplexIT i) = triangReadT rc
 where rc (TriangSkeleton _ ssb) = return . fmap SimplexIT . fst $ ssb Arr.! i

lookSplxVerticesIT :: ∀ t m n k x . (HaskMonad m, KnownNat k, KnownNat n)
               => SimplexIT t k x -> TriangT t n x m (SimplexIT t Z x ^ S k)
lookSplxVerticesIT = fmap (\(Option(Just r))->r) . onSkeleton . lookSplxVerticesIT'

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
lookVertexIT = fmap (\(Option(Just r))->r) . onSkeleton . lookVertexIT'

lookVertexIT' :: ∀ t m x . HaskMonad m => SimplexIT t Z x -> TriangT t Z x m x
lookVertexIT' (SimplexIT i) = triangReadT $ \(TriangVertices vs) -> return.fst $ vs Arr.! i

lookSimplex :: ∀ t m n k x . (HaskMonad m, KnownNat k, KnownNat n)
               => SimplexIT t k x -> TriangT t n x m (Simplex k x)
lookSimplex s = do 
       vis <- lookSplxVerticesIT s
       fmap makeSimplex $ mapM lookVertexIT vis

simplexITList :: ∀ t m n k x . (HaskMonad m, KnownNat k, KnownNat n)
               => TriangT t n x m [SimplexIT t k x]
simplexITList = fmap (\(Option(Just r))->r) $ onSkeleton simplexITList'

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
superSimplices' = fmap (\(Option(Just r))->r) . onSkeleton . superSimplices''

superSimplices'' :: ∀ t m n x . (HaskMonad m, KnownNat n)
                  => SimplexIT t n x -> TriangT t (S n) x m [SimplexIT t (S n) x]
superSimplices'' (SimplexIT i) =
    fmap ( \tr -> SimplexIT <$> case tr of
                    TriangSkeleton (TriangSkeleton _ tsps) _ -> snd (tsps Arr.! i)
                    TriangSkeleton (TriangVertices tsps) _ -> snd (tsps Arr.! i)
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
    


-- | Import an entire triangulation, as disjoint from everything already in the monad.
disjointTriangulation :: ∀ t m n x . (KnownNat n, HaskMonad m)
       => Triangulation n x -> TriangT t n x m (SimplexIT t n x)
disjointTriangulation t = TriangT $ \tr -> return ( SimplexIT $ nTopSplxs tr, tr <> t )

disjointSimplex :: ∀ t m n x . (KnownNat n, HaskMonad m)
       => Simplex n x -> TriangT t n x m (SimplexIT t n x)
disjointSimplex = disjointTriangulation . singleSimplex


webinateTriang :: ∀ t m n x . (HaskMonad m, KnownNat n)
         => SimplexIT t Z x -> SimplexIT t n x -> TriangT t (S n) x m (SimplexIT t (S n) x)
webinateTriang ptt@(SimplexIT pt) bst@(SimplexIT bs) = do
  existsReady <- lookupSimplexCone ptt bst
  case existsReady of
   Option (Just ext) -> return ext
   _ -> TriangT $ \(TriangSkeleton sk cnn)
         -> let resi = Arr.length cnn
                res = SimplexIT $ Arr.length cnn      :: SimplexIT t (S n) x
            in case sk of
             TriangVertices vs -> return
                   $ ( res
                     , TriangSkeleton (TriangVertices
                           $ vs Arr.// [ (pt, second (resi:) $ vs Arr.! pt)
                                       , (bs, second (resi:) $ vs Arr.! bs) ]
                               ) $ Arr.snoc cnn (freeTuple$->$(pt, bs), []) )
             TriangSkeleton _ cnn'
                   -> let (cnbs,_) = cnn' Arr.! bs
                      in do (cnws,sk') <- unsafeRunTriangT ( do
                              cnws <- forM cnbs $ \j -> do
                                 kt@(SimplexIT k) <- webinateTriang ptt (SimplexIT j)
                                 addUplink' res kt
                                 return k
                              addUplink' res bst
                              return cnws
                             ) sk
                            let snocer = (freeSnoc cnws bs, [])
                            return $ (res, TriangSkeleton sk' $ Arr.snoc cnn snocer)
 where addUplink' :: SimplexIT t (S n) x -> SimplexIT t n x -> TriangT t n x m ()
       addUplink' (SimplexIT i) (SimplexIT j) = TriangT
        $ \sk -> pure ((), case sk of
                       TriangVertices vs
                           -> let (v,ul) = vs Arr.! j
                              in TriangVertices $ vs Arr.// [(j, (v, i:ul))]
                       TriangSkeleton skd us
                           -> let (b,tl) = us Arr.! j
                              in TriangSkeleton skd $ us Arr.// [(j, (b, i:tl))]
                   )
                                                    



introVertToTriang :: ∀ t m n x . (HaskMonad m, KnownNat n)
                  => x -> [SimplexIT t n x] -> TriangT t (S n) x m (SimplexIT t Z x)
introVertToTriang v glues = do
      j <- fmap (\(Option(Just k)) -> SimplexIT k) . onSkeleton . TriangT
             $ return . tVertSnoc
      mapM_ (webinateTriang j) glues
      return j
 where tVertSnoc :: Triangulation Z x -> (Int, Triangulation Z x)
       tVertSnoc (TriangVertices vs)
           = (Arr.length vs, TriangVertices $ vs `Arr.snoc` (v,[]))
      




-- | Type-level zero of kind 'Nat'.
type Zero = Z
type One = S Zero
type Two = S One
type Three = S Two
type Succ = S


