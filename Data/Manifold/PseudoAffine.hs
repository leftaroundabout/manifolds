{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE UndecidableInstances     #-}
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
{-# LANGUAGE CPP                      #-}


module Data.Manifold.PseudoAffine where
    


import Data.List
import Data.Maybe
import Data.Semigroup
import Data.Function (on)
import Data.Fixed

import Data.VectorSpace
import Data.LinearMap
import Data.LinearMap.HerMetric
import Data.MemoTrie (HasTrie)
import Data.AffineSpace
import Data.Basis
import Data.Complex hiding (magnitude)
import Data.Void
import Data.Tagged
import Data.Manifold.Types

import qualified Prelude

import Control.Category.Constrained.Prelude hiding ((^))
import Control.Arrow.Constrained
import Control.Monad.Constrained
import Data.Foldable.Constrained




infix 6 .-~.
infixl 6 .+~^

-- | 'PseudoAffine' is intended as an alternative class for 'Manifold's. The interface
--   is almost identical to the better-known 'AffineSpace' class, but unlike in the
--   standard mathematical definition of affine spaces we don't require associativity of
--   '.+~^' with '^+^', except in an asymptotic sense for small vectors.
--   
--   That innocent-looking change makes the class applicable to vastly more general types:
--   while an affine space is basically nothing but a vector space without particularly
--   designated origin, a pseudo-affine space can have nontrivial topology on the global
--   scale, and yet be used in practically the same way as an affine space. At least the
--   usual spheres and tori make good instances, perhaps the class is in fact equivalent to
--   /parallelisable manifolds/.
class PseudoAffine x where
  type PseudoDiff x :: *
  (.-~.) :: x -> x -> Option (PseudoDiff x)
  (.+~^) :: x -> PseudoDiff x -> x


type LocallyScalable s x = ( PseudoAffine x, (PseudoDiff x) ~ PseudoDiff x
                           , HasMetric (PseudoDiff x)
                           , DualSpace (PseudoDiff x) ~ DualSpace (PseudoDiff x)
                           , HasMetric (DualSpace (PseudoDiff x))
                           , PseudoDiff x ~ DualSpace (DualSpace (PseudoDiff x))
                           , s ~ Scalar (PseudoDiff x)
                           , s ~ Scalar (DualSpace (PseudoDiff x)) )
type LinearManifold s x = ( PseudoAffine x, PseudoDiff x ~ x
                          , HasMetric x, HasMetric (DualSpace x)
                          , DualSpace (DualSpace x) ~ x
                          , s ~ Scalar x, s ~ Scalar (DualSpace x) )
type RealDimension r = ( PseudoAffine r, PseudoDiff r ~ r
                       , HasMetric r, DualSpace r ~ r, Scalar r ~ r
                       , RealFloat r )



palerp :: (PseudoAffine x, VectorSpace (PseudoDiff x))
    => x -> x -> Option (Scalar (PseudoDiff x) -> x)
palerp p1 p2 = fmap (\v t -> p1 .+~^ t *^ v) $ p2 .-~. p1



#define deriveAffine(t)          \
instance PseudoAffine t where {   \
  type PseudoDiff t = Diff t;      \
  a.-~.b = pure (a.-.b);            \
  (.+~^) = (.+^)  }

deriveAffine(Double)
deriveAffine(Rational)

instance PseudoAffine (ZeroDim k) where
  type PseudoDiff (ZeroDim k) = ZeroDim k
  Origin .-~. Origin = pure Origin
  Origin .+~^ Origin = Origin
instance (PseudoAffine a, PseudoAffine b) => PseudoAffine (a,b) where
  type PseudoDiff (a,b) = (PseudoDiff a, PseudoDiff b)
  (a,b).-~.(c,d) = liftA2 (,) (a.-~.c) (b.-~.d)
  (a,b).+~^(v,w) = (a.+~^v, b.+~^w)
instance (PseudoAffine a, PseudoAffine b, PseudoAffine c) => PseudoAffine (a,b,c) where
  type PseudoDiff (a,b,c) = (PseudoDiff a, PseudoDiff b, PseudoDiff c)
  (a,b,c).-~.(d,e,f) = liftA3 (,,) (a.-~.d) (b.-~.e) (c.-~.f)
  (a,b,c).+~^(v,w,x) = (a.+~^v, b.+~^w, c.+~^x)


instance PseudoAffine S¹ where
  type PseudoDiff S¹ = ℝ
  S¹ φ₁ .-~. S¹ φ₀
     | δφ > pi     = pure (δφ - 2*pi)
     | δφ < (-pi)  = pure (δφ + 2*pi)
     | otherwise   = pure δφ
   where δφ = φ₁ - φ₀
  S¹ φ₀ .+~^ δφ
     | φ' < 0     = S¹ $ φ' + tau
     | otherwise  = S¹ $ φ'
   where φ' = (φ₀ + δφ)`mod'`tau

instance PseudoAffine S² where
  type PseudoDiff S² = ℝ²
  S² ϑ₁ φ₁ .-~. S² ϑ₀ φ₀
     | ϑ₀ < pi/2  = pure ( ϑ₁*^embed(S¹ φ₁) ^-^ ϑ₀*^embed(S¹ φ₀) )
     | otherwise  = pure ( (pi-ϑ₁)*^embed(S¹ φ₁) ^-^ (pi-ϑ₀)*^embed(S¹ φ₀) )
  S² ϑ₀ φ₀ .+~^ δv
     | ϑ₀ < pi/2  = sphereFold PositiveHalfSphere $ ϑ₀*^embed(S¹ φ₀) ^+^ δv
     | otherwise  = sphereFold NegativeHalfSphere $ (pi-ϑ₀)*^embed(S¹ φ₀) ^+^ δv

sphereFold :: S⁰ -> ℝ² -> S²
sphereFold hfSphere v
   | ϑ₀ > pi     = S² (inv $ tau - ϑ₀) ((φ₀+pi)`mod'`tau)
   | otherwise  = S² (inv ϑ₀) φ₀
 where S¹ φ₀ = coEmbed v
       ϑ₀ = magnitude v `mod'` tau
       inv ϑ = case hfSphere of PositiveHalfSphere -> ϑ
                                NegativeHalfSphere -> pi - ϑ



tau :: Double
tau = 2 * pi





type LinDevPropag d c = HerMetric (PseudoDiff c) -> HerMetric (PseudoDiff d)

dev_ε_δ :: RealDimension a
                => (a -> a) -> LinDevPropag a a
dev_ε_δ f d = let ε = 1 / metric d 1 in projector $ 1 / sqrt (f ε)

newtype Differentiable s d c
   = Differentiable { runDifferentiable ::
                        d -> ( c, PseudoDiff d :-* PseudoDiff c, LinDevPropag d c ) }
type (-->) = Differentiable ℝ


instance (VectorSpace s) => Category (Differentiable s) where
  type Object (Differentiable s) o = LocallyScalable s o
  id = Differentiable $ \x -> (x, idL, const zeroV)
  Differentiable f . Differentiable g = Differentiable $
     \x -> let (y, g', devg) = g x
               (z, f', devf) = f y
               devfg δz = let δy = transformMetric f' δz
                              εy = devf δz
                          in transformMetric g' εy ^+^ devg δy ^+^ devg εy
           in (z, f'*.*g', devfg)


instance (VectorSpace s) => Cartesian (Differentiable s) where
  type UnitObject (Differentiable s) = ZeroDim s
  swap = Differentiable $ \(x,y) -> ((y,x), lSwap, const zeroV)
   where lSwap = linear swap
  attachUnit = Differentiable $ \x -> ((x, Origin), lAttachUnit, const zeroV)
   where lAttachUnit = linear $ \x ->  (x, Origin)
  detachUnit = Differentiable $ \(x, Origin) -> (x, lDetachUnit, const zeroV)
   where lDetachUnit = linear $ \(x, Origin) ->  x
  regroup = Differentiable $ \(x,(y,z)) -> (((x,y),z), lRegroup, const zeroV)
   where lRegroup = linear regroup
  regroup' = Differentiable $ \((x,y),z) -> ((x,(y,z)), lRegroup, const zeroV)
   where lRegroup = linear regroup'


instance (VectorSpace s) => Morphism (Differentiable s) where
  Differentiable f *** Differentiable g = Differentiable h
   where h (x,y) = ((fx, gy), lPar, devfg)
          where (fx, f', devf) = f x
                (gy, g', devg) = g y
                devfg δs = transformMetric lfst δx 
                           ^+^ transformMetric lsnd δy
                  where δx = devf $ transformMetric lcofst δs
                        δy = devg $ transformMetric lcosnd δs
                lPar = linear $ lapply f'***lapply g'
         lfst = linear fst; lsnd = linear snd
         lcofst = linear (,zeroV); lcosnd = linear (zeroV,)


instance (VectorSpace s) => PreArrow (Differentiable s) where
  terminal = Differentiable $ \_ -> (Origin, zeroV, const zeroV)
  fst = Differentiable $ \(x,_) -> (x, lfst, const zeroV)
   where lfst = linear fst
  snd = Differentiable $ \(_,y) -> (y, lsnd, const zeroV)
   where lsnd = linear snd
  Differentiable f &&& Differentiable g = Differentiable h
   where h x = ((fx, gx), lFanout, devfg)
          where (fx, f', devf) = f x
                (gx, g', devg) = g x
                devfg δs = (devf $ transformMetric lcofst δs)
                           ^+^ (devg $ transformMetric lcosnd δs)
                lFanout = linear $ lapply f'&&&lapply g'
         lcofst = linear (,zeroV); lcosnd = linear (zeroV,)


instance (VectorSpace s) => WellPointed (Differentiable s) where
  unit = Tagged Origin
  globalElement x = Differentiable $ \Origin -> (x, zeroV, const zeroV)
  const x = Differentiable $ \_ -> (x, zeroV, const zeroV)



type DfblFuncValue s = GenericProxy (Differentiable s)

instance (VectorSpace s) => HasProxy (Differentiable s) where
  alg = genericAlg
  ($~) = genericProxyMap
instance (VectorSpace s) => CartesianProxy (Differentiable s) where
  alg1to2 = genericAlg1to2
  alg2to1 = genericAlg2to1
  alg2to2 = genericAlg2to2
instance (VectorSpace s)
      => PointProxy (DfblFuncValue s) (Differentiable s) a x where
  point = genericPoint



actuallyLinear :: ( LinearManifold s x, LinearManifold s y )
            => (x:-*y) -> Differentiable s x y
actuallyLinear f = Differentiable $ \x -> (lapply f x, f, const zeroV)


dfblFnValsFunc :: ( LocallyScalable s c, LocallyScalable s c', LocallyScalable s d
                  , v ~ PseudoDiff c, v' ~ PseudoDiff c'
                  , ε ~ HerMetric v, ε ~ HerMetric v' )
             => (c' -> (c, v':-*v, ε->ε)) -> DfblFuncValue s d c' -> DfblFuncValue s d c
dfblFnValsFunc f = (Differentiable f $~)

dfblFnValsCombine :: forall d c c' c'' v v' v'' ε ε' ε'' s. 
         ( LocallyScalable s c,  LocallyScalable s c',  LocallyScalable s c''
         ,  LocallyScalable s d
         , v ~ PseudoDiff c, v' ~ PseudoDiff c', v'' ~ PseudoDiff c''
         , ε ~ HerMetric v  , ε' ~ HerMetric v'  , ε'' ~ HerMetric v'', ε~ε', ε~ε''  )
       => (  c' -> c'' -> (c, (v',v''):-*v, ε -> (ε',ε''))  )
         -> DfblFuncValue s d c' -> DfblFuncValue s d c'' -> DfblFuncValue s d c
dfblFnValsCombine cmb (GenericProxy (Differentiable f))
                      (GenericProxy (Differentiable g)) 
    = GenericProxy . Differentiable $
        \d -> let (c', f', devf) = f d
                  (c'', g', devg) = g d
                  (c, h', devh) = cmb c' c''
                  h'l = h' *.* lcofst; h'r = h' *.* lcosnd
              in ( c
                 , h' *.* linear (lapply f' &&& lapply g')
                 , \εc -> let εc' = transformMetric h'l εc
                              εc'' = transformMetric h'r εc
                              (δc',δc'') = devh εc 
                          in devf εc' ^+^ devg εc''
                               ^+^ transformMetric f' δc'
                               ^+^ transformMetric g' δc''
                 )
 where lcofst = linear(,zeroV)
       lcosnd = linear(zeroV,) 





instance (LinearManifold s v, LocallyScalable s a, Floating s)
    => AdditiveGroup (DfblFuncValue s a v) where
  zeroV = point zeroV
  (^+^) = dfblFnValsCombine $ \a b -> (a^+^b, lPlus, const zeroV)
      where lPlus = linear $ uncurry (^+^)
  negateV = dfblFnValsFunc $ \a -> (negateV a, lNegate, const zeroV)
      where lNegate = linear negateV
  
instance (RealDimension n, LocallyScalable n a)
            => Num (DfblFuncValue n a n) where
  fromInteger i = point $ fromInteger i
  (+) = dfblFnValsCombine $ \a b -> (a+b, lPlus, const zeroV)
      where lPlus = linear $ uncurry (+)
  (*) = dfblFnValsCombine $
          \a b -> ( a*b
                  , linear $ \(da,db) -> a*db + b*da
                  , \d -> let d¹₂ = sqrt d in (d¹₂,d¹₂)
                           -- ε δa δb = (a+δa)·(b+δb) - (a·b + (a·δa + b·δb)) 
                           --         = δa·δb
                           --   so choose δa = δb = √ε
                  )
  negate = dfblFnValsFunc $ \a -> (negate a, lNegate, const zeroV)
      where lNegate = linear negate
  abs = dfblFnValsFunc dfblAbs
   where dfblAbs a
          | a>0        = (a, idL, dev_ε_δ $ \ε -> a + ε/2) 
          | a<0        = (-a, negateV idL, dev_ε_δ $ \ε -> ε/2 - a)
          | otherwise  = (0, zeroV, (^/ sqrt 2))
  signum = dfblFnValsFunc dfblSgn
   where dfblSgn a
          | a>0        = (1, zeroV, dev_ε_δ $ const a)
          | a<0        = (-1, zeroV, dev_ε_δ $ \_ -> -a)
          | otherwise  = (0, zeroV, const $ projector 1)



-- VectorSpace instance is more problematic than you'd think: multiplication
-- requires the allowed-deviation backpropagators to be split as square
-- roots, but the square root of a nontrivial-vector-space metric requires
-- an eigenbasis transform, which we have not implemented yet.
-- 
-- instance (LinearManifold s v, LocallyScalable s a, Floating s)
--       => VectorSpace (DfblFuncValue s a v) where
--   type Scalar (DfblFuncValue s a v) = DfblFuncValue s a (Scalar v)
--   (*^) = dfblFnValsCombine $ \μ v -> (μ*^v, lScl, \ε -> (ε ^* sqrt 2, ε ^* sqrt 2))
--       where lScl = linear $ uncurry (*^)


-- | Important special operator needed to compute intersection of 'Region's.
minDblfuncs :: (LocallyScalable s m, RealDimension s)
     => Differentiable s m s -> Differentiable s m s -> Differentiable s m s
minDblfuncs (Differentiable f) (Differentiable g) = Differentiable h
 where h x
         | fx==gx   = ( fx, (f'^+^g')^/2
                      , \d -> devf d ^+^ devg d
                               ^+^ transformMetric (f'^-^g')
                                                   (projector $ metric d 1) )
         | fx < gx   = ( fx, f'
                       , \d -> devf d
                               ^+^ transformMetric (f'^-^g')
                                                   (projector $ metric d 1 + gx - fx) )
        where (fx, f', devf) = f x
              (gx, g', devg) = g x



data Region s m where
  GlobalRegion :: Region s m
  Region :: m                      -- Some point /p/ in the region.
         -> (Differentiable s m s) -- A function that is positive at /p/, decreases
                                   --  and crosses zero at the region boundaries.
                                   --  (If it goes positive again somewhere else,
                                   --  these areas shall /not/ be considered belonging
                                   --  to the (by definition connected) region.)
         -> Region s m


newtype PWDiffable s d c
   = PWDiffable {
        getDfblDomain :: d -> (Region s d, Differentiable s d c) }



instance (RealDimension s) => Category (PWDiffable s) where
  type Object (PWDiffable s) o = LocallyScalable s o
  id = PWDiffable $ \x -> (GlobalRegion, id)
  PWDiffable f . PWDiffable g = PWDiffable h
   where h x₀ = case g x₀ of
                 (GlobalRegion, gr)
                  -> let (y₀,_,_) = runDifferentiable gr x₀
                     in case f y₀ of
                         (GlobalRegion, fr) -> (GlobalRegion, fr . gr)
                         (Region _ ry, fr)
                               -> ( Region x₀ $ ry . gr, fr . gr )
                 (Region _ rx, gr)
                  -> let (y₀,_,_) = runDifferentiable gr x₀
                     in case f y₀ of
                         (GlobalRegion, fr) -> (Region x₀ rx, fr . gr)
                         (Region _ ry, fr)
                               -> ( Region x₀ $ minDblfuncs (ry . gr) rx
                                  , fr . gr )
          where (rx, gr) = g x₀
                

