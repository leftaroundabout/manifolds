{-# LANGUAGE TypeOperators, GADTs, FlexibleContexts #-}

module Data.Function.Differentiable.Data where


import Data.Semigroup
import Data.Function.Affine
import Data.VectorSpace
import Math.LinearMap.Category

import Data.Manifold.Types.Primitive
import Data.Manifold.PseudoAffine

import qualified Control.Category.Constrained as CC



type LinDevPropag d c = Metric c -> Metric d


-- | The category of differentiable functions between manifolds over scalar @s@.
--   
--   As you might guess, these offer /automatic differentiation/ of sorts (basically,
--   simple forward AD), but that's in itself is not really the killer feature here.
--   More interestingly, we actually have the (à la Curry-Howard) /proof/
--   built in: the function /f/ has at /x/&#x2080; derivative /f'&#x2093;/&#x2080;,
--   if, for&#xb9; /&#x3b5;/>0, there exists /&#x3b4;/ such that
--   |/f/ /x/ &#x2212; (/f/ /x/&#x2080; + /x/&#x22c5;/f'&#x2093;/&#x2080;)| < /&#x3b5;/
--   for all |/x/ &#x2212; /x/&#x2080;| < /&#x3b4;/.
-- 
--   Observe that, though this looks quite similar to the standard definition
--   of differentiability, it is not equivalent thereto &#x2013; in fact it does
--   not prove any analytic properties at all. To make it equivalent, we need
--   a lower bound on /&#x3b4;/: simply /&#x3b4;/ gives us continuity, and for
--   continuous differentiability, /&#x3b4;/ must grow at least like &#x221a;/&#x3b5;/
--   for small /&#x3b5;/. Neither of these conditions are enforced by the type system,
--   but we do require them for any allowed values because these proofs are obviously
--   tremendously useful &#x2013; for instance, you can have a root-finding algorithm
--   and actually be sure you get /all/ solutions correctly, not just /some/ that are
--   (hopefully) the closest to some reference point you'd need to laborously define!
-- 
--   Unfortunately however, this also prevents doing any serious algebra with the
--   category, because even something as simple as division necessary introduces
--   singularities where the derivatives must diverge.
--   Not to speak of many e.g. trigonometric functions that are undefined
--   on whole regions. The 'PWDiffable' and 'RWDiffable' categories have explicit
--   handling for those issues built in; you may simply use these categories even when
--   you know the result will be smooth in your relevant domain (or must be, for e.g.
--   physics reasons).
--   
--   &#xb9;(The implementation does not deal with /&#x3b5;/ and /&#x3b4;/ as
--   difference-bounding reals, but rather as metric tensors which define a
--   boundary by prohibiting the overlap from exceeding one.
--   This makes the category actually work on general manifolds.)
data Differentiable s d c where
   Differentiable :: ( d -> ( c   -- function value
                            , Needle d +> Needle c -- Jacobian
                            , LinDevPropag d c -- Metric showing how far you can go
                                               -- from x₀ without deviating from the
                                               -- Taylor-1 approximation by more than
                                               -- some error margin
                              ) )
                  -> Differentiable s d c
   AffinDiffable :: (AffineManifold d, AffineManifold c)
               => DiffableEndoProof d c -> Affine s d c -> Differentiable s d c




data DiffableEndoProof d c where
  IsDiffableEndo :: DiffableEndoProof d d
  NotDiffableEndo :: DiffableEndoProof d c

instance Semigroup (DiffableEndoProof d c) where
  IsDiffableEndo <> _ = IsDiffableEndo
  _ <> IsDiffableEndo = IsDiffableEndo
  _ <> _ = NotDiffableEndo
  

instance CC.Category DiffableEndoProof where
  id = IsDiffableEndo
  IsDiffableEndo . IsDiffableEndo = IsDiffableEndo
  _ . _ = NotDiffableEndo


-- | A pathwise connected subset of a manifold @m@, whose tangent space has scalar @s@.
data Region s m = Region { regionRefPoint :: m
                         , regionRDef :: PreRegion s m }

-- | A 'PreRegion' needs to be associated with a certain reference point ('Region'
--   includes that point) to define a connected subset of a manifold.
data PreRegion s m where
  GlobalRegion :: PreRegion s m
  RealSubray :: RealDimension s => S⁰ -> s -> PreRegion s s
  PreRegion :: (Differentiable s m s) -- A function that is positive at reference point /p/,
                                      -- decreases and crosses zero at the region's
                                      -- boundaries. (If it goes positive again somewhere
                                      -- else, these areas shall /not/ be considered
                                      -- belonging to the (by definition connected) region.)
         -> PreRegion s m








-- | Category of functions that, where defined, have an open region in
--   which they are continuously differentiable. Hence /RegionWiseDiff'able/.
--   Basically these are the partial version of `PWDiffable`.
-- 
--   Though the possibility of undefined regions is of course not too nice
--   (we don't need Java to demonstrate this with its everywhere-looming @null@ values...),
--   this category will propably be the &#x201c;workhorse&#x201d; for most serious
--   calculus applications, because it contains all the usual trig etc. functions
--   and of course everything algebraic you can do in the reals.
-- 
--   The easiest way to define ordinary functions in this category is hence
--   with its 'AgentVal'ues, which have instances of the standard classes 'Num'
--   through 'Floating'. For instance, the following defines the /binary entropy/
--   as a differentiable function on the interval @]0,1[@: (it will
--   actually /know/ where it's defined and where not. And I don't mean you
--   need to exhaustively 'isNaN'-check all results...)
-- 
-- @
-- hb :: RWDiffable &#x211d; &#x211d; &#x211d;
-- hb = alg (\\p -> - p * logBase 2 p - (1-p) * logBase 2 (1-p) )
-- @
newtype RWDiffable s d c
   = RWDiffable {
        tryDfblDomain :: d -> (PreRegion s d, Option (Differentiable s d c)) }

notDefinedHere :: Option (Differentiable s d c)
notDefinedHere = Option Nothing

