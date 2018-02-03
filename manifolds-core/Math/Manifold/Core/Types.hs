-- |
-- Module      : Math.Manifold.Core.Types
-- Copyright   : (c) Justus Sagemüller 2016
-- License     : GPL v3
-- 
-- Maintainer  : (@) sagemueller $ geo.uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 
-- Several low-dimensional manifolds, represented in some simple way as Haskell
-- data types. All these are in the 'PseudoAffine' class.
-- 


{-# LANGUAGE TypeFamilies             #-}


module Math.Manifold.Core.Types where


import Data.VectorSpace
import Math.Manifold.VectorSpace.ZeroDimensional
import Data.AffineSpace
import Data.Basis
import Data.Void
import Data.Monoid

import Control.Applicative (Const(..), Alternative(..))




-- | The zero-dimensional sphere is actually just two points. Implementation might
--   therefore change to @ℝ⁰ 'Control.Category.Constrained.+' ℝ⁰@: the disjoint sum of two
--   single-point spaces.
data S⁰ = PositiveHalfSphere | NegativeHalfSphere deriving(Eq, Show)

otherHalfSphere :: S⁰ -> S⁰
otherHalfSphere PositiveHalfSphere = NegativeHalfSphere
otherHalfSphere NegativeHalfSphere = PositiveHalfSphere

data ℝP⁰ = ℝPZero deriving (Eq, Show)

-- | The unit circle.
newtype S¹ = S¹ { φParamS¹ :: Double -- ^ Must be in range @[-π, π[@.
                } deriving (Show)




newtype ℝP¹ = ℝP¹ { rParamℝP¹ :: Double -- ^ Range @[-1,1]@.
                  } deriving (Show)

-- | The ordinary unit sphere.
data S² = S² { ϑParamS² :: !Double -- ^ Range @[0, π[@.
             , φParamS² :: !Double -- ^ Range @[-π, π[@.
             } deriving (Show)



-- | The two-dimensional real projective space, implemented as a unit disk with
--   opposing points on the rim glued together.
data ℝP² = ℝP² { rParamℝP² :: !Double -- ^ Range @[0, 1]@.
               , φParamℝP² :: !Double -- ^ Range @[-π, π[@.
               } deriving (Show)



-- | The standard, closed unit disk. Homeomorphic to the cone over 'S¹', but not in the
--   the obvious, &#x201c;flat&#x201d; way. (And not at all, despite
--   the identical ADT definition, to the projective space 'ℝP²'!)
data D² = D² { rParamD² :: !Double -- ^ Range @[0, 1]@.
             , φParamD² :: !Double -- ^ Range @[-π, π[@.
             } deriving (Show)

-- | A (closed) cone over a space @x@ is the product of @x@ with the closed interval 'D¹'
--   of &#x201c;heights&#x201d;,
--   except on its &#x201c;tip&#x201d;: here, @x@ is smashed to a single point.
--   
--   This construct becomes (homeomorphic-to-) an actual geometric cone (and to 'D²') in the
--   special case @x = 'S¹'@.
data CD¹ x = CD¹ { hParamCD¹ :: !Double -- ^ Range @[0, 1]@
                 , pParamCD¹ :: !x      -- ^ Irrelevant at @h = 0@.
                 } deriving (Show)


-- | An open cone is homeomorphic to a closed cone without the &#x201c;lid&#x201d;,
--   i.e. without the &#x201c;last copy&#x201d; of @x@, at the far end of the height
--   interval. Since that means the height does not include its supremum, it is actually
--   more natural to express it as the entire real ray, hence the name.
data Cℝay x = Cℝay { hParamCℝay :: !Double -- ^ Range @[0, &#x221e;[@
                   , pParamCℝay :: !x      -- ^ Irrelevant at @h = 0@.
                   } deriving (Show)






-- | The &#x201c;one-dimensional disk&#x201d; &#x2013; really just the line segment between
--   the two points -1 and 1 of 'S⁰', i.e. this is simply a closed interval.
newtype D¹ = D¹ { xParamD¹ :: Double -- ^ Range @[-1, 1]@.
                } deriving (Show)
fromIntv0to1 :: ℝ -> D¹
fromIntv0to1 x | x<0        = D¹ (-1)
               | x>1        = D¹ 1
               | otherwise  = D¹ $ x*2 - 1



type ℝ = Double
type ℝ⁰ = ZeroDim ℝ




instance VectorSpace () where
  type Scalar () = ℝ
  _ *^ () = ()

instance HasBasis () where
  type Basis () = Void
  basisValue = absurd
  decompose () = []
  decompose' () = absurd
instance InnerSpace () where
  () <.> () = 0


