-- |
-- Module      : Math.Manifold.Core.Types.Internal
-- Copyright   : (c) Justus Sagemüller 2018
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsagemue $ uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 
-- Several low-dimensional manifolds, represented in some simple way as Haskell
-- data types. All these are in the 'PseudoAffine' class.
-- 


module Math.Manifold.Core.Types.Internal where

import Math.Manifold.VectorSpace.ZeroDimensional



-- | The zero-dimensional sphere is actually just two points. Implementation might
--   therefore change to @ℝ⁰ 'Control.Category.Constrained.+' ℝ⁰@: the disjoint sum of two
--   single-point spaces.
data S⁰ = PositiveHalfSphere | NegativeHalfSphere deriving(Eq, Show)

data ℝP⁰ = ℝPZero deriving (Eq, Show)

-- | The unit circle.
newtype S¹ = S¹Polar { φParamS¹ :: Double -- ^ Must be in range @[-π, π[@.
                     } deriving (Show)


newtype ℝP¹ = HemisphereℝP¹Polar { φParamℝP¹ :: Double -- ^ Range @[-π/2,π/2[@.
                                 } deriving (Show)

-- | The ordinary unit sphere.
data S² = S²Polar { ϑParamS² :: !Double -- ^ Range @[0, π[@.
                  , φParamS² :: !Double -- ^ Range @[-π, π[@.
                  } deriving (Show)


-- | The two-dimensional real projective space, implemented as a disk with
--   opposing points on the rim glued together. Image this disk as the northern hemisphere
--   of a unit sphere; 'ℝP²' is the space of all straight lines passing through
--   the origin of 'ℝ³', and each of these lines is represented by the point at which it
--   passes through the hemisphere.
data ℝP² = HemisphereℝP²Polar { ϑParamℝP² :: !Double -- ^ Range @[0, π/2]@.
                              , φParamℝP² :: !Double -- ^ Range @[-π, π[@.
                              } deriving (Show)


-- | The standard, closed unit disk. Homeomorphic to the cone over 'S¹', but not in the
--   the obvious, “flat” way. (In is /not/ homeomorphic, despite
--   the almost identical ADT definition, to the projective space 'ℝP²'!)
data D² = D²Polar { rParamD² :: !Double -- ^ Range @[0, 1]@.
                  , φParamD² :: !Double -- ^ Range @[-π, π[@.
                  } deriving (Show)

-- | A (closed) cone over a space @x@ is the product of @x@ with the closed interval 'D¹'
--   of “heights”,
--   except on its “tip”: here, @x@ is smashed to a single point.
--   
--   This construct becomes (homeomorphic-to-) an actual geometric cone (and to 'D²') in the
--   special case @x = 'S¹'@.
data CD¹ x = CD¹ { hParamCD¹ :: !Double -- ^ Range @[0, 1]@
                 , pParamCD¹ :: !x      -- ^ Irrelevant at @h = 0@.
                 } deriving (Show)


-- | An open cone is homeomorphic to a closed cone without the “lid”,
--   i.e. without the “last copy” of @x@, at the far end of the height
--   interval. Since that means the height does not include its supremum, it is actually
--   more natural to express it as the entire real ray, hence the name.
data Cℝay x = Cℝay { hParamCℝay :: !Double -- ^ Range @[0, ∞[@
                   , pParamCℝay :: !x      -- ^ Irrelevant at @h = 0@.
                   } deriving (Show)

-- | The “one-dimensional disk” – really just the line segment between
--   the two points -1 and 1 of 'S⁰', i.e. this is simply a closed interval.
newtype D¹ = D¹ { xParamD¹ :: Double -- ^ Range @[-1, 1]@.
                } deriving (Show)

type ℝ = Double
type ℝ⁰ = ZeroDim ℝ




