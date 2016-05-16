
-- |
-- Module      : Data.SetLike.Intersection
-- Copyright   : (c) Justus Sagemüller 2016
-- License     : GPL v3
-- 
-- Maintainer  : (@) sagemueller $ geo.uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 


module Data.SetLike.Intersection where

import Data.Semigroup


newtype IntersectT s x = IntersectT { getIntersectors :: [s x] }


singleIntersect :: s x -> IntersectT s x
singleIntersect = IntersectT . pure

rmTautologyIntersect ::
         (s x -> s x -> Option (s x)) -- ^ Subset-finder
      -> IntersectT s x -> IntersectT s x
rmTautologyIntersect smaller (IntersectT isoa) = IntersectT $ rti isoa
 where rti (s₀:ss) = reduce [] ss
        where reduce sp [] = s₀ : rti sp
              reduce sp (s₁:sr) = case smaller s₀ s₁ of
               Option (Just si) -> rti $ si : sp ++ sr
               Option Nothing   -> reduce (s₁:sp) sr
       rti l = l
            

