
-- |
-- Module      : Data.SetLike.Intersection
-- Copyright   : (c) Justus Sagemüller 2016
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsag $ hvl.no
-- Stability   : experimental
-- Portability : portable
-- 


module Data.SetLike.Intersection where

import qualified Data.List.NonEmpty as NE
import Data.List.NonEmpty (NonEmpty(..))


newtype IntersectT s x = IntersectT { getIntersectors :: NonEmpty (s x) }


singleIntersect :: s x -> IntersectT s x
singleIntersect = IntersectT . pure

rmTautologyIntersect ::
         (s x -> s x -> Maybe (s x)) -- ^ Subset-finder
      -> IntersectT s x -> IntersectT s x
rmTautologyIntersect smaller (IntersectT isoa) = IntersectT $ rti isoa
 where rti (s₀:|ss) = reduce [] ss
        where reduce [] [] = s₀:|[]
              reduce (sp₀:sp) [] = NE.cons s₀ $ rti (sp₀:|sp)
              reduce sp (s₁:sr) = case smaller s₀ s₁ of
               Just si -> rti $ si :| (sp ++ sr)
               Nothing -> reduce (s₁:sp) sr
            

