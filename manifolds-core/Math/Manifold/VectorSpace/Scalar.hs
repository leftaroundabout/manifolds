-- |
-- Module      : Math.Manifold.VectorSpace.Scalar
-- Copyright   : (c) Justus Sagemüller 2022
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsag $ hvl.no
-- Stability   : experimental
-- Portability : portable
-- 

{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE UndecidableInstances     #-}
{-# LANGUAGE TypeFamilies             #-}


module Math.Manifold.VectorSpace.Scalar where

import Data.VectorSpace


class (VectorSpace s, Num s, Scalar s ~ s) => ScalarSpace s
instance (VectorSpace s, Num s, Scalar s ~ s) => ScalarSpace s
