-- |
-- Module      : Math.Manifold.Embedding.Simple.Class
-- Copyright   : (c) Justus Sagemüller 2018
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsag $ hvl.no
-- Stability   : experimental
-- Portability : portable
-- 
-- Some manifolds are “naturally” embedded within some bigger space. For instance,
-- the topological spheres are readily identified with the geometric unit spheres in
-- real vector spaces.
--
-- An embedding is a pretty strong relationship, but often all that's needed is being
-- able to map single points from the manifold to the enclosing space. This module offers
-- a class which does just that.




module Math.Manifold.Embedding.Simple.Class (
          NaturallyEmbedded(..)
   ) where


import Data.Manifold.Types.Primitive
