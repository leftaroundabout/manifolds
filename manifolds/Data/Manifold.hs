-- |
-- Module      : Data.Manifold
-- Copyright   : (c) Justus Sagemüller 2013
-- License     : GPL v3
-- 
-- Maintainer  : (@) sagemueller $ geo.uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 
-- This is something of a first attempt at formalising manifolds and continuous
-- mappings thereon. They /work/
-- (check out <http://hackage.haskell.org/package/dynamic-plot-0.1.0.0> for a use case),
-- but aren't very efficient. The interface might well change considerably in the future.


{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE UndecidableInstances     #-}


module Data.Manifold (module Data.Manifold.PseudoAffine, module Data.Manifold.Types) where

import Data.Manifold.PseudoAffine
import Data.Manifold.Types







