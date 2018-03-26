-- |
-- Module      : Data.Manifold.Mesh
-- Copyright   : (c) Justus Sagemüller 2018
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsagemue $ uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 

{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE FlexibleContexts    #-}

module Data.Manifold.Mesh where

import Data.Manifold.Types.Primitive
import Math.Manifold.Core.PseudoAffine
import Data.Manifold.PseudoAffine
import Data.Simplex.Abstract

import Data.Manifold.Web
import Data.Manifold.Web.Internal
import Data.Manifold.FibreBundle

class SimplexSpanning (MeshDomainSpace メ) => Mesh メ where
  type MeshDomainSpace メ :: *
  asWeb :: メ y -> PointsWeb (MeshDomainSpace メ) y
  meshSimplicesInWeb :: メ y -> [AbstractSimplex (Needle (MeshDomainSpace メ)) WebNodeId]
  meshSimplices :: メ y -> [SimplexF (MeshDomainSpace メ) y]
  meshSimplices mesh
    = map (fmap $ \i -> case indexWeb web i of
                         Just (x,info) -> (info^.thisNodeData):@.x
                         Nothing -> error $ "Faulty `Mesh` instance: node #"++show i
                                                     ++" not in web." )
          nodeRefs
   where web = webLocalInfo $ asWeb mesh
         nodeRefs = meshSimplicesInWeb mesh
  
