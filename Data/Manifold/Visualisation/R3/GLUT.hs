{-# LANGUAGE TypeFamilies        #-}


module Data.Manifold.Visualisation.R3.GLUT where


import Data.Manifold

import Graphics.Rendering.OpenGL hiding (Triangulation)
import Graphics.UI.GLUT hiding (Triangulation)

import Data.VectorSpace

import Control.Monad    

import Data.Vector ((!))
import qualified Data.Vector as V

type Render = IO()



renderTriangulationUntil :: (Vertex v, InnerSpace v, Show v) => 
                         (Simplex v->Bool) -> Triangulation v -> Render
renderTriangulationUntil smallEnough triang
   = V.forM_ (sComplexSimplices triang) $ renderSimplexUntil smallEnough
   
renderSimplexUntil :: (Vertex v, InnerSpace v, Show v) =>
                       (Simplex v->Bool)  -- ^ 'True' if the simplex is sufficiently small to be rendered as a straight line/triangle/tetrahedron...
                    -> Simplex v -> Render
renderSimplexUntil _ (Simplex0 p) = renderPrimitive Points $ vertex p
renderSimplexUntil smallEnough s@(SimplexN sides _)
 | smallEnough s
       = case V.length sides of
           2 -> do
              putStrLn $ "Now plotting a line..."
              forM_ (fSimplexVertices s) print
              faceColor <- get currentColor
              color $ Color3 (1::GLfloat) 1 1
              renderPrimitive Lines $ forM_ (fSimplexVertices s) vertex
              color faceColor
           3 -> do
              putStrLn $ "Now plotting a triangle..."
              forM_ (fSimplexVertices s) print
              renderPrimitive Triangles $ forM_ (fSimplexVertices s) vertex
              V.forM_ sides $ renderSimplexUntil smallEnough
 | otherwise      = renderTriangulationUntil smallEnough 
                          $ simplexBarycentricSubdivision s
renderSimplexUntil se (PermutedSimplex _ s) = renderSimplexUntil se s


simplexLength :: (InnerSpace v, s~Scalar v, RealFloat s) => Simplex v -> s
simplexLength(Simplex0 _) = 0
simplexLength(SimplexN bounds inrs)
 | V.length bounds == 2   = magnitude $ getSimplex0(bounds!0) ^-^ getSimplex0(bounds!1)
 | otherwise              = V.maximum $ V.map simplexLength bounds
simplexLength(PermutedSimplex _ s) = simplexLength s


triangViewMain :: (Vertex v, InnerSpace v, Show v) => 
                         (Simplex v->Bool) -> Triangulation v -> IO()
triangViewMain smallEnough triang = do 
    (progname, _) <- getArgsAndInitialize
    createWindow "A simple view of a triangulation"
    displayCallback $= display
    mainLoop
 where display = do 
         clear [ColorBuffer]
         color $ Color3 (0.1::GLfloat) 0.1 0.1
         renderTriangulationUntil smallEnough triang
         flush
         
-- myPoints :: [(GLfloat,GLfloat,GLfloat)]
-- myPoints = map (\k -> (sin(2*pi*k/12),cos(2*pi*k/12),0.0)) [1..12] 
-- triangViewMain' _ _ = do 
--   (progname, _) <- getArgsAndInitialize
--   createWindow "Hello World"
--   displayCallback $= display
--   mainLoop
--  where display = do 
--           clear [ColorBuffer]
--           renderPrimitive Triangles $ mapM_ (\(x, y, z)->vertex$Vertex3 x y z) myPoints
--           flush