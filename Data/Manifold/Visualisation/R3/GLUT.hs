{-# LANGUAGE TypeFamilies        #-}


module Data.Manifold.Visualisation.R3.GLUT where


import Data.Manifold

import Graphics.Rendering.OpenGL hiding (Triangulation)
import Graphics.UI.GLUT hiding (Triangulation)

import Data.VectorSpace

import Control.Monad
import Control.Arrow

import Data.Vector ((!))
import qualified Data.Vector as V

import System.Exit
import System.Random
import Control.Monad.Random

type Render = IO()

-- instance Random GLfloat where
--   randomR r = first(realToFrac :: Double->GLfloat) . randomR r
--   random = first(realToFrac :: Double->GLfloat) . random

instance Random (Color3 GLfloat) where
  random = runRand $ fmap(\(r:g:b:_) -> Color3 (r/2) (g/2) (b/2)) getRandoms


data TrianglatnRenderCfg v = TrianglatnRenderCfg
       { simplexSmallEnoughPred :: Simplex v -> Bool
       -- ^ 'True' if the simplex is sufficiently small to be rendered as a straight line/triangle/tetrahedron...
       , triangleRenderer, edgeRenderer     :: [v]   -> Render
       , logTrianglatnRender :: Bool
       }

stdEdgeRenderer, stdTriangleRenderer, randColTriangleRenderer :: Vertex v => [v] -> Render

stdEdgeRenderer verts = do
    faceColor <- get currentColor
    color $ Color3 (0.7::GLfloat) 0.7 0.7
    renderPrimitive Lines $ mapM_ vertex verts
    color faceColor

stdTriangleRenderer verts = do
    renderPrimitive Triangles $ mapM_ vertex verts

randColTriangleRenderer verts = do
    color =<< (randomIO :: IO (Color3 GLfloat))
    renderPrimitive Triangles $ mapM_ vertex verts

    


renderTriangulation :: (Vertex v, Show v) => 
                         TrianglatnRenderCfg v -> Triangulation v -> Render
renderTriangulation cfg triang
   = V.forM_ (sComplexSimplices triang) $ renderSimplex cfg
   
renderSimplex :: (Vertex v, Show v) =>
                       TrianglatnRenderCfg v
                    -> Simplex v -> Render
renderSimplex _ (Simplex0 p) = renderPrimitive Points $ vertex p
renderSimplex cfg s@(SimplexN sides _)
 | simplexSmallEnoughPred cfg s = do
         case V.length sides of
           2 -> do
              when (logTrianglatnRender cfg) $ do
                 putStrLn $ "Now plotting a line..."
                 forM_ (fSimplexVertices s) print
              edgeRenderer cfg $ fSimplexVertices s
           3 -> do
              when (logTrianglatnRender cfg) $ do
                 putStrLn $ "Now plotting a triangle..."
                 forM_ (fSimplexVertices s) print
              triangleRenderer cfg $ fSimplexVertices s
           _ -> return()
         V.forM_ sides $ renderSimplex cfg
 | otherwise      = renderTriangulation cfg
                          $ simplexBarycentricSubdivision s
renderSimplex cfg (PermutedSimplex _ s) = renderSimplex cfg s


simplexLength :: (InnerSpace v, s~Scalar v, RealFloat s) => Simplex v -> s
simplexLength(Simplex0 _) = 0
simplexLength(SimplexN bounds inrs)
 | V.length bounds == 2   = magnitude $ getSimplex0(bounds!0) ^-^ getSimplex0(bounds!1)
 | otherwise              = V.maximum $ V.map simplexLength bounds
simplexLength(PermutedSimplex _ s) = simplexLength s


triangViewMain :: (Vertex v, Show v) => 
                         TrianglatnRenderCfg v -> Triangulation v -> IO()
triangViewMain cfg triang = do 
    (progname, _) <- getArgsAndInitialize
    createWindow "A simple view of a triangulation"
    initialDisplayMode $= [WithDepthBuffer]
    depthFunc $= Just Less
    keyboardMouseCallback $= Just keyboardMouse
    displayCallback $= display
    mainLoop
 where display = do 
         clear [ColorBuffer, DepthBuffer]
         color $ Color3 (0.3::GLfloat) 0.3 0.3
         renderTriangulation cfg triang
         flush
         
       keyboardMouse :: KeyboardMouseCallback
       keyboardMouse (Char '\ESC') Down _ _ = exitSuccess
       keyboardMouse key state modifiers position = return ()


         
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