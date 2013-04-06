{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE ScopedTypeVariables #-}


module Data.Manifold.Visualisation.R3.GLUT where


import Data.Manifold

import Prelude hiding ((.), id)

import Graphics.Rendering.OpenGL hiding (Triangulation)
import Graphics.UI.GLUT hiding (Triangulation)

import Data.VectorSpace

import Control.Monad
import Control.Category
import Control.Arrow

import Data.Vector ((!))
import qualified Data.Vector as V

import System.Exit
import System.Random
import Control.Monad.Random


-- instance Random GLfloat where
--   randomR r = first(realToFrac :: Double->GLfloat) . randomR r
--   random = first(realToFrac :: Double->GLfloat) . random

instance Random (Color3 GLfloat) where
  random = runRand $ fmap(\(r:g:b:_) -> Color3 (n r) (n g) (n b)) getRandoms
   where n = (+1/8) . (/2)


data TrianglatnRenderCfg rendMonad vertex = TrianglatnRenderCfg
       { simplexSmallEnoughPred :: Simplex vertex -> rendMonad Bool
       -- ^ 'True' if the simplex is sufficiently small (or obscured-from-sight, etc.)
       --  to be rendered as a straight line/triangle/tetrahedron...
       , triangleRenderer, edgeRenderer     :: [vertex]   -> rendMonad()
       , simplexRenderRefine :: Simplex vertex -> rendMonad () -> rendMonad ()
       , logTrianglatnRender :: String -> rendMonad()
       }


type Render = IO()

stdEdgeRenderer, stdTriangleRenderer, randColTriangleRenderer 
      :: Vertex v => [v] -> Render

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

ignore :: Monad m => a -> m()
ignore = return . const()
    


renderTriangulation :: forall v r. (Show v, Monad r) =>
                   TrianglatnRenderCfg r v -> Triangulation v -> r()
renderTriangulation cfg triang
   = V.forM_ (sComplexSimplices triang) $ renderSimplex cfg
   
   
renderSimplex :: forall v r. (Show v, Monad r) =>
                   TrianglatnRenderCfg r v -> Simplex v -> r()
 
renderSimplex _ (Simplex0 p) = return()
renderSimplex cfg (PermutedSimplex _ s) = renderSimplex cfg s

renderSimplex cfg s@(SimplexN sides _) = do
    allSmallEnough <- smallEnough s
    case V.length sides of
     1 -> return()
     2 | allSmallEnough -> do
              lPutStrLn "Plotting a line..."; lPrint vertices
              edgeRenderer cfg vertices
       | otherwise -> completeSubdiv 
     3 -> do
           (shortEnoughSides, tooLongSides)
                   <- aPartition (Kleisli smallEnough <<^ snd) $ V.indexed sides
           case V.length tooLongSides of
              0 -> do
                 lPutStrLn "Plotting a triangle..."
                 triangle vertices
              1 -> do
                 let (longSideId, (tooLongS_verts, tooLongS_baryCtr))
                         = second (fSimplexVertices &&& simplexBarycenter)
                                        $ V.head tooLongSides
                 lPutStrLn "Plotting a split triangle..."
                 forM_ tooLongS_verts $ \sVtx -> do
                    triangle
                       [ tooLongS_baryCtr, sVtx, vertices!!longSideId ]
              2 -> simplexRenderRefine cfg s
                     $ renderWedge(tooLongSides!0)(tooLongSides!1)
              3 -> completeSubdiv
     4 -> V.forM_ sides $ renderSimplex cfg
     _ -> return()
 where
       vertices = fSimplexVertices s
       lPrint = lPutStrLn . show
       lPutStrLn str = lPutStr str >> lPutStr "\n"
       lPutStr = logTrianglatnRender cfg
       completeSubdiv = simplexRenderRefine cfg s .
              renderTriangulation cfg $ simplexBarycentricSubdivision s
       smallEnough = simplexSmallEnoughPred cfg
       triangle vs = lPrint vs >> triangleRenderer cfg vs
       
       renderWedge :: (Int,Simplex v) -> (Int,Simplex v) -> r()
       renderWedge (li,ls) (ri,rs)
        = renderStripBetween ls (rs, (1-)) 
                 (Just $ if (ri-li)`mod`3 > 1 then 0 else 1)
       
       renderStripBetween :: Simplex v -> (Simplex v, (Int->Int)) -> Maybe Int -> r()
       renderStripBetween baseSide (oppSide, oppOrient) tipsTouch = do
          baseShortEnough <- smallEnough baseSide
          oppShortEnough  <- smallEnough oppSide
          let baseVs = fSimplexVertices baseSide
              oppVs  = fSimplexVertices oppSide
              oppVss = (oppVs!!) . oppOrient
          if baseShortEnough then
            if oppShortEnough then
              case tipsTouch of
               Just ti -> do
                 lPutStrLn "Plotting a triangle tip..."
                 triangle $ oppVss(1-ti) : baseVs
               Nothing -> do
                 lPutStrLn "Plotting a (split) quadrangle..."
                 forM_ [last baseVs, oppVss 0] $
                    triangle . (:[head baseVs, oppVss 1])
             else do
              let oppBaryctr = simplexBarycenter oppSide
              case tipsTouch of
               Just ti -> do
                 lPutStrLn "Plotting a split triangle..."
                 forM_ oppVs $
                    triangle . (:[baseVs!!(1-ti), oppBaryctr])
               Nothing -> do
                 lPutStrLn "Plotting a 3-split quadrangle..."
                 triangle $ oppBaryctr : baseVs
                 forM_ [0,1] $ \i ->
                    triangle [baseVs!!i, oppBaryctr, oppVss i]
           else do
            let baseDivs = sComplexSimplices $ simplexBarycentricSubdivision baseSide
                baseBaryctr = simplexBarycenter baseSide
            if oppShortEnough then
              case tipsTouch of
               Just ti -> do
                 lPutStrLn "Plotting a split triangle..."
                 forM_ baseVs $
                    triangle . (:[oppVss(1-ti), baseBaryctr])
               Nothing -> do
                 lPutStrLn "Plotting a 3-split quadrangle..."
                 triangle $ baseBaryctr : oppVs
                 forM_ [0,1] $ \i ->
                    triangle [baseVs!!i, baseBaryctr, oppVss i]
             else do
              let oppDivs = sComplexSimplices $ simplexBarycentricSubdivision oppSide
              forM_ [0,1] $ \i ->
                 renderStripBetween (baseDivs! i)
                                    (oppDivs ! oppOrient i, id)
                                    (do { i'<-tipsTouch; guard(i==i'); return 0 })
              
   {- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
             (shortEnoughSides, tooLongSides)
                 <- aPartition (smallEnough <<^ snd) $ V.indexed longSides
             case V.length tooLongSides of
              0 | tipsTouch  -> do
                    lPutStrLn "Plotting a triangle tip..."
                    let tVerts = (rayVerts!0!!1) : (rayVerts!1)
                    forM_ tVerts lPrint
                    triangle tVerts
                | otherwise  -> do
                    lPutStrLn "Plotting a (split) quadrangle..."
                    forM_ [0,1] $ \i -> do
                       let tVerts = rayVerts!i!!([invDirections 1,0]!!i) 
                                     : rayVerts!(1-i)
                       lPutStrLn " triangle"; forM_ tVerts lPrint
                       triangle tVerts
              1 -> do
                     let (longSideId, (tooLongS_verts, tooLongS_baryCtr))
                             = second (fSimplexVertices &&& simplexBarycenter)
                                 $ V.head tooLongSides
                         sBase = fSimplexVertices . snd $ V.head shortEnoughSides
                     if tipsTouch then do
                       lPutStrLn "Plotting a split triangle..."
                       lPrint tooLongS_baryCtr
                       forM_ tooLongS_verts $ \sVtx -> do
                          let tVerts = [ tooLongS_baryCtr
                                       , sVtx
                                       , sBase !! ([id, invDirections]!!longSideId $ 1) ]
                          lPutStrLn " triangle"; forM_ tVerts lPrint
                          triangle tVerts
                      else do
                       lPutStrLn "Plotting a 3-split quadrangle..."
                       lPutStrLn " triangle"; lPrint tooLongS_baryCtr; forM_ sBase lPrint
                       triangleRenderer cfg $ tooLongS_baryCtr : sBase
                       forM_ [0,1] $ \i -> do
                          let tVerts = [ tooLongS_baryCtr, sBase!!i
                                       , tooLongS_verts!!invDirections i ]
                          lPutStrLn " triangle"; forM_ tVerts lPrint
                          triangle tVerts
                       
              2 -> do
                    let divisions :: Array(Array(Simplex v))
                        divisions = V.map( sComplexSimplices 
                                         . simplexBarycentricSubdivision) longSides
                        delegate i = V.fromList [divisions!0!invDirections i, divisions!1!i]
                    renderStripBetween (delegate 0) False     id 
                    renderStripBetween (delegate 1) tipsTouch id
        where rayVerts = V.map fSimplexVertices longSides
   -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -}
       
       adjace lsides
         | fst(lsides!1) - fst(lsides!0) `elem` [1, -2] = usides
         | otherwise                          = V.reverse usides
        where usides = V.map snd lsides


aPartition :: Monad r => (Kleisli r a Bool) -> Array a -> r(Array a, Array a) 
aPartition p = liftM((V.map fst***V.map fst) . V.partition snd) 
                 . V.mapM(runKleisli $ id &&& p)
       
       


simplexLength :: (InnerSpace v, s~Scalar v, RealFloat s) => Simplex v -> s
simplexLength(Simplex0 _) = 0
simplexLength(SimplexN bounds inrs)
 | V.length bounds == 2   = magnitude $ getSimplex0(bounds!0) ^-^ getSimplex0(bounds!1)
 | otherwise              = V.maximum $ V.map simplexLength bounds
simplexLength(PermutedSimplex _ s) = simplexLength s


triangViewMain :: (Vertex v, Show v) => 
                         TrianglatnRenderCfg IO v -> Triangulation v -> IO()
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