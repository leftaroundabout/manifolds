{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecordWildCards     #-}


module Data.Manifold.Visualisation.R3.GLUT where


import Data.Manifold

import Prelude hiding ((.), id)

import Graphics.Rendering.OpenGL hiding (Triangulation)
import Graphics.UI.GLUT hiding (Triangulation)

import Data.AffineSpace
import Data.VectorSpace

import Control.Monad
import Control.Category
import Control.Arrow

import Control.Monad.IO.Class
import Control.Monad.Trans.Reader

import Data.Maybe

import Data.Vector ((!))
import qualified Data.Vector as V

import Data.IORef

import Data.Time.Clock

import System.Exit
import System.Random
import Control.Monad.Random


-- instance Random GLfloat where
--   randomR r = first(realToFrac :: Double->GLfloat) . randomR r
--   random = first(realToFrac :: Double->GLfloat) . random

instance Random (Color3 GLfloat) where
  random = runRand $ fmap(\(r:g:b:_) -> Color3 (n r) (n g) (n b)) getRandoms
   where n = (+1/2) . (/2)


data TrianglatnRenderCfg rendMonad vertex = TrianglatnRenderCfg
       { simplexSmallEnoughPred :: Simplex vertex -> rendMonad Bool
       -- ^ 'True' if the simplex is sufficiently small (or obscured-from-sight, etc.)
       --  to be rendered as a straight line/triangle/tetrahedron...
       , triangleRenderer  :: vertex -> vertex -> vertex -> rendMonad()
       , edgeRenderer     ::  vertex -> vertex           -> rendMonad()
       , simplexRenderRefine :: Simplex vertex -> rendMonad () -> rendMonad ()
       , logTrianglatnRender :: String -> rendMonad()
       }



stdEdgeRenderer :: (Vertex v, MonadIO r) => v -> v -> r()
stdEdgeRenderer v₀ v₁ = liftIO $ do
    faceColor <- get currentColor
    color $ Color3 (0.7::GLfloat) 0.7 0.7
    renderPrimitive Lines $ do{vertex v₀; vertex v₁}
    color faceColor


stdTriangleRenderer :: (Vertex v, Color v, MonadIO r)
          => v -> v -> v -> r()
stdTriangleRenderer v₀ v₁ v₂ 
   = liftIO . renderPrimitive Triangles $ do
       color v₀; vertex v₀
       color v₁; vertex v₁
       color v₂; vertex v₂
       

randColTriangleRenderer :: (Vertex v, MonadIO r)
               => v -> v -> v -> r()
randColTriangleRenderer v₀ v₁ v₂ = liftIO $ do
    color =<< (randomIO :: IO(Color3 GLfloat))
    renderPrimitive Triangles $ do
       vertex v₀; vertex v₁; vertex v₂


stdShadableTriangleRenderer, randColShadableTriangleRenderer 
      :: (Vertex v, MonadIO r)
              => (v->Color3 GLfloat) -> v -> v -> v -> r()
              
stdShadableTriangleRenderer shf = genShadableTriangleRenderer shf (Color3 0.6 0.6 0.6)


randColShadableTriangleRenderer shf v₀ v₁ v₂ = liftIO $ do
    colour <- randomIO
    genShadableTriangleRenderer shf colour v₀ v₁ v₂

genShadableTriangleRenderer :: (Vertex v, MonadIO r)
              => (v->Color3 GLfloat) -> Color3 GLfloat -> v -> v -> v -> r()
genShadableTriangleRenderer shf (Color3 r g b) v₀ v₁ v₂ = liftIO $ do
    renderPrimitive Triangles $ forM_ [v₀,v₁,v₂] $ \v -> do
       let (Color3 r' g' b') = shf v
       color $ Color3 (r*r') (g*g') (b*b')
       vertex v

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

renderSimplex cfg@(TrianglatnRenderCfg {..}) s@(SimplexN sides _) = do
    allSmallEnough <- smallEnough s
    case V.length sides of
     1 -> return()
     2 | allSmallEnough -> do
              lPutStrLn "Plotting a line..."; lPrint vertices
              let[v0,v1]=vertices in edgeRenderer v0 v1
       | otherwise -> completeSubdiv 
     3 {-| allSmallEnough -> do
           lPutStrLn "Plotting a triangle..."
           triangle vertices
       | otherwise -} -> do
           (shortEnoughSides, tooLongSides)
                   <- aPartition (Kleisli smallEnough <<^ snd) $ V.indexed sides
           case V.length tooLongSides of
              0 -> do
                 lPutStrLn "Plotting a triangle..."
                 triangle vertices
              1 -> do
                 lPutStrLn "Plotting a split triangle..."
                 uncurry (renderSplitTriangle . (vertices!!)) $ V.head tooLongSides
--                  let (longSideId, (tooLongS_verts, tooLongS_baryCtr))
--                          = second (fSimplexVertices &&& simplexBarycenter)
--                                         $ V.head tooLongSides
--                  lPutStrLn "Plotting a split triangle..."
--                  forM_ tooLongS_verts $ \sVtx -> do
--                     triangle
--                        [ tooLongS_baryCtr, sVtx, vertices!!longSideId ]
              2 -> simplexRenderRefine s
                     $ renderWedge(tooLongSides!0)(tooLongSides!1)
              _ -> completeSubdiv
     4 -> V.forM_ sides $ renderSimplex cfg
     _ -> return()
 where
       vertices = fSimplexVertices s
       lPrint = lPutStrLn . show
       lPutStrLn str = lPutStr str >> lPutStr "\n"
       lPutStr = logTrianglatnRender
       completeSubdiv = simplexRenderRefine s .
              renderTriangulation cfg $ simplexBarycentricSubdivision s
       smallEnough = simplexSmallEnoughPred
       triangle vs = lPrint vs >> let[v0,v1,v2]=vs in triangleRenderer v0 v1 v2
       
       renderConeTriangle, renderSplitTriangle :: v -> Simplex v -> r()
       
       renderConeTriangle headv base = do
          isSimple <- smallEnough base
          if isSimple then triangle $ headv : fSimplexVertices base
           else renderSplitTriangle headv base
             
       renderSplitTriangle headv base
          = V.forM_ baseDivs $ \bdiv -> renderConeTriangle headv bdiv
        where baseDivs = sComplexSimplices $ simplexBarycentricSubdivision base
          
       
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
             else do -- not oppShortEnough
              case tipsTouch of
               Just ti -> do
                 lPutStrLn "Plotting a split triangle..."
                 renderSplitTriangle (baseVs!!(1-ti)) oppSide
               Nothing -> do
                 let oppBaryctr = simplexBarycenter oppSide
                     oppDivs = sComplexSimplices $ simplexBarycentricSubdivision oppSide
                 lPutStrLn "Plotting a multi-split quadrangle..."
                 triangle $ oppBaryctr : baseVs
                 forM_ [0,1] $ \i ->
                    renderConeTriangle (baseVs!!i) (oppDivs ! oppOrient i)
           else do -- not baseShortEnough
            let baseDivs = sComplexSimplices $ simplexBarycentricSubdivision baseSide
                baseBaryctr = simplexBarycenter baseSide
            if oppShortEnough then
              case tipsTouch of
               Just ti -> do
                 lPutStrLn "Plotting a split triangle..."
                 renderSplitTriangle (oppVss $ 1-ti) baseSide
               Nothing -> do
                 lPutStrLn "Plotting a multi-split quadrangle..."
                 triangle $ baseBaryctr : oppVs
                 forM_ [0,1] $ \i ->
                    renderConeTriangle (oppVss i) (baseDivs ! i)
             else do -- not oppShortEnough
              let oppDivs = sComplexSimplices $ simplexBarycentricSubdivision oppSide
              forM_ [0,1] $ \i ->
                 renderStripBetween (baseDivs! i)
                                    (oppDivs ! oppOrient i, id)
                                    (do { i'<-tipsTouch; guard(i==i'); return 0 })
              


aPartition :: Monad r => (Kleisli r a Bool) -> Array a -> r(Array a, Array a) 
aPartition p = liftM((V.map fst***V.map fst) . V.partition snd) 
                 . V.mapM(runKleisli $ id &&& p)
       
       


simplexLength :: (InnerSpace v, s~Scalar v, RealFloat s) => Simplex v -> s
simplexLength(Simplex0 _) = 0
simplexLength(SimplexN bounds inrs)
 | V.length bounds == 2   = magnitude $ getSimplex0(bounds!0) ^-^ getSimplex0(bounds!1)
 | otherwise              = V.maximum $ V.map simplexLength bounds
simplexLength(PermutedSimplex _ s) = simplexLength s

simplexViewLength :: Simplex (Vertex3 GLfloat) -> GLfloat
simplexViewLength = simplexLengthBy $
    \(Vertex3 x₀ y₀ _)(Vertex3 x₁ y₁ _)
        -> let xd = x₁-x₀; yd = y₁-y₀
           in sqrt $ xd*xd + yd*yd 

simplexLengthBy :: RealFloat l => (v->v->l) -> Simplex v -> l
simplexLengthBy _ (Simplex0 _) = 0
simplexLengthBy lfn s@(SimplexN bounds _)
 | V.length bounds == 2   = let [v₀, v₁] = fSimplexVertices s
                            in  lfn v₀ v₁
 | otherwise              = V.maximum $ V.map (simplexLengthBy lfn) bounds
simplexLengthBy lfn (PermutedSimplex _ s) = simplexLengthBy lfn s


-- data SceneRotation = SceneRotation
--    { defRotationAxis :: Vector3 GLfloat
--    , rotationSpeed

data GLSceneConfig = GLSceneConfig
    { enableLighting :: Bool
    }

defOrthoSceneCfg :: GLSceneConfig
defOrthoSceneCfg = GLSceneConfig False



data VisualisationRTInfo = VisualisationRTInfo 
  { totalVisRuntime, timeSinceLastFrame :: NominalDiffTime
  }

type VisualisationRT = ReaderT VisualisationRTInfo IO

askTotalVisRuntime, askTimeSinceLastFrame :: VisualisationRT NominalDiffTime
askTotalVisRuntime = fmap totalVisRuntime ask
askTimeSinceLastFrame = fmap timeSinceLastFrame ask


glViewMain :: GLSceneConfig -> VisualisationRT() -> IO()
glViewMain _ render = do 
    (progname, _) <- getArgsAndInitialize
    createWindow "A simple view of a triangulation"
    
    initialDisplayMode $= [WithDepthBuffer, DoubleBuffered]
    
    globFrameCount <- newIORef (0 :: Int)
    
    pausedTime <- newIORef (Nothing :: Maybe UTCTime)
    [ttlRunTime, maxFrameWait] <- mapM newIORef [0, 0 :: NominalDiffTime]
    lastFrameTime <- newIORef =<< getCurrentTime
    
    reshapeCallback $= Just (\(Size w h) ->
         viewport $= (Position (fromIntegral $ (w-h)`div`2) 0, Size h h)
       )
    
    depthFunc $= Just Less
    
    let printExitInfo = do
         ttframes <- readIORef globFrameCount
         tttime <- readIORef ttlRunTime
         latency <- readIORef maxFrameWait
         putStrLn $ "Displayed a total of "++show ttframes++" frames during "
                  ++show tttime++" of active runtime"
         putStrLn $ " (average "++take 4(show $ fromIntegral ttframes/realToFrac tttime)++" FPS,"
                  ++ " latency "++show latency++")."
       
    closeCallback $= Just printExitInfo
    
    keyboardMouseCallback $= (Just $ \key state modifiers position ->
       case (key, state) of
         (Char '\ESC', Down) -> printExitInfo >> exitSuccess
         (Char ' ', Down)    -> do
            pausedAt <- readIORef pausedTime
            case pausedAt of
             Just tp -> do
                writeIORef lastFrameTime =<< getCurrentTime
                writeIORef pausedTime Nothing
             Nothing -> writeIORef pausedTime . Just =<< getCurrentTime
         _                   -> return ()
      )
    
    
    
    displayCallback $= do 
         paused <- readIORef pausedTime
         when(isNothing paused) $ do
            clear [ColorBuffer, DepthBuffer]
            color $ Color3 (0.3::GLfloat) 0.3 0.3
            
            timeNow <- getCurrentTime
            timeLF <- readIORef lastFrameTime
            let thisΔt = timeNow`diffUTCTime`timeLF
            modifyIORef ttlRunTime (+thisΔt)
            writeIORef lastFrameTime timeNow
            modifyIORef maxFrameWait $ max thisΔt
            
            ttlRT <- readIORef ttlRunTime
            
            preservingMatrix .
              runReaderT render $ VisualisationRTInfo
                { totalVisRuntime = ttlRT
                , timeSinceLastFrame = thisΔt }
            
            swapBuffers
            
            modifyIORef globFrameCount (+1)
       
    idleCallback $= Just (postRedisplay Nothing)
    
    windowSize $= Size 480 480
    
  
--     when enableLighting $ do
--        lighting $= Enabled
--        normalize $= Enabled
--        position (Light 0) $= Vertex4 10000 4000 8000  1
--        diffuse (Light 0) $= Color4 1 1 1 1
--        light (Light 0) $= Enabled
    
    mainLoop
         


         


class TriangleHasNormal v where
  type TriangleNormal v :: *
  unnormldTriangleNormal  :: v -> v -> v -> TriangleNormal v
  triangleNormal :: v -> v -> v -> TriangleNormal v

instance (Floating a) => TriangleHasNormal (Vertex3 a) where
  type TriangleNormal (Vertex3 a) = Normal3 a
  unnormldTriangleNormal (Vertex3 x₀ y₀ z₀) (Vertex3 x₁ y₁ z₁) (Vertex3 x₂ y₂ z₂)
    = Normal3 (yΔ₁ * zΔ₂ - zΔ₁ * yΔ₂) (zΔ₁ * xΔ₂ - xΔ₁ * zΔ₂) (xΔ₁ * yΔ₂ - yΔ₁ * xΔ₂)
   where xΔ₁ = x₁-x₀; xΔ₂ = x₂-x₀; yΔ₁ = y₁-y₀; yΔ₂ = y₂-y₀; zΔ₁ = z₁-z₀; zΔ₂ = z₂-z₀
  triangleNormal v₀ v₁ v₂ = Normal3 (x*n) (y*n) (z*n)
   where (Normal3 x y z) = unnormldTriangleNormal v₀ v₁ v₂
         n = 1/sqrt(x*x + y*y + z*z)
   


data CleverGLvertex vert extraInfo
       = CleverGLvertex { vertexP :: !vert
                        , vExtraInfo :: !extraInfo }
             deriving(Eq, Show)

instance (Vertex vert) => Vertex (CleverGLvertex vert ei) where
  vertex (CleverGLvertex v _) = vertex v
instance (Color colour) => Color (CleverGLvertex vt colour) where
  color (CleverGLvertex _ c) = color c
instance (Normal normal) => Normal (CleverGLvertex vt normal) where
  normal (CleverGLvertex _ n) = normal n


-- data BrcDiffLimits = BrcDiffLimits
--       { 

cleverGLvertex_brcDiffLimit :: ( RealFloat f, InnerSpace f, f~Scalar f
                               , AffineSpace propty, d~Diff propty
                               , VectorSpace d, Fractional(Scalar d) )
                                => f -> (d -> Bool)
                         -> Simplex(CleverGLvertex (Vertex3 f) propty) -> Bool
cleverGLvertex_brcDiffLimit brcOffLim propDiffPred s = posOk && proptyOk
 where (CleverGLvertex (Vertex3 brcx brcy _) brcPropty)
             = simplexBarycenter s
       
       splVerts = fSimplexVertices s
       n = length splVerts
       
       proptyOk = propDiffPred avgOff
        where avgOff = foldr addup zeroV splVerts ^* recip (fromIntegral n)
              addup(CleverGLvertex _ p) p' = (p .-. brcPropty) ^+^ p'
       
       posOk 
          | n==3       = brcInside3
          | otherwise  = offDistSq < brcOffLim*brcOffLim
        where brcInside3 = α>0 && α<1 && β>0 && β<1
               where [p₀,p₁,p₂] = pPoints
                     v₁ = p₁ ^-^ p₀; v₂ = p₂ ^-^ p₀
                     vᵣ = brcP ^-^ p₀
                     α = ( ρ₂₂ * κ₁ - ρ₁₂ * κ₂ ) / τ
                     β = ( ρ₁₁ * κ₂ - ρ₁₂ * κ₁ ) / τ
                     τ = ρ₁₁ * ρ₂₂ - ρ₁₂ * ρ₁₂
                     ρ₁₁ = v₁<.>v₁; ρ₁₂ = v₁<.>v₂; ρ₂₂ = v₂<.>v₂
                     κ₁ = vᵣ<.>v₁; κ₂ = vᵣ<.>v₂
              brcP = (brcx,brcy)
              pPoints = map (\(CleverGLvertex (Vertex3 x y _) _) -> (x,y)) splVerts
              pBrc@(pbx,pby) = midBetween pPoints
              offDistSq = magnitudeSq $ brcP ^-^ pBrc
       
       
          
--   = simplexLength(fmap vertexP s) <= maxLength
--    && simplexLength(fmap (\(CleverGLvertex _ (propty3 r _ _)) -> r) s) <= maxColourDiff
--    && simplexLength(fmap (\(ColourGLvertex _ (Color3 _ g _)) -> g) s) <= maxColourDiff
--    && simplexLength(fmap (\(ColourGLvertex _ (Color3 _ _ b)) -> b) s) <= maxColourDiff
