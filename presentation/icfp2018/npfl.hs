-- This work is licensed under the Creative Commons Attribution-NoDerivatives
-- 4.0 International License.
-- To view a copy of this license, visit http://creativecommons.org/licenses/by-nd/4.0/
-- or send a letter to Creative Commons, PO Box 1866, Mountain View, CA 94042, USA.

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes       #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE ImplicitParams    #-}

import Presentation.Yeamer
import Presentation.Yeamer.Maths
import Math.LaTeX.StringLiterals
import qualified Text.Blaze.Html as Blaze
import Text.Cassius

import Data.Semigroup
import Data.Semigroup.Numbered
import Data.List (transpose, inits)
import Control.Arrow ((>>>))
import Control.Monad (guard)

import Data.Manifold.Types
import Data.Manifold.PseudoAffine
import Data.VectorSpace
import Data.VectorSpace.Free
import Math.LinearMap.Category
import Linear.V3

import Graphics.Dynamic.Plot.R2
import qualified Diagrams.Prelude as Dia
import qualified Diagrams.Backend.Cairo as Dia

import System.Environment
import Control.Lens hiding (set)
import Control.Concurrent
import Data.IORef


main :: IO ()
main = do
 newPlotLock <- newIORef Nothing
 let ?plotLock = newPlotLock
 
 yeamer . styling style $ do
   ""──
     "global-title"#%
       "Manifolds as Haskell Types"
     ──
     "Justus Sagemüller"
     ──
     "reference"#%("Institut für Geophysik und Meteorologie"──"Universität zu Köln")
   
   items_p ("What is Earth's dimensionality?"======)
    [ ( plotServ
         [ clickThrough
            [ colourPaintPlot
               $ \p@(x,y)
                   -> let r = magnitude p
                          re = earthDist
                      in guard (r < re)
                          >> let θ = asin $ r/re
                                 φ = atan2 y x
                             in Just . earthFn $ S²Polar θ φ
            , trajectoryPlot
               [("Earth", earthRadius), ("Sun", sunRadius)]
               [ [(xe,ye), (xs, ys)]
               | ((V3 xe ye _, _), (V3 xs ys _, _))
                  <- traject2Body (earthMass                            , sunMass)
                                  ((V3 earthDist 0 0, V3 0 earthSpeed 0), zeroV) ]
            , trajectoryPlot
               [("Earth", earthRadius), ("Sun", sunRadius)]
               [ [(xe,ye), (xs, ys)]
               | ((V3 xe ye _, _), (V3 xs ys _, _))
                  <- traject2Body (sunMass, earthMass)
                                  ( (V3 earthDist 0 0, zeroV)
                                  , (zeroV, V3 0 (-earthSpeed) 0) ) ] ]
         , unitAspect, xInterval (-earthDist, earthDist)
                     , yInterval (0, earthDist) ]
      , "It's one-dimensional." )
    , (id, "It's two-dimensional.")
    , (id, "It's three-dimensional.")
    , (id, "It's four-dimensional.")
    ]
       
   "Manifolds"
    ====== do
     items []


style = [cassius|
   body
     height: 96vh
     color: #ffe
     background: linear-gradient(#263, #516)
     font-size: 6vmin
     font-family: "Linux libertine", "Times New Roman"
   .main-title
     font-size: 180%
   h1
     font-size: 150%
   div
     width: 95%
     height: 100%
     text-align: center
     margin: auto
     border-radius: 6px
     background: rgba(0,0,15,0.1);
   .global-title
     width: 70%
     font-size: 180%
     font-weight: bold
   .headed-container
     height: 80%
   .vertical-concatenation
     display: flex
     flex-direction: column
   .items-list>div
     margin-left: 0px
   .items-list>div>div, .items-list>.list-item
     display: list-item
     margin-left: 2em
     text-align: left
   .list-item
     text-align: left
   .emph
     font-style: italic
   .small
     font-size: 67%
   .verb
     display: inline-block
     font-size: 86%
     background-color: #227
     font-family: "Ubuntu Mono", "Droid Sans mono", "Courier New"
   pre
     text-align: left
     font-size: 86%
     background-color: #204
     font-family: "Ubuntu Mono", "Droid Sans mono", "Courier New"
   .reference, .cited-author
      font-variant: small-caps
  |] ()

items :: [Presentation] -> Presentation

items [] = mempty
items bs = "items-list" #% foldr1 (──) (("list-item"#%)<$>bs)

items_p :: (Presentation -> Presentation)
          -> [(Presentation -> Presentation, Presentation)] -> Presentation
items_p f its = mapM_ (uncurry($))
                $ zip (fmap f <$> id:map fst its)
                      (map (items . map snd) $ inits its)


type Distance = ℝ  -- in m
type Pos = V3 Distance
type Speed = ℝ -- in m/s
type Velo = V3 Speed
type PhaseSpace = (Pos, Velo)
type Mass = ℝ   -- in kg

plotServ :: (?plotLock :: IORef (Maybe ThreadId))
         => [DynamicPlottable] -> Presentation -> Presentation
plotServ pl cont = serverSide`id`do
       locked <- readIORef ?plotLock
       case locked of
        Nothing -> do
         writeIORef ?plotLock . Just
          =<< forkFinally
               (plotWindow pl)
               (\_ -> do
                 stillLocked <- readIORef ?plotLock
                 myId <- myThreadId
                 case stillLocked of
                   Just i | i==myId
                     -> writeIORef ?plotLock Nothing )
        _ -> error "Another plot window is still open."
  >> cont

plotStat :: ViewportConfig -> [DynamicPlottable] -> Presentation
plotStat viewCfg pl = imageFromFileSupplier "png" $ \file -> do
    prerendered <- plotPrerender viewCfg pl
    Dia.renderCairo file
                    (Dia.mkSizeSpec $ Just (fromIntegral $ viewCfg^.xResV)
                               Dia.^& Just (fromIntegral $ viewCfg^.yResV))
                    prerendered

rk4 :: (AffineSpace y, RealSpace (Diff y), t ~ ℝ)
    => (y -> Diff y) -> Diff t -> (t,y) -> [(t,y)]
rk4 f h = go
 where go (t,y) = (t,y) : go
            (t+h, y .+^ h/6 · (k₁ ^+^ 2·k₂ ^+^ 2·k₃ ^+^ k₄))
        where k₁ = f y
              k₂ = f $ y .+^ h/2 · k₁
              k₃ = f $ y .+^ h/2 · k₂
              k₄ = f $ y .+^ h · k₃

trajectoryPlot :: [(String, Distance)] -> [[(ℝ,ℝ)]] -> DynamicPlottable
trajectoryPlot meta = plotLatest
    . map ( transpose . take 80 >>>
           \chunkCompos -> plotMultiple
             [ (if name/="" then legendName name else id)
              $ plot [ lineSegPlot chunkCompo
                     , shapePlot . Dia.moveTo (Dia.p2 $ last chunkCompo)
                             . Dia.opacity 0.6
                         $ Dia.circle radius ]
             | ((name,radius), chunkCompo) <- zip meta chunkCompos ]
           )
    . iterate (drop 20)

type TwoBody = (PhaseSpace, PhaseSpace)

earthMass, sunMass :: Mass
earthMass = 5.972e24  -- in kg
sunMass = 1.988e30    -- in kg

earthDist, sunRadius, earthRadius :: Distance
earthDist = 1.496e11 -- in m
sunRadius = 6.957e8 -- in m
earthRadius = 6.371e6 -- in m

earthSpeed :: Speed
earthSpeed = 29.8e3 -- in m/s

gravConst :: ℝ
gravConst = 6.674e-11  -- in N·m²/kg²

gravAcc :: Mass -> Diff Pos -> Diff Velo
gravAcc mt δx = (gravConst * mt / magnitude δx^3) · δx

traject2Body :: (Mass, Mass) -> TwoBody -> [TwoBody]
traject2Body (me, ms) xv₀ = snd <$>
      rk4 (\((xe,ve), (xs,vs))
            -> ( (ve, gravAcc ms $ xs.-.xe)
               , (vs, gravAcc me $ xe.-.xs) )
               )
          12000
          (0, xv₀)

earthFn :: S² -> Dia.Colour ℝ
earthFn p
   | any (\(loc,size) -> magnitudeSq (p.-~.loc) < size^2)
      [ (S²Polar 1 0, 0.7) ]
                = Dia.darkgreen
   | otherwise  = Dia.midnightblue
