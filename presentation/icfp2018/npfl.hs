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
import Linear.V2
import Linear.V3
import Math.Rotations.Class (Rotatable, AxisSpace, rotateAbout)

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
            [ trajectoryPlot
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
                                  , (zeroV, V3 0 (-earthSpeed) 0) ) ] 
            , withInteractiveRotation (earthDist,0) earthRadius `id` \iaRotn ->
                colourPaintPlot `id` (\pHelC
                   -> let p@(x,y) = pHelC ^-^ (earthDist, 0)
                          r = magnitude p
                          re = earthRadius
                      in guard (r < re)
                          >> let θ = acos $ y/re
                                 φ = -asin $ x/(sin θ * re)
                             in Just . earthFn . iaRotn $ S²Polar θ φ )
                 <> shapePlot (Dia.lwO 3 . Dia.lc Dia.blue
                      . Dia.moveTo (Dia.p2 (earthDist,0)) $ Dia.circle earthRadius )
            ]
         , unitAspect, xInterval (-earthDist, earthDist)
                     , yInterval (0, earthDist) ]
      , "It's one-dimensional." )
    , (id, "It's two-dimensional.")
    , (id, "It's three-dimensional.")
    , (id, "It's four-dimensional.")
    ]
       
   "What does dimensionality even mean?"
    ====== do
     "“Number of variables needed to define a given state”"
     "“Number of "<>emph"scalars"<>" needed to define a given state”"
           ── do [plaintext|
                    data ℝ = Double
                    data V3 = V3 {x::ℝ, y::ℝ, z::ℝ} |]
                 [plaintext|
                    data S² = S²Polar {θ::ℝ, φ::ℝ} |]
                  ── imageFromFile "img/concepts/polarcoords.svg"

   "Manifolds"
    ====== do
     "A manifold is a topological space "<>𝑀$<>", "
      <>hide("with a set of "<>emph"charts"<>": subsets that cover all of "<>𝑀$<>","
             <>" each of which is homeomorphic to an open ball in a vector space.")
      ── hide' (plotServ $ unitAspect :
                 [ plot [ lineSegPlot [ (sin θ*sin φ, cos θ - 0.1*sin θ*cos φ) 
                                      | disp <- (orig.+^).(dir₁^*)<$>[-20..20]
                                      , magnitudeSq disp < 3
                                      , let S²Polar θ φ = pole .+~^ disp ]
                        | [dir₀, dir₁] <- map(^*0.15)<$>[[V2 1 0, V2 0 1], [V2 0 1, V2 1 0]]
                        , orig <- (dir₀^*)<$>[-20..20] ]
                 | pole <- [S²Polar 0 0, S²Polar pi 0]
                 ] )
          "Example: north- and south hemispheres."

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
   .still-hidden
     visibility: hidden
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

emph :: Presentation -> Presentation
emph = ("emph"#%)

hide :: Presentation -> Presentation
hide = hide' id

hide' :: (Presentation -> Presentation) -> Presentation -> Presentation
hide' f x = do
    "still-hidden"#%x
    "now-visible"#%f x


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

-- | A very rough globe model, representing the continents as circular blobs.
earthFn :: S² -> Dia.Colour ℝ
earthFn p
   = case [ colour
          |  (    loc   ,  size,    colour          ) <-
           [ (  90◯    0,  0.3 , Dia.aliceblue      )  -- Arctic
           , ( -90◯    0,  0.5 , Dia.aliceblue      )  -- Antarctic
           , (  48◯  -86,  0.6 , Dia.forestgreen    )  -- Asia
           , (  50◯  -15,  0.3 , Dia.darkgreen      )  -- Europe
           , (  19◯    0,  0.27, Dia.darkkhaki      )  -- northern Africa
           , (  18◯  -30,  0.32, Dia.khaki          )  -- Middle East
           , ( -13◯  -26,  0.27, Dia.forestgreen    )  -- southern Africa
           , (  46◯  100,  0.5 , Dia.darkolivegreen )  -- North America
           , (  12◯   83,  0.15, Dia.darkgreen      )  -- Middle America
           , (  -9◯   57,  0.4 , Dia.darkgreen      )  -- northern South America
           , ( -37◯   66,  0.2 , Dia.forestgreen    )  -- southern South America
           , ( -25◯ -133,  0.4 , Dia.orange         )  -- Australia
           ]
          , magnitudeSq (p.-~.loc) < size^2 ] of
        (c:_) -> c
        _     -> Dia.midnightblue
 where infix 4 ◯
       lat ◯ lon = S²Polar ((90-lat)*pi/180)
                           (  lon   *pi/180)

withInteractiveRotation :: (Rotatable r, AxisSpace r ~ ℝP²)
  => (ℝ,ℝ) -> ℝ -> ((r -> r) -> DynamicPlottable) -> DynamicPlottable
withInteractiveRotation dragOrigin sphRadius disp = plot $ \(MousePressed mouse) ->
    let (rdx,rdz) = maybe zeroV (^-^dragOrigin) mouse ^/ sphRadius
        axis
         | rdx==0     = HemisphereℝP²Polar (pi/2) (-pi/2)
         | rdx*rdz>0  = HemisphereℝP²Polar (atan $ rdz/rdx) (pi/2)
         | otherwise  = HemisphereℝP²Polar (atan $ -rdz/rdx) (-pi/2)
    in disp $ rotateAbout axis
               (S¹Polar $ magnitude(rdx,rdz) * signum rdx)
