-- This work is licensed under the Creative Commons Attribution-NoDerivatives
-- 4.0 International License.
-- To view a copy of this license, visit http://creativecommons.org/licenses/by-nd/4.0/
-- or send a letter to Creative Commons, PO Box 1866, Mountain View, CA 94042, USA.

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes       #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE ImplicitParams    #-}
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE Rank2Types        #-}
{-# LANGUAGE UnicodeSyntax     #-}

import Presentation.Yeamer
import Presentation.Yeamer.Maths
import Math.LaTeX.StringLiterals
import qualified Text.Blaze.Html as Blaze
import Text.Hamlet
import Text.Cassius

import Data.Semigroup
import Data.Semigroup.Numbered
import Data.List (transpose, inits, partition)
import Control.Arrow ((>>>), (&&&), first, second)
import Control.Monad (guard)

import Data.Manifold.Types
import Data.Manifold.PseudoAffine
import Data.Manifold.FibreBundle
import Data.VectorSpace
import Data.VectorSpace.Free
import Math.LinearMap.Category
import Math.Manifold.Embedding.Simple.Class
import Linear.V2
import Linear.V3
import Math.Rotations.Class (Rotatable, AxisSpace, rotateAbout, zAxis)

import Graphics.Dynamic.Plot.R2
import qualified Diagrams.Prelude as Dia
import qualified Diagrams.Backend.Cairo as Dia
import Diagrams.Prelude (p2)

import System.Environment
import Control.Lens hiding (set)
import Control.Concurrent
import Data.IORef
import Text.Printf (printf)
import GHC.Exts (IsString(fromString))


main :: IO ()
main = do
 newPlotLock <- newIORef Nothing
 let ?plotLock = newPlotLock
 
 yeamer . styling style $ do
   ""──
     "global-title"#%
       "Numerical Algorithms Based on a Naïve “Pseudo-Affine” Abstraction"
     ──
     "Justus Sagemüller"
     ──
     "reference"#%("Institut für Geophysik und Meteorologie"──"Universität zu Köln")
   
   "Magnetohydrodynamics"
    ====== do
     ""
   
   "The idea of a pseudo-affine space"
    ====== do
     "Within each chart, the manifold can be described as a vector space."
      ── do
       let vsClass = [plaintext|
              class VectorSpace v where
                type Scalar v :: *
                (⨣) :: v -> v -> v
                (·^) :: Scalar v -> v -> v
             |]
       vsClass
       vsClass──[plaintext|
              instance VectorSpace (ℝ,ℝ,ℝ) where
                type Scalar (ℝ,ℝ,ℝ) = ℝ
                (x₀,y₀,z₀) ⨣ (x₁,y₁,z₁) = (x₀+x₁, y₀+y₁, z₀+z₁)
                μ ·^ (x,y,z) = (μ*x, μ*y, μ*z)
             |]
       vsClass
         ── law[plaintext|(u ⨣ v) ⨣ w ≡ u ⨣ (v ⨣ w)  |]
         ── law[plaintext|u ⨣ v       ≡ v ⨣ u        |]
         ── law[plaintext|(λ+μ)·v     ≡ λ·v ⨣ μ·v    |]
     "Globally, the manifold is not a vector space. But around each point?"
      ── do
       do [plaintext|
              class VectorSpace (Diff p) => AffineSpace p where
                type Diff p :: *
                (.-.) :: p -> p -> Diff p
                (.+^) :: p -> Diff p -> p
             |]
          [plaintext|
              class VectorSpace (Needle p) => PseudoAffine p where
                type Needle p :: *
                (.-~.) :: p -> p -> Needle p
                (.+~^) :: p -> Needle p -> p
             |]
         ── do
          [plaintext|
              instance AffineSpace (ℝ,ℝ) where
                type Diff (ℝ,ℝ) = (ℝ,ℝ)
                (x₀,y₀) .-. (x₁,y₁) = (x₀-x₁, y₀-y₁)
                (x, y)  .+^ (δx,δy) = (x+δx , y+δy )
             |]
          law   [plaintext|p .-. p         ≡ 0̂              |]
           ──law[plaintext|p .+^ (q .-. p) ≡ q              |]
           ──law[plaintext|p .+^ (v ⨣ w)   ≡ (p .+^ v) .+^ w|]
          law   [plaintext|p .-~. p        ≡ 0̂              |]
           ──law[plaintext|p .+~^(q .-~.p) ≡ q              |]
           ── do
             law[plaintext|p .+~^(v ⨣ w)   ‡ (p .+~^v) .+^ w|]
             law[plaintext|v ↦ p.+~^v   should be continuous|]
      
   "The 1-sphere"
    ====== do
     let circCtr = (-1.5, -1.2)
     plotServ [ let plPts :: (S¹, S¹) -> DynamicPlottable
                    plPts (p,q) = plotMultiple
                      [ legendName "𝑆¹" . shapePlot . Dia.moveTo (p2 circCtr)
                       . Dia.fcA Dia.transparent $ Dia.circle 1
                      , legendName (printf "q.-~.p = %.2f" v)
                         $ lineSegPlot [ case embed (p .+~^ η*^v :: S¹) of
                                           V2 x y -> circCtr .+^ 1.02*^(x,y)
                                       | η <- [0,0.05..1] ]
                          <> shapePlot
                             (Dia.arrowBetween (Dia.P zeroV) (p2 (v+1e-3,0)))
                      , mconcat [ diagramPlot $ Dia.text t
                                  & Dia.scale 0.15
                                  & Dia.fc Dia.white
                                  & Dia.moveTo loc
                                | (t, loc) <- [ ("q", p2 circCtr.+^embed q^*1.12)
                                              , ("p", p2 circCtr.+^embed p^*0.88) ] ] ]
                     where v = q .-~! p
                in mouseInteractive
                       (\ev -> (if magnitude (p2 circCtr .-. p2 (ev^.clickLocation)) < 1
                                 then first else second)
                              . const . coEmbed . (.-.p2 circCtr) . p2
                                   $ ev^.releaseLocation)
                       (S¹Polar 0, S¹Polar 0) plPts
              , unitAspect, xInterval (-pi, pi), dynamicAxes ]
      [plaintext|
        data S¹ = S¹Polar { φ :: ℝ  {- actually, only ⌊-π,π⌈ -} }
        
        instance PseudoAffine S¹ where
          type Needle S¹ = ℝ
          S¹Polar φ₁ .-~. S¹Polar φ₀
             | δφ > pi     = δφ - (2*pi)
             | δφ < (-pi)  = δφ + (2*pi)
             | otherwise   = pure δφ
           where δφ = φ₁ - φ₀
          S¹Polar φ₀ .+~^ δφ  = S¹Polar $ φ'
           where φ' = (φ₀ + δφ) `mod'` (2*pi)
       |]
     plotServ [ let plPts :: S¹ -> DynamicPlottable
                    plPts p = plotMultiple
                      [ legendName "𝑆¹" . shapePlot . Dia.moveTo (p2 circCtr)
                       . Dia.fcA Dia.transparent $ Dia.circle 1
                      , legendName "q.-~.p"
                       . shapePlot $ mconcat
                          [ (Dia.text (printf "%.1f" δ)
                                  & Dia.scale (importance / 15)
                                  & Dia.moveTo loc'')
                             <> Dia.fromVertices [loc, loc']
                                  & Dia.opacity (1 / (1 + δ^2/2))
                          | δ <- [-3, -2.8 .. 3]
                          , let importance = cos (δ*pi)^4 + 0.5
                                q = p.+~^δ :: S¹
                                [loc,loc',loc'']
                                  = [ p2 circCtr.+^embed q
                                       ^*(1 - (-1)^^(round $ δ*5)*roff)
                                    | roff <- [0, (importance+0.5)/25, importance/8] ]
                          ]
                      , mconcat [ diagramPlot $ Dia.text t
                                  & Dia.scale 0.15
                                  & Dia.fc Dia.white
                                  & Dia.moveTo loc
                                | (t, loc) <- [ ("p", p2 circCtr.+^embed p^*1.12) ] ] ]
                in mouseInteractive
                       (\ev -> const . coEmbed . (.-.p2 circCtr) . p2
                                   $ ev^.releaseLocation)
                       (S¹Polar 0) plPts
              , unitAspect, xInterval (-pi, 1) ]
      [plaintext|
        data S¹ = {- The abstract circle -}
        
        instance PseudoAffine S¹ where
          type Needle S¹ = ℝ
          p .-~. q = {- rotate the origin to
                       p and read off the
                       position of q. Use
                       its azimuth as the distance. -}
          p .+~^ δ  = {- set q up at the azimuth δ,
                        then rotate circle so the
                        origin moves to p. -}
       |]
   
   "The 2-torus"
    ====== do
     let torusCtr = V3 (-1.5) 0 (-1.2)
         viewAngle = 0.2
         wiremeshResolution = 9
     plotServ [ let embedding (S¹Polar α, S¹Polar β)
                      = let thickness = 1/4
                            r = 1 + cos β*thickness
                        in V3 (r*cos α) (r*sin α) (sin β*thickness)
                    viewProjection (V3 x y z)
                      = (x, sin viewAngle * y + cos viewAngle * z)
                    torusProject p = viewProjection $ torusCtr .+^ embedding p
                    plPts :: T² -> T² -> DynamicPlottable
                    plPts p₀ p₁ = plotMultiple
                      [ legendName "𝑇²" $ plot
                         [ tweakPrerendered (Dia.opacity 0.3) $ lineSegPlot
                            [ torusProject ((S¹Polar 0,S¹Polar 0).+~^disp)
                            | disp <- (orig.+^).(dir₁^*)
                                <$>[-wiremeshResolution..wiremeshResolution] ]
                         | [dir₀, dir₁] <- map(^*(pi/wiremeshResolution))
                                             <$>[ [(1,0), (0,1)]
                                                , [(0,1), (1,0)] ]
                         , orig <- (dir₀^*)<$>[-wiremeshResolution..wiremeshResolution] ]
                      , legendName (printf "p.-~.q = (%.1f,%.1f)" (fst v) (snd v))
                         $ (lineSegPlot [ viewProjection
                                          $ torusCtr .+^ embedding (p₀ .+~^ η*^v)
                                       | η <- [0,0.05..1] ]
                             & tweakPrerendered (Dia.lwO 3))
                          <> shapePlot
                             (Dia.arrowBetween (Dia.P zeroV) (Dia.p2 v))
                      , mconcat [ diagramPlot $ Dia.text t
                                  & Dia.scale 0.15
                                  & Dia.fc Dia.white
                                  & Dia.moveTo loc
                                | (t, loc) <- [ ("q", Dia.p2 $ torusProject p₀)
                                              , ("p", Dia.p2 $ torusProject p₁) ] ] ]
                     where v = p₁ .-~! p₀
                in plotLatest
                     [ plPts (S¹Polar 0.+~^x₀, S¹Polar 0.+~^y₀)
                             (S¹Polar 0.+~^x₁, S¹Polar 0.+~^y₁)
                     | [x₀,y₀,x₁,y₁] <- tail
                          $ foldr (zipWith (:) . enumFromThen 0) (repeat [])
                                         [0.02, 1/17, -pi/39, 0.01] ]
              , unitAspect, xInterval (-pi, pi), dynamicAxes ] $
      "... or "<>emph"any"<>" cartesian product space:"
       <>maths[[ 𝑇◝2 ⩵ 𝑆◝1 × 𝑆◝1 ]]""
        <>
       [plaintext|
        instance (PseudoAffine x, PseudoAffine y) => PseudoAffine (x,y) where
          type Needle (x,y) = (Needle x, Needle y)
          (x₁,y₁) .-~. (x₀,y₀) = (x₁.-~.x₀, y₁.-~.y₀)
          (x₁,y₁) .+~^ (x₀,y₀) = (x₁.+~^x₀, y₁.+~^y₀)
       |]
      

style = [cassius|
   body
     height: 96vh
     color: #ffe
     background: linear-gradient(#263, #516)
     font-size: 5vmin
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
   .laweqn pre
     background-color: #422
   .reference, .cited-author
      font-variant: small-caps
   a.pseudolink
      text-decoration: underline
      color: #7090ff
  |] ()

items :: [Presentation] -> Presentation

items [] = " "
items bs = "items-list" #% foldr1 (──) (("list-item"#%)<$>bs)

items_p :: (Presentation -> Presentation)
          -> [(Presentation -> Presentation, Presentation)] -> Presentation
items_p f its = mapM_ (uncurry($))
                $ zip (fmap f <$> id:map fst its)
                      (map (items . map snd) $ inits its)

emph :: Presentation -> Presentation
emph = ("emph"#%)

urlRef :: String -> Presentation
urlRef s = staticContent [shamlet|<a .pseudolink>#{s}|]

law :: Presentation -> Presentation
law = ("laweqn"#%)

hide :: Presentation -> Presentation
hide = hide' id

hide' :: (Presentation -> Presentation) -> Presentation -> Presentation
hide' f x = do
    "still-hidden"#%x
    "now-visible"#%f x

verb :: String -> Presentation
verb s = "verb" #% fromString s

type Distance = ℝ  -- in m
type Pos = V3 Distance
type Speed = ℝ -- in m/s
type Velo = V3 Speed
type PhaseSpace = (Pos, Velo)
type Mass = ℝ   -- in kg
type PhaseSpace_ConsE = (Pos, S²)

type T² = (S¹, S¹)

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

opac :: Double -> DynamicPlottable -> DynamicPlottable
opac = tweakPrerendered . Dia.opacity


type ODESolver = ∀ y t . (PseudoAffine y, RealSpace (Needle y), t ~ ℝ, Interior y ~ y)
    => (y -> Needle y) -> Needle t -> (t,y) -> [(t,y)]

euler :: ODESolver
euler f h = go
 where go (t,y) = (t,y) : go (t+h, y .+~^ h · f y)

rk4 :: ODESolver
rk4 f h = go
 where go (t,y) = (t,y) : go
            (t+h, y .+~^ h/6 · (k₁ ^+^ 2·k₂ ^+^ 2·k₃ ^+^ k₄))
        where k₁ = f y
              k₂ = f $ y .+~^ h/2 · k₁
              k₃ = f $ y .+~^ h/2 · k₂
              k₄ = f $ y .+~^ h · k₃

trajectoryPlot :: Int -> [(String, Distance)] -> [[(ℝ,ℝ)]] -> DynamicPlottable
trajectoryPlot speed meta = plotLatest
    . map ( transpose . take 80 >>>
           \chunkCompos -> plotMultiple
             [ (if name/="" then legendName name else id)
              $ plot [ lineSegPlot chunkCompo
                     , shapePlot . Dia.moveTo (p2 $ last chunkCompo)
                             . Dia.opacity 0.6
                         $ Dia.circle radius ]
             | ((name,radius), chunkCompo) <- zip meta chunkCompos ]
           )
    . iterate (drop speed)

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

traject2Body :: ODESolver -> (Mass, Mass) -> TwoBody -> [TwoBody]
traject2Body solver (me, ms) xv₀ = snd <$>
   solver (\((xe,ve), (xs,vs))
            -> ( (ve, gravAcc ms $ xs.-.xe)
               , (vs, gravAcc me $ xe.-.xs) )
               )
          120000
          (0, xv₀)

data SymplecticOperability = SymplecticWorking | BrownMotionBroken

traject1Body_ConsE :: ODESolver -> SymplecticOperability
                        -> Mass -> PhaseSpace -> [PhaseSpace_ConsE]
traject1Body_ConsE solver okness ms (x₀,v₀) = snd <$>
   solver (\(xe,veDir)
            -> let absv = sqrt $ 2*(energy - epot xe)
                   accTn:@._ = coEmbed ( gravAcc ms (negateV xe)
                                         ^/(case okness of
                                             SymplecticWorking -> absv
                                             BrownMotionBroken -> 1):@. embed veDir
                                           :: TangentBundle ℝ³ )
                                 :: TangentBundle S²
               in (absv*^embed veDir, accTn)
               )
          120000
          (0, (x₀, coEmbed v₀))
 where energy = epot x₀ + 1/2*magnitudeSq v₀
       epot x = -gravConst*ms/magnitude x

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
