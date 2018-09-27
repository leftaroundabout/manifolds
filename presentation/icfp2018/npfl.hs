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
import Control.Arrow ((>>>), (&&&), second)
import Control.Monad (guard)

import Data.Manifold.Types
import Data.Manifold.PseudoAffine
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

import System.Environment
import Control.Lens hiding (set)
import Control.Concurrent
import Data.IORef
import Text.Printf (printf)


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
            [ trajectoryPlot 2
               [("Earth", earthRadius), ("Sun", sunRadius)]
               [ [(xe,ye), (xs, ys)]
               | ((V3 xe ye _, _), (V3 xs ys _, _))
                  <- traject2Body rk4 (earthMass                            , sunMass)
                                      ((V3 earthDist 0 0, V3 0 earthSpeed 0), zeroV) ]
            , trajectoryPlot 2
               [("Earth", earthRadius), ("Sun", sunRadius)]
               [ [(xe,ye), (xs, ys)]
               | ((V3 xe ye _, _), (V3 xs ys _, _))
                  <- traject2Body rk4 (sunMass, earthMass)
                                      ( (V3 earthDist 0 0, zeroV)
                                      , (zeroV, V3 0 (-earthSpeed) 0) ) ] 
            , withInteractiveRotation (earthDist,0) earthRadius `id` \iaRotn ->
                colourPaintPlot `id` (\pHelC
                   -> let p@(x,y) = pHelC ^-^ (earthDist, 0)
                          r = magnitude p
                          re = earthRadius
                      in guard (r < re)
                          >> let ϑ = acos $ y/re
                                 φ = -asin $ x/(sin ϑ * re)
                             in Just . earthFn . iaRotn $ S²Polar ϑ φ )
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
                    data ℝ³ = ℝ³ {x::ℝ, y::ℝ, z::ℝ} |]
                 mapM_ (──imageFromFile "img/concepts/polarcoords.svg")
                  [ [plaintext|
                    data S² = S²Polar {ϑ::ℝ, φ::ℝ} |]
                  , [plaintext|
                    data S² = S²Polar {ϑ::⌊0,π⌉, φ::⌊-π,π⌉} |]
                  , plotServ [ diagramPlot . Dia.lc Dia.white
                                 $ Dia.circle 1
                                  <> Dia.fromVertices (Dia.p2 . (,0)<$>[-1,1])
                                  <> Dia.fromVertices (Dia.p2 . (0,)<$>[-1,1])
                             , plot $ \(MousePressed mouse)
                                -> case mouse of
                                     Just (x,z) | x^2+z^2 < 1
                                      -> let ϑ = acos z
                                             φ = asin $ x/sin ϑ
                                         in legendName (printf "ϑ = %.2f, φ = %.2f" ϑ φ)
                                              $ lineSegPlot [zeroV, (x,z)]
                                               <> shapePlot (Dia.ellipseXY (sin φ) 1
                                                              & Dia.fcA Dia.transparent)
                                     _ -> mempty
                             , unitAspect ]
                    [plaintext|
                    data S² = S²Polar { ϑ::⌊0,π⌉, φ :: ⌊-π,π⌉ unless ϑ≡0 or ϑ≡π } |]
                  ]

   "Manifolds"
    ====== do
     "A manifold is a topological space "<>𝑀$<>", "
      <>hide("with a set of "<>emph"charts"<>": subsets that cover all of "<>𝑀$<>","
             <>" each of which is homeomorphic to an open ball in a vector space.")
      ──mapM_ (\(charts, rChart, caption) -> do
         let viewAngle = 0.2
         hide' (plotServ $ unitAspect :
            [ plot $ \(MousePressed mouse) ->
               let (φ₀, rOpening) = case second (+viewAngle) <$> mouse of
                     Nothing -> (0, 1)
                     Just (x, y) | y < 0      -> (x, 1)
                                 | y < 1      -> (x, 1/(1-y))
                                 | otherwise  -> (x, 1e6)
               in  plot [ lineSegPlot
                            [ case ctr rOpening (S¹Polar φ₀)
                                    .+^ rOpening*^embed (S²Polar ϑ φ) of
                                V3 x y z -> (x, sin viewAngle * y + cos viewAngle * z)
                            | disp <- (orig.+^).(dir₁^*)<$>[-20..20]
                            , magnitudeSq disp < rChart
                            , let S²Polar ϑ φq = pole .+~^ (disp^/rOpening)
                                  φ = φ₀ + φq ]
                        | [dir₀, dir₁] <- map(^*0.2)<$>[ [V2 1 0, V2 0 1]
                                                       , [V2 0 1, V2 1 0] ]
                        , orig <- (dir₀^*)<$>[-20..20] ]
            | pole <- charts
            , let ctr rOpening φ₀ = embed (rotateAbout zAxis φ₀ pole) ^* (1-rOpening)
            ])
           caption
          ) [ ( [S²Polar 0 0     , S²Polar pi 0    ]
              , 3
              , "Example: north- and south hemispheres." )
            , ( (S²Polar 0 0        : [ S²Polar (2*pi/3) φ
                                      | φ <- [0, 2*pi/3, -2*pi/3] ])
              , 1.8
              , "Example: four charts in tetrahedral location." )
            ]
   
   "Vectors revisited"
    ====== do
     "A vector is an element of a vector space."
     "A vector space over scalar "<> 𝑆 $<>" is a set "<> 𝑉 $<>" with operations"
      <> maths [ ["(+)" ⸪ 𝑉 -→ 𝑉 -→ 𝑉]
               , ["(·)" ⸪ 𝑆 -→ 𝑉 -→ 𝑉] ]""
      <> " such that (+) is associative and commutative and (·) distributes over it."
     do [plaintext|
          class VectorSpace v where
            type Scalar v :: *
            (^+^) :: v -> v -> v
            (*^) :: Scalar v -> v -> v
         |]
        [plaintext|
          class AdditiveGroup v where
            (^+^) :: v -> v -> v
            negateV :: v -> v
            zeroV :: v
          class VectorSpace v where
            type Scalar v :: *
            (*^) :: Scalar v -> v -> v
         |]
      ── urlRef"hackage.haskell.org/package/vector-spaces"
      ── do law[plaintext|(u^+^v)^+^w ≡ u^+^(v^+^w)  |]
            law[plaintext|u^+^v       ≡ v^+^u        |]
            law[plaintext|(λ+μ)*^v    ≡ λ*^v ^+^ μ*^v|]
            law[plaintext|                           |]
   
   "Affine spaces"
    ====== do
     "“Vector spaces without a distinguished origin”"
      ── [plaintext|
       class AdditiveGroup (Diff p) => AffineSpace p where
         type Diff p :: *
         (.-.) :: p -> p -> Diff p
         (.+^) :: p -> Diff p -> p
      |]
      ── law[plaintext|p .-. p         ≡ zeroV          |]
      ── law[plaintext|p .+^ (q .-. p) ≡ q              |]
      ── law[plaintext|p .+^ (v ^+^ w) ≡ (p .+^ v) .+^ w|]
   
   "Manifolds as weaker affine spaces"
    ====== do
     [plaintext|
       class AdditiveGroup (Needle x) => PseudoAffine x where
         type Needle x :: *
         (.-~.) :: x -> x -> Needle x
         (.+~^) :: x -> Needle x -> x
      |]
      ── law[plaintext|p .-. p         ≡ zeroV          |]
      ── law[plaintext|p .+^ (q .-. p) ≡ q              |]
   
   "The 1-sphere"
    ====== do
     let circCtr = (-1.5, -1.2)
     plotServ [ let plPts :: ([(ℝ,ℝ)], [(ℝ,ℝ)]) -> DynamicPlottable
                    plPts ([], p₁s) = plPts ([(1.1,0)], p₁s)
                    plPts (p₀s, []) = plPts (p₀s, [(0.9,0)])
                    plPts ((x₀,y₀):_, (x₁,y₁):_) = plotMultiple
                      [ legendName "𝑆¹" . shapePlot . Dia.moveTo (Dia.p2 circCtr)
                       . Dia.fcA Dia.transparent $ Dia.circle 1
                      , legendName (printf "p.-~.q = %.2f" v)
                         $ lineSegPlot [ case embed (p₀ .+~^ η*^v :: S¹) of
                                           V2 x y -> circCtr .+^ 1.02*^(x,y)
                                       | η <- [0,0.05..1] ]
                          <> shapePlot
                             (Dia.arrowBetween (Dia.P zeroV) (Dia.p2 (v+1e-3,0)))
                      , mconcat [ diagramPlot $ Dia.text t
                                  & Dia.scale 0.15
                                  & Dia.fc Dia.white
                                  & Dia.moveTo loc
                                | (t, loc) <- [ ("q", Dia.p2 $ circCtr.+^(x₀,y₀))
                                              , ("p", Dia.p2 $ circCtr.+^(x₁,y₁)) ] ] ]
                     where [p₀, p₁] = coEmbed <$> [V2 x₀ y₀, V2 x₁ y₁] :: [S¹]
                           v = p₁ .-~! p₀
                in plot $ \(MouseClicks clicks)
                     -> plPts . partition ((>1) . magnitude) $ (^-^circCtr)<$>clicks
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
                         [ tweakPrerendered (Dia.opacity 0.4) $ lineSegPlot
                            [ torusProject ((S¹Polar 0,S¹Polar 0).+~^disp)
                            | disp <- (orig.+^).(dir₁^*)
                                <$>[-wiremeshResolution..wiremeshResolution] ]
                         | [dir₀, dir₁] <- map(^*(pi/wiremeshResolution))
                                             <$>[ [(1,0), (0,1)]
                                                , [(0,1), (1,0)] ]
                         , orig <- (dir₀^*)<$>[-wiremeshResolution..wiremeshResolution] ]
                      , legendName (printf "p.-~.q = (%.1f,%.1f)" (fst v) (snd v))
                         $ lineSegPlot [ viewProjection
                                          $ torusCtr .+^ embedding (p₀ .+~^ η*^v)
                                       | η <- [0,0.05..1] ]
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
      "Torus as cartesian product:"
       <>maths[[ 𝑇◝2 ⩵ 𝑆◝1 × 𝑆◝1 ]]""
        <>
       [plaintext|
        instance (PseudoAffine x, PseudoAffine y) => PseudoAffine (x,y) where
          type Needle (x,y) = (Needle x, Needle y)
          (x₁,y₁) .-~. (x₀,y₀) = (x₁.-~.x₀, y₁.-~.y₀)
          (x₁,y₁) .+~^ (x₀,y₀) = (x₁.+~^x₀, y₁.+~^y₀)
       |]
   
   "The 2-sphere"
    ====== do
     let sphereCtr = V3 (-1.5) 0 (-1.2)
         viewAngle = 0.2
         wiremeshResolution = 9
     plotServ [ let viewProjection (V3 x y z)
                      = (x, sin viewAngle * y + cos viewAngle * z)
                    sphereProject :: S² -> (ℝ,ℝ)
                    sphereProject p = viewProjection $ sphereCtr .+^ embed p
                    plPts :: S² -> S² -> DynamicPlottable
                    plPts p₀ p₁ = plotMultiple
                      [ legendName "𝑆²" $ plot
                         [ tweakPrerendered (Dia.opacity 0.4) $ lineSegPlot
                            [ sphereProject ((S²Polar 0 0).+~^disp)
                            | disp <- (orig.+^).(dir₁^*)
                                <$>[-wiremeshResolution..wiremeshResolution]
                            , magnitude disp < pi ]
                         | [dir₀, dir₁] <- map(^*(pi/(sqrt 2*wiremeshResolution)))
                                             <$>[ [V2 1 1, V2 1 (-1)]
                                                , [V2 (-1) 1, V2 1 1] ]
                         , orig <- (dir₀^*)<$>[-wiremeshResolution..wiremeshResolution] ]
                      , legendName (printf "p.-~.q = (%.1f,%.1f)" (v^._x) (v^._y))
                         $ lineSegPlot [ viewProjection
                                          $ sphereCtr .+^ embed (p₀ .+~^ η*^v :: S²)
                                       | η <- [0,0.05..1] ]
                          <> shapePlot
                             (Dia.arrowBetween (Dia.P zeroV) (Dia.P v))
                      , mconcat [ diagramPlot $ Dia.text t
                                  & Dia.scale 0.15
                                  & Dia.fc Dia.white
                                  & Dia.moveTo loc
                                | (t, loc) <- [ ("q", Dia.p2 $ sphereProject p₀)
                                              , ("p", Dia.p2 $ sphereProject p₁) ] ] ]
                     where v = p₁ .-~! p₀
                in plotLatest
                     [ plPts (S²Polar 0 0.+~^V2 x₀ y₀)
                             (S²Polar 0 0.+~^V2 x₁ y₁)
                     | [x₀,y₀,x₁,y₁] <- tail
                          $ foldr (zipWith (:) . enumFromThen 0) (repeat [])
                                         [0.02, 1/17, -pi/39, 0.01] ]
              , unitAspect, xInterval (-pi, pi), dynamicAxes ] $
       [plaintext|
        instance PseudoAffine S² where
          type Needle S² = ℝ²
          S²Polar ϑ₁ φ₁ .-~. S²Polar ϑ₀ φ₀ = d *^ embed(S¹Polar γc)
           where V3 qx qy qz = embed $ S²Polar ϑ₁ (φ₁-φ₀)
                 
                 sϑ₀ = sin ϑ₀; cϑ₀ = cos ϑ₀
                 (bx,bz) = ( cϑ₀ * qx - sϑ₀ * qz
                           , sϑ₀ * qx + cϑ₀ * qz )
                 by      = qy
                 
                 S²Polar d γ = coEmbed $ V3 bx by bz
                 
                 γc | ϑ₀ < pi/2   = γ + φ₀
                    | otherwise   = γ - φ₀
          S²Polar ϑ₀ φ₀ .+~^ 𝐯 = S²Polar ϑ₁ φ₁
           where S¹Polar γc = coEmbed 𝐯
                 γ | ϑ₀ < pi/2   = γc - φ₀
                   | otherwise   = γc + φ₀
                 d = magnitude 𝐯
                 S¹Polar φ₁ = S¹Polar φ₀ .+~^ δφ
                 
                 V3 bx by bz = embed $ S²Polar d γ
                 
                 sϑ₀ = sin ϑ₀; cϑ₀ = cos ϑ₀
                 (qx,qz) = ( cϑ₀ * bx + sϑ₀ * bz
                           ,-sϑ₀ * bx + cϑ₀ * bz )
                 qy      = by
                 
                 S²Polar ϑ₁ δφ = coEmbed $ V3 qx qy qz
       |]

   "ODEs"
    ====== do
     "Example: Newton equations of motion"
       <> do maths [[ (del◝2<>𝐱)/del⁀𝑡 ⩵ 𝐅/𝑚 ]]""
             maths [[ (del◝2<>𝐱°𝑡)/del⁀𝑡◝2 ⩵ 𝐅°𝑡/𝑚 ]]""
             maths [[ (del◝2<>𝐱°𝑡)/del⁀𝑡◝2 ⩵ 𝐅°(𝐱°𝑡)/𝑚 ]]""
             maths [ [ (del◝2<>𝐱°𝑡)/del⁀𝑡◝2 ⩵ 𝐅°(𝐱°𝑡)/𝑚 ]
                   , [ 𝑡 ⸪ ℝ , 𝑚 ⸪ ℝ ]
                   , [ 𝐱 ⸪ ℝ -→ ℝ◝3 ]
                   , [ 𝐅 ⸪ ℝ◝3 -→ ℝ◝3 ] ]""
             maths [ [ (del<>(𝐱،𝐯)°𝑡)/del⁀𝑡 ⩵ (𝐯، 𝐅°(𝐱°𝑡)/𝑚) ]
                   , [ 𝑡 ⸪ ℝ , 𝑚 ⸪ ℝ ]
                   , [ (𝐱،𝐯) ⸪ ℝ -→ ℝ◝6 ]
                   , [ 𝐅 ⸪ ℝ◝3 -→ ℝ◝3 ] ]""
      ── do
       emph "Ordinary differential equation"
       "Ordinary differential equations:"
         ── do
          maths [ [dot 𝐲°𝑡 ⩵ 𝑓°(𝐲°𝑡)]
                , [𝐲 ⸪ ℝ -→ ℝ◝𝑛 , 𝑓 ⸪ ℝ◝𝑛 -→ ℝ◝𝑛] ]""
          maths [[ dot 𝐲°𝑡 ⩵ 𝑓°(𝐲°𝑡) ]]""
           ── "Picard-Lindelöf theorem: if "<>𝑓$<>" is "<>emph"Lipschitz continuous"
             <>", then there is a unique solution."
   
   let tangentPlot t₀ y y' = plot [ lineSegPlot [ (t₀+μ*c, y+μ*s)
                                                | μ <- [-ε, ε] ]
                                        & opac 0.08
                                  | ε<-(+0.3).(2**)<$>[-4,-3.5..2] ]
                             <> lineSegPlot [ (t₀-μ*s, y+μ*c)
                                            | μ <- [-0.01, 0.01] ]
        where (s,c) = sin&&&cos $ atan y'
       eulerCode_vectSpc = [plaintext|
            euler :: VectorSpace v 
                => (v -> v) -> ℝ -> v -> [(ℝ,v)]
            euler f h y₀ = go 0 y₀
             where go ti yi = (ti, yi) : go (ti+h) (yi ^+^ h*^f yi)
           |]
   "Numerical solving of ODEs"
    ====== do
    "“Follow the derivatives” (tangents)"
     & let g t = exp (-t^2)
           g' t = -2*t * exp (-t^2)
        in plotServ [ continFnPlot g
                    , plot $ \(MouseClicks clicks)
                        -> plot [ tangentPlot t₀ (g t₀) (g' t₀)
                                | (t₀,_) <- clicks ]
                    , xAxisLabel "𝑡", yAxisLabel "𝑦", unitAspect
                    ]
    (let g t = exp (-t^2)
         g' t = -2*t * exp (-t^2)
        in plotServ [ continFnPlot g
                    , plot $ \(MouseClicks clicks)
                        -> plot [ tangentPlot t₀ y (g' t₀)
                                | (t₀,y) <- clicks ]
                    , xAxisLabel "𝑡", yAxisLabel "𝑦", unitAspect
                    ])
     $ "“Follow the derivatives” (tangents)"
       ── do
       "Euler's method:"
        <> maths [ [ 𝑡◞(𝑖+1) ⩵ 𝑡◞𝑖 + ℎ ]
                 , [ 𝑦◞(𝑖+1) ⩵ 𝑦◞𝑖 + ℎ*𝑓°(𝑦◞𝑖) ] ]""
       "Euler's method:"
        <> maths [ [ 𝑡◞(𝑖+1) ⩵ 𝑡◞𝑖 + ℎ ]
                 , [ 𝑦◞(𝑖+1) ⩵ 𝑦◞𝑖 + ℎ*𝑓°(𝑦◞𝑖) ] ]""
        ── eulerCode_vectSpc
       eulerCode_vectSpc
        ── [plaintext|
              gravAcc :: Mass -> Diff Pos -> Diff Velo
              gravAcc mt δx = (gravConst * mt / magnitude δx^3) · δx
              
              > euler (\((xe,ve), (xs,vs))
                          -> ( (ve, gravAcc sunMass $ xs.-.xe)
                             , (vs, gravAcc earthMass $ xe.-.xs) ) )
         |] & plotServ
           [ trajectoryPlot 2
               [("Earth", earthRadius), ("Sun", sunRadius)]
               [ [(xe,ye), (xs, ys)]
               | ((V3 xe ye _, _), (V3 xs ys _, _))
                  <- traject2Body euler (earthMass                            , sunMass)
                                        ((V3 earthDist 0 0, V3 0 earthSpeed 0), zeroV) ]
           , unitAspect, xInterval (-earthDist, earthDist)
                         , yInterval (0, earthDist), dynamicAxes ]
       "Euler's method is unstable and can cause energy to grow without bounds!"
         & plotServ
           [ trajectoryPlot 10
               [("Earth", earthRadius), ("Sun", sunRadius)]
               [ [(xe,ye), (xs, ys)]
               | ((V3 xe ye _, _), (V3 xs ys _, _))
                  <- traject2Body euler (earthMass                            , sunMass)
                                        ((V3 earthDist 0 0, V3 0 earthSpeed 0), zeroV) ]
           , unitAspect, xInterval (-earthDist, earthDist)
                       , yInterval (0, earthDist) ]
       "Euler's method is unstable and can cause energy to grow without bounds!"
        <> do
          maths [[ 𝐸 ⩵ 𝑈 + 𝑇 ]]""
          maths [[ 𝐸 ⩵ 𝐺*𝑀*𝑚/norm 𝐱 + 𝑇 ]]""
          maths [[ 𝐸 ⩵ 𝐺*𝑀*𝑚/norm 𝐱 + 1/2*𝑚*norm 𝐯◝2 ]]""
          maths [[ 𝐸 ⩵ 𝐺*𝑀*𝑚/norm 𝐱 + 1/2*𝑚*𝑣*norm (hat%$>𝐯)◝2 ]]""
     
   "Solving of ODEs on manifolds"
    ====== do
     eulerCode_vectSpc
     [plaintext|
       euler :: PseudoAffine y
           => (y -> Needle y) -> Needle ℝ -> y -> [(ℝ,y)]
       euler f h y₀ = go 0 y₀
        where go ti yi = (ti, yi) : go (ti+h) (yi .+~^ h*^f y)
      |]


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
                     , shapePlot . Dia.moveTo (Dia.p2 $ last chunkCompo)
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
