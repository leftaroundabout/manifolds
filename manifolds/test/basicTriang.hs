import Data.Manifold
import Data.Manifold.Visualisation.R3.GLUT

import Data.IORef

import Data.Time.Clock

import Graphics.Rendering.OpenGL hiding (Triangulation)
import Graphics.UI.GLUT hiding (Triangulation)

import Data.VectorSpace
import Data.VectorSpace.OpenGL

import Control.Arrow
import Control.Monad.Trans.Reader
import Control.Monad.IO.Class


type GLVertex = Vertex3 GLfloat
type GLSimplex = Simplex GLVertex
type GLTriangulation = Triangulation GLVertex

type NVertex = CleverGLvertex (Vertex3 GLfloat) (Normal3 GLfloat)

type GLNTriangulation = Triangulation NVertex


my2Simplex, my2Simplex' :: GLSimplex
my2Simplex' = affineSimplex [ Vertex3   1     0   0
                           , Vertex3   0     1   0
                           , Vertex3   0     0   0 ]
my2Simplex = affineSimplex [ Vertex3   0      1    0
                           , Vertex3 (-xb)(-1/2) 0
                           , Vertex3  xb  (-1/2) 0 ]
     where xb = sqrt 3 / 2

my3Simplices :: [GLSimplex]
my3Simplices = [
    affineSimplex [ Vertex3 1   0   1
                  , Vertex3 0   1   1
                  , Vertex3 0.3 0.3 0
                  , Vertex3 0   0   1  ]
  , affineSimplex [ Vertex3 1   0   1
                  , Vertex3 0.1(-0.3)1
                  , Vertex3 0.3 0.3 0
                  , Vertex3 0   0   1  ]
               ]

parachute :: GLfloat -> GLfloat -> GLNTriangulation
parachute φ₀ screwGr = fmap bendNShade rectangle
 where bendNShade (Vertex2 u v)
                 = CleverGLvertex vert normal
        where vert = Vertex3 x y z
              normal = Normal3 x y z
              x = (sin ϑ*cos φ)
              z = (sin ϑ*sin φ)
              y = (cos ϑ)
              φ = u*1.1*screwGr + φ₀
              ϑ = u + pi/2 + v/screwGr -- + sum[sin(sin u/(80.5-n) + cos v/(37+n))/9823 | n<-[1..1700]]
       rectangle :: Triangulation(Vertex2 GLfloat)
       rectangle = affineSimplex [ Vertex2 1 (-1), Vertex2 (-1) 1, Vertex2 (-1) (-1) ]
               ⊿⊳ affineSimplex [ Vertex2 (-1) 1, Vertex2 1 (-1), Vertex2 1    1    ]

myTetrahedron = simplexBoundary $ head my3Simplices

myTriangulation = autoglueTriangulation [my2Simplex]


lightDir = normalized $ Normal3 1 1 1


renderCfg :: TrianglatnRenderCfg VisualisationRT NVertex
renderCfg = TrianglatnRenderCfg
               { simplexSmallEnoughPred = return 
                    . cleverGLvertex_brcDiffLimit 0.01 ((<0.04).magnitude)
               , triangleRenderer = randColShadableTriangleRenderer $
                                        \(CleverGLvertex _ normal) ->
                                          let h = abs(normal<.>lightDir)/2 + 0.3
                                              (r,g,b) = (3/8, 7/9, 1)
                                          in Color3 (h*r) (h*g) (h*b) 
               , edgeRenderer     = stdEdgeRenderer
               , simplexRenderRefine = const id
               , logTrianglatnRender = ignore  -- putStr
               }

sceneConfig :: GLSceneConfig
sceneConfig = defOrthoSceneCfg


main = do
   glViewMain sceneConfig $ do
          t <- askTotalVisRuntime
          let φ₀i = realToFrac t * 2
              screwGr = φ₀i/7 + 1
          renderTriangulation renderCfg $ parachute φ₀i screwGr
--           $ myTetrahedron
--           $ nStepBarycentricSubdivisions 0 myTriangulation
                                   