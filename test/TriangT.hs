

module TriangT where


import Data.SimplicialComplex
import Data.Manifold.TreeCover
import Graphics.Dynamic.Plot.R2
import Diagrams.Prelude
import Diagrams.Backend.Cairo
import IPPrint.Colored


triangTest :: AutoTriang Two P2
triangTest =
   elementaryTriang (p2(0,0) :<| p2(0,1) .<. p2(1,0))
   <> elementaryTriang (p2(1.5,0.5) :<| p2(0.5,1.5) .<. p2(1.5,1.5))

plotTriangle :: Simplex Two P2 -> DynamicPlottable
plotTriangle s = shapePlot $ fromVertices (last vs : vs) & strokeLocLoop & opacity 0.3
 where vs = simplexVertices' s

main :: IO ()
main = do
   let trings = breakdownAutoTriang triangTest
   cpprint trings
   plotWindow $ plotTriangle <$> trings
   return ()
   


