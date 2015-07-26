

module TriangT where


import Data.SimplicialComplex
import Data.Manifold.TreeCover
import Graphics.Dynamic.Plot.R2
import Diagrams.Prelude
import Diagrams.Backend.Cairo

triangTest :: AutoTriang Two P2
triangTest =
   elementaryTriang (p2(0,0) :<| p2(0,1) .<. p2(1,0))
   <> elementaryTriang (p2(1.5,0.5) :<| p2(0.5,1.5) .<. p2(1.5,1.5))

plotTriangle :: Simplex Two P2 -> DynamicPlottable
plotTriangle s = plot (fromVertices (last vs : vs) & lc red :: Diagram B R2)
 where vs = simplexVertices' s

main :: IO ()
main = do
   let trings = breakdownAutoTriang triangTest
   plotWindow $ plotTriangle <$> trings
   return ()
   


