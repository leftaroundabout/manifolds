

module TriangT where


import Data.SimplicialComplex
import Graphics.Dynamic.Plot.R2
import Diagrams.Prelude

triangTest :: TriangT t Two R2 IO [[R2]]
triangTest = do
   --[r0] <- simplexITList
   [s0,s1,s2] <- simplexITList
   r1 <- introVertToTriang (1 ^& 1) [s0]
   mapM (fmap simplexVertices' . lookSimplex) [r1]

main :: IO ()
main = do
   splxs <- evalTriangT triangTest . singleSimplex
      $ 0^&0 :<| 0^&1 .<. 1^&0
   return ()
   


