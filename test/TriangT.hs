

module TriangT where


import Data.SimplicialComplex
import Graphics.Dynamic.Plot.R2
import Diagrams.Prelude

triangTest :: TriangT t Two R2 IO [[R2]]
triangTest = return []

main :: IO ()
main = do
   splxs <- evalTriangT triangTest mempty
   return ()
   


