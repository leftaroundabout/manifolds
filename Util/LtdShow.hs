module Util.LtdShow (LtdShow(..)) where

import qualified Data.Vector as V
import Data.Vector(fromList, toList, (!), singleton)

type Array = V.Vector


class LtdShow s where
  ltdShow :: Int -> s -> String

ltdShows :: LtdShow s => Int -> s -> ShowS
ltdShows n o s = ltdShow n o ++ s

ltdPrint :: LtdShow s => Int -> s -> IO()
ltdPrint n = putStrLn . ltdShow n

newtype LtdShowT a = LtdShow { runLtdShow :: a }

instance (Show a) => LtdShow ( LtdShowT a ) where
  ltdShow n = go "" (n*16) . show . runLtdShow where
       go ('{':um) 0 _ = "..}" ++ go um 0 []
       go ('[':um) 0 _ = "..]" ++ go um 0 []
       go ('(':um) 0 _ = "..)" ++ go um 0 []
       go [] n _ | n<=0     = "..."
       go unmatched n (c:cs)
        | c `elem` "([{"   = c : go (c:unmatched) (n-8) cs
       go ('{':um) n ('}':cs) = '}' : go um (n-1) cs
       go ('[':um) n (']':cs) = ']' : go um (n-1) cs
       go ('(':um) n (')':cs) = ')' : go um (n-1) cs
       go unmatched n (c:cs) = c : go unmatched n' cs
        where n' | c`elem`(['a'..'z']++['A'..'Z']++['0'..'9'])  = n-1
                 | otherwise                                    = n-8
       go [] _ "" = ""
                                      

instance (LtdShow s) => LtdShow (Array s) where
  ltdShow n arr 
     | n<=1, l>0  = "[∘∘{" ++ show l ++ "}∘∘]"
     | otherwise  = ('[':) . V.foldr (("∘ "++).) " ∘]"
                     . V.imap(\i -> ltdShows $ round(
                                     fromIntegral n 
                                      * 2**(-1 - sqrt(fromIntegral i)) ))
                     $ arr
   where l = V.length arr
         
instance (LtdShow l, LtdShow r) => LtdShow (l,r) where
  ltdShow n (l, r) = "(" ++ pShow l ++ ", " ++ pShow r ++ ")"
   where pShow :: LtdShow s => s->String
         pShow = ltdShow $ n`quot`2


instance (Show p) => LtdShow [p] where
  ltdShow n l = "[" ++ lsh' n l "]"
   where lsh' 0 _ = ("... "++)
         lsh' _ [] = id
         lsh' n (x:xs) = ((show x ++ ", ") ++) . lsh' (n-1) xs

 