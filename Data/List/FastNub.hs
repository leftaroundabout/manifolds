module Data.List.FastNub where


import Data.List
import Data.Function


type FastNub a = (Eq a, Ord a) -- S̶h̶o̶u̶l̶d̶ ̶r̶e̶a̶l̶l̶y̶ ̶b̶e̶ ̶(̶E̶q̶ ̶a̶,̶̶ ̶H̶a̶s̶h̶a̶b̶l̶e̶ ̶a̶)̶
fastNub :: FastNub a => [a] -> [a]
fastNub = map head . group . sort

-- | Simply a merge sort that discards equivalent elements.
fastNubBy :: (a->a->Ordering) -> [a] -> [a]
fastNubBy _ [] = []
fastNubBy _ [e] = [e]
fastNubBy cmp es = merge(fastNubBy cmp lhs)(fastNubBy cmp rhs)
 where (lhs,rhs) = splitAt (length es `quot` 2) es
       merge [] rs = rs
       merge ls [] = ls
       merge (l:ls) (r:rs) = case cmp l r of
                              LT -> l : merge ls (r:rs)
                              GT -> r : merge (l:ls) rs
                              EQ -> merge (l:ls) rs

-- | Like 'fastNubBy', but doesn't just discard duplicates but \"merges\" them.
-- @'fastNubBy' cmp = cmp `'fastNubByWith'` 'const'@.
fastNubByWith :: (a->a->Ordering) -> (a->a->a) -> [a] -> [a]
fastNubByWith _ _ [] = []
fastNubByWith _ _ [e] = [e]
fastNubByWith cmp cmb es = merge(fastNubByWith cmp cmb lhs)(fastNubByWith cmp cmb rhs)
 where (lhs,rhs) = splitAt (length es `quot` 2) es
       merge [] rs = rs
       merge ls [] = ls
       merge (l:ls) (r:rs) = case cmp l r of
                              LT -> l : merge ls (r:rs)
                              GT -> r : merge (l:ls) rs
                              EQ -> merge (cmb l r : ls) rs

sfGroupBy :: (a->a->Ordering) -> [a] -> [[a]]
sfGroupBy cmp = fastNubByWith (cmp`on`head) (++) . map(:[])
