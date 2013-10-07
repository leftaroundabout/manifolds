module Util.Associate where



-- | Unlike the related 'zipWith', 'associateWith' \"spreads out\" the shorter
-- list by duplicating elements, before merging, to minimise the number of
-- elements from the longer list which aren't used.
associateWith :: (a->b->c) -> [a] -> [b] -> [c]
associateWith f a b
  | lb>la      = spreadn(lb`quot`la) f a b
  | otherwise  = spreadn(la`quot`lb) (flip f) b a
 where la = length a; lb = length b
       spreadn n f' = go
        where go (e:es) t
               | (et, tr) <- splitAt n t  
                    = foldr((:) . f' e) (go es tr) et
              go _ _ = []
              
-- | @associate = associateWith (,)@.
associate :: [a] -> [b] -> [(a,b)]
associate = associateWith (,)

associaterSectorsWith :: (a->[b]->c) -> [a] -> [b] -> [c]
associaterSectorsWith f a b = spreadn(lb`quot`la) a b
 where la = length a; lb = length b
       spreadn n (e:es) t
        | (et, tr) <- splitAt n t  = f e et : spreadn n es tr
       spreadn _ _ _ = []

associaterSectors :: [a] -> [b] -> [(a,[b])]
associaterSectors = associaterSectorsWith (,)
       
associatelSectorsWith :: ([a]->b->c) -> [a] -> [b] -> [c]
associatelSectorsWith f = flip (associaterSectorsWith $ flip f)

associatelSectors :: [a] -> [b] -> [([a],b)]
associatelSectors = associatelSectorsWith (,)

partitions :: Int -> [a] -> [[a]]
partitions n = go
 where go [] = []
       go l | (chunk,rest) <- splitAt n l  = chunk : go rest

divide :: Int -> [a] -> [[a]]
divide n ls = partitions(length ls`div`n) ls
 
 
mapOnNth :: (a->a) -> Int -> [a] -> [a]
mapOnNth f 0 (l:ls) = f l : ls
mapOnNth f n (l:ls) = l : mapOnNth f (n-1) ls
mapOnNth _ _   []   = []

mapExceptOnNth :: (a->a) -> Int -> [a] -> [a]
mapExceptOnNth f 0 (l:ls) = l : map f ls
mapExceptOnNth f n (l:ls) = f l : mapOnNth f (n-1) ls
mapExceptOnNth _ _   []   = []

