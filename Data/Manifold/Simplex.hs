module Data.Manifold.Simplex where


data Simplex p = Simplex {
    subSimplicesMkp :: Array (ClRefSimplex p)
  }

data SubdivAccID = SubdivAccID { 
   subdivFacebasis
 , sdfbSubdiv
 , sdfbSubdivFaceID   :: Int
 } deriving (Eq, Show)
 
data ClRefSimplex p = ClRefSimplex {
    subSimplexInnards :: OpenSimplex p
  , simplexClosureRef :: Array Int
  }
data ClRefSimplexSubdiv p = ClRefSimplexSubdiv {
    simplexSubdivInnards :: OpenSimplex p
  , simplexClosureRefInFace :: Array Int
  , simplexClosureRefInSds  :: Array Int
  }

data OpenSimplex p = SimplexInnards {
    osimplexBarycenter :: p
  , osimplexSubdivs :: Array (Array (ClRefSimplexSubdiv p))
  , osimplexSubdividers :: Array (OpenSimplex p, Array SubdivAccID)
  }

-- class HasSimplices s where
--   onOpenSimplices :: (OpenSimplex p -> OpenSimplex q) -> s p -> s q
--   onSimplices :: (Simplex p -> Simplex q) -> s p -> s q
-- instance HasSimplices Simplex where
--   onOpenSimplices = fmap . onOpenSimplices
--   onSimplices = id
-- 

simplexMainInnard :: Simplex p -> OpenSimplex p
simplexMainInnard = subSimplexInnards . V.head . subSimplicesMkp

subSimplices :: Simplex p -> Array (Simplex p)
subSimplices (Simplex subsMkp) = fmap assembleSub subsMkp
 where assembleSub (ClRefSimplex innard sSubRefs)
          = Simplex $ (ClRefSimplex innard V.empty) `V.cons` fmap reIndex sSubRefs
        where reIndex i = ClRefSimplex thisSubInr $ V.backpermute fwdRefMap thisSubSrs
               where (ClRefSimplex thisSubInr thisSubSrs) = subsMkp ! i
              fwdRefMap = inverseAssoc sSubRefs

zeroSimplex :: p -> Simplex p
zeroSimplex = Simplex . V.singleton . (`ClRefSimplex`V.empty) . zeroOpenSimplex

zeroOpenSimplex :: p -> OpenSimplex p
zeroOpenSimplex p = SimplexInnards p V.empty V.empty

openSimplexDimension :: OpenSimplex p -> Int
openSimplexDimension (SimplexInnards _ subdivs _) 
   = invFactorial (V.length subdivs) - 1

simplexSubdivs :: Simplex p -> Array(Simplex p)
simplexSubdivs s@(Simplex subqs) 
          = V.indexed (V.zip osimplexSubdivs (V.tail subs)) >>= assembleSubdGroup
 where subs = subSimplices s
       refAll = V.enumFromN 1 $ V.length subqs - 1
       mainInr@(SimplexInnards {..}) = subSimplexInnards $ V.head subqs
       assembleSubdGroup (sideID, (sdGroup, side))
         = V.zipWith assembleSubd (sdGroup) (simplexSubdivs side)
        where assembleSubd (ClRefSimplexSubdiv {..}) (Simplex sideSubdSubs)
                = Simplex $ ClRefSimplex subSimplexInnards refAll
                    `V.cons` fmap rerefSubdsubFromFace simplexClosureRefInFace
                    V.++     fmap rerefSubdsubFromSds  simplexClosureRefInSds
               where rerefSubdsubFromSds sdID
                        = ClRefSimplex cutWallInr cutWallSubRef
                      where (cutWallInr, cutWallUses) = osimplexSubdividers ! sdID
                            (SubdivAccID{..})
                                 = V.find ((==sideID) . subdivFacebasis) cutWallUses
                            cutWallSubRef = undefined
                     rerefSubdsubFromFace fcID
                        = ClRefSimplex faceSubdInr $ fmap (+1) faceSubdSubRef
                      where (ClRefSimplex faceSubdInr faceSubdSubRef) 
                                                         = sideSubdSubs ! fcID
         

subdividersWithSubs :: Simplex p -> [(OpenSimplex p, Array (OpenSimplex p))]
subdividersWithSubs = undefined
--   (Simplex subs)
--             = map (second gatherDivSubs) dvds
--  where gatherDivSubs (subSrc@(SubdivAccID{..}):_)
--          = fromSide `V.cons` fromLesserDivs
--         where fromSide = subdivGroups ! subdivFacebasis ! sdfbSubdiv
--               fromLesserDivs = 
--        (SimplexInnards baryc subdivGroups dvds) = V.head subs
-- 
{-# SPECIALIZE invFactorial :: Int -> Int #-}
invFactorial :: Integral i => i->i
invFactorial k = invFact 1 1
 where invFact n j
        | j >= k   = n
        | n'<-n+1  = invFact n' $ j*n'


-- | Note that the 'Functor' instances of 'Simplex' and 'Triangulation'
-- are only vaguely related to the actual category-theoretic /simplicial functor/.
instance Functor Simplex where
  fmap f = Simplex . fmap (fmap f) . subSimplicesMkp

instance Functor ClRefSimplex where
  fmap f (ClRefSimplex si srf) = ClRefSimplex (fmap f si) srf

instance Functor OpenSimplex where
  fmap f (SimplexInnards brc divs dvders)
        = SimplexInnards ( f brc )
                         ( (fmap.fmap.fmap ) f divs   )
                         ( (fmap.first.fmap) f dvders )

instance Comonad OpenSimplex where
  extract (SimplexInnards brc _ _) = brc
  
  duplicate s@(SimplexInnards brc sdGroups subdvds)
   = SimplexInnards s
         ( (fmap.fmap) 
             (\(ClRefSimplex si srf) -> ClRefSimplex (duplicate si) srf )
             sdGroups )
         ( (fmap.first) duplicate subdvds )

-- Works something like the following: 'extract' retrieves the barycenter,
-- 'duplicate' replaces the barycenter of each subsimplex /s/ with all of /s/ itself.
instance Comonad Simplex where
 
  extract (Simplex subs)
   | ClRefSimplex(SimplexInnards baryc _ _)_ <- V.head subs  = baryc
  
  duplicate (Simplex inrs) = duplicat
   where duplicat = Simplex $ fmap lookupSides inrs
         
         dduplicat@(Simplex ddsubs) = fmap duplicate duplicat
         
         lookupSides ( ClRefSimplex (SimplexInnards baryc sdGroups subdvds)
                                    subsubIds                               )
           = ClRefSimplex (SimplexInnards (Simplex $ V.backpermute inrs subsubIds) 
                                          dupdSds dupdSdvds                        )
                          subsubIds
          where dupdSds = V.zipWith recm
                             sdGroups
                             ( fmap (osimplexBarycenter . subSimplexInnards) thisSubSubs )
                thisSubSubs = V.backpermute ddsubs subsubIds
                dupdSdvds = fmap sdFRecm subdvds
                recm subdivs faceBase
                  = V.zipWith recmi subdivs faceSDBases
                 where recmi (ClRefSimplex subdiv subdivMq) faceSubdiv 
                                              = simplexMainInnard dupSub
                        where sdqFaces = fmap fst 
                                          . V.filter (any ((==j) . sdfbSubdiv) . snd)
                                          $ sdGFaces
                              dupSub = duplicate . Simplex 
                                              . fmap (`ClRefSimplex`undefined) $
                                         subdiv 
                                `V.cons` fmap fst (subSimplicesMkp faceSubdiv)
                                    V.++ sdqFaces
                                `V.snoc` zeroOpenSimplex baryc
                       faceSDBases = fmap osimplexBarycenter 
                                       $ fmap fst (subSimplicesMkp faceBase)
                       sdGFaces = V.fromList
                                . filter (any ((==i) . subdivFacebasis) . snd)
                                $ subdvds
                sdFRecm (SimplexInnards b s _, orient) 
                 | V.null s  = (SimplexInnards (zeroSimplex b) V.empty [], orient)
                sdFRecm (_, orient@(SubdivAccID i j k : _)) 
                      = (fst dupSub, orient)
                 where dupSub = (subSimplicesMkp . duplicate . osimplexBarycenter)
                                  (dupdSds ! i ! j) ! k




affineSimplexCone :: forall v . EuclidSpace v => v -> Simplex v -> Simplex v
affineSimplexCone p base@(Simplex baseSubs) = Simplex subs
 where subs = coneFillSubs V.++ baseSubs' `V.snoc` (zeroOpenSimplex p, V.empty)
       coneFillSubs = fmap fillConeSub baseSubs
       fillConeSub (baseSubInr, baseSubqRef) = (csubInr, subqRef)
        where csubInr = undefined
              subqRef = undefined
--                | V.null baseSubqRef
--                    = SimplexInnards lineBaryc lineSubs V.empty
--                        where lineBaryc = midBetween [p, osimplexBarycenter baseSubInr]
--                              lineSubs  = undefined
--                | otherwise
--                    = simplexMainInnard $ affineSimplexCone p baseSubsimplex
              
       baseSubs' = fmap (\(bsinr, bssSubrefs)
                          -> ( bsinr, fmap (+ V.length coneFillSubs) bssSubrefs )
                        ) baseSubs

affineSimplex :: forall v . EuclidSpace v => [v] -> Simplex v
affineSimplex (v:vs) = foldr affineSimplexCone (zeroSimplex v) vs

recalcInnardsAffine :: forall v . EuclidSpace v => Simplex v -> Simplex v
recalcInnardsAffine (Simplex baseSubs) = Simplex $ baseSubs V.// [(0, reMainInr)]
 where properSubs = V.tail baseSubs
       properSubsIds = V.enumFromN 1 $ V.length properSubs
       dim = openSimplexDimension (V.head properSubs) + 1
       reMainInr = ( SimplexInnards barycenter subdivs subdvds
                   , properSubsIds                             ) 
       barycenter = zeroOpenSimplex . midBetween . V.toList
                      $ fmap (osimplexBarycenter . fst) properSubs
       subdivs = V.imap bSdGroups properSubs
        where bSdGroups i = undefined
       subdvds = V.toList $ V.zip properSubsIds properSubs >>= extrDividers
        where extrDividers (im1, (sideQInr, sideQRx))
                = ( if openSimplexDimension sideQInr < dim-1
                     then undefined
                     else id )
                    $ fmap coneOnSideDvd (osimplexSubdividers sideQInr)
               where 
                     coneOnSideDvd (sdvdInr, sdvdSrc)
                      = ( simplexMainInnard $ recalcInnardsAffine hollowDvd
                        , fmap reref sdvdSrc                                )
                      where reref = undefined
                            hollowDvd = Simplex $
                                        undefined
                                  -- The subdivider's innard (to be filled by 'recalcInnardsAffine' recursively).
                               `V.cons` undefined
                                  -- The subdivider's faces, which are lesser subdividers themselves already calculated.
                               V.++    (sdvdInr, enumFromN (divDim+1) divDim) 
                                  -- The known face as taken from the given shell.
                               `V.cons` undefined
                                  -- The 
                               `V.snoc` (barycenter, [])
                                  -- The vertex at the outer simplex' barycenter.
                            divDim = openSimplexDimension sdvdInr + 1
                            divInSideSubs = undefined
                            completionSrc = head sdvdSrc
                            (SimplexInnards _ sideSubdGroups sideDividers) = sideQInr
                  





instance (Show p) => LtdShow (Simplex p) where
  ltdShow 0 _ = "Simplex (...) (...)"
  ltdShow n (Simplex sinrs) = "Simplex (" ++ pShow (fmap fst sinrs) ++ ")"
   where pShow :: LtdShow s => s->String
         pShow = ltdShow $ n`quot`2

instance (Show p) => LtdShow (OpenSimplex p) where
  ltdShow 0 _ = "SI (...) (...) (...)"
  ltdShow n (SimplexInnards brc sds dvds) = "SI " ++ show brc
                                      ++ pShow sds
                                      ++ " " ++ pShow (V.fromList dvds)
   where pShow :: LtdShow s => s->String
         pShow = ltdShow $ n`quot`3
                                      
     
              
midBetween :: (VectorSpace v, Fractional(Scalar v)) => [v] -> v
midBetween vs = sumV vs ^/ (fromIntegral $ length vs)
       

  


-- | Remove \"gaps\" in an array of unique numbers, i.e. the set of elements
-- is mapped strict-monotonically to @[0 .. length arr - 1]@.
sediment :: Array Int -> Array Int
sediment = V.map fst . saSortBy(compare`on`fst.snd)
             . V.indexed . saSortBy(compare`on`snd) . V.indexed


-- | 'inverseAssoc' is basically the inverse of 'Data.Vector.backpermute'.
inverseAssoc :: Array Int -> Array Int
inverseAssoc = V.fromList . psFillGaps . V.toList
                    . saSortBy (compare`on`snd) . V.indexed
 where psFillGaps [(e,_)] = [e]
       psFillGaps ( (a,α) : r@((b,β):_) )
        | β == succ α  = a : psFillGaps r
        | otherwise    = a : psFillGaps ( (undefined, succ α) : r )





 


infixl 7 ↺↺, ↺↻
class Permutation π where
  (↺↺) :: π -> π -> π
  (↺↻) :: π -> π -> π
  p↺↻q = p ↺↺ invPerm q
  invPerm :: π -> π




deleteAt :: Int -> [a] -> [a]
deleteAt n = uncurry(++) . second tail . splitAt n

reglueRemAt :: Int -> [a] -> [a]
reglueRemAt n = uncurry(flip(++)) . second tail . splitAt n

-- | @'omit1s' [0,1,2,3] = [[1,2,3], [0,2,3], [0,1,3], [0,1,2]]@
omit1s :: [a] -> [[a]]
omit1s [] = []
omit1s [_] = [[]]
omit1s (v:vs) = vs : map(v:) (omit1s vs)

-- | @'gapPositions' [0,1,2,3] = [[1,2,3], [2,3,0], [3,0,1], [0,1,2]]@
gapPositions :: [a] -> [[a]]
gapPositions = gp id
 where gp rq (v:vs) = (vs++rq[]) : gp (rq.(v:)) vs
       gp _ _ = []


type Map = Map.Map


type Array = V.Vector


{-# INLINE enumFromN #-}
enumFromN :: Num a => a -> Int -> [a]
enumFromN i0 = V.toList . V.enumFromN i0

saSort :: Ord a => Array a -> Array a
saSort = V.modify VAIns.sort

-- The sorting algorithm of choice is simple insertion sort, because simplices
-- that can feasibly be handled will always have low dimension, so the better
-- complexity of more sophisticated sorting algorithms is no use on the short
-- vertex arrays.
{-# INLINE saSortBy #-}
saSortBy :: VAIns.Comparison a -> Array a -> Array a
saSortBy cmp = V.modify $ VAIns.sortBy cmp
