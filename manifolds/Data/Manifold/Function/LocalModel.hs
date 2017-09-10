-- |
-- Module      : Data.Manifold.Function.LocalModel
-- Copyright   : (c) Justus Sagemüller 2017
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsagemue $ uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 

{-# LANGUAGE ScopedTypeVariables      #-}
{-# LANGUAGE UnicodeSyntax            #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE TupleSections            #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE StandaloneDeriving       #-}
{-# LANGUAGE TemplateHaskell          #-}
{-# LANGUAGE ConstraintKinds          #-}

module Data.Manifold.Function.LocalModel (
    -- * The model class
      LocalModel (..)
    -- ** Local data fit models
    , AffineModel(..), QuadraticModel(..)
    , estimateLocalJacobian, estimateLocalHessian
    , propagationCenteredModel
    , propagationCenteredQuadraticModel
    , quadraticModel_derivatives
    -- ** Differential equations
    , DifferentialEqn, LocalDifferentialEqn(..)
    , propagateDEqnSolution_loc, LocalDataPropPlan(..)
    -- ** Range interpolation
    , rangeWithinVertices
    ) where


import Data.Manifold.Types
import Data.Manifold.PseudoAffine
import Data.Manifold.Types.Primitive ((^))
import Data.Manifold.Shade
import Data.Manifold.Riemannian

import Data.VectorSpace
import Math.LinearMap.Category

import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.List.NonEmpty as NE

import qualified Prelude as Hask

import Control.Category.Constrained.Prelude
import Control.Arrow.Constrained

import Control.Lens
import Control.Lens.TH


newtype LocalDifferentialEqn ㄇ x y = LocalDifferentialEqn {
      _rescanDifferentialEqn :: ㄇ x y
                             -> (Maybe (Shade' y), Maybe (Shade' (LocalLinear x y)))
    }
makeLenses ''LocalDifferentialEqn

type DifferentialEqn ㄇ x y = Shade (x,y) -> LocalDifferentialEqn ㄇ x y

data LocalDataPropPlan x y = LocalDataPropPlan
       { _sourcePosition :: !(Interior x)
       , _targetPosOffset :: !(Needle x)
       , _sourceData, _targetAPrioriData :: !y
       , _relatedData :: [(Needle x, y)]
       }
deriving instance (Show (Interior x), Show y, Show (Needle x))
             => Show (LocalDataPropPlan x y)

makeLenses ''LocalDataPropPlan


{-# DEPRECATED estimateLocalJacobian "Use `fitLocally`" #-}
estimateLocalJacobian :: ∀ x y . ( WithField ℝ Manifold x, Refinable y
                                 , SimpleSpace (Needle x), SimpleSpace (Needle y) )
            => Metric x -> [(Local x, Shade' y)]
                             -> Maybe (Shade' (LocalLinear x y))
estimateLocalJacobian = elj ( pseudoAffineWitness :: PseudoAffineWitness x
                            , pseudoAffineWitness :: PseudoAffineWitness y )
 where elj ( PseudoAffineWitness (SemimanifoldWitness BoundarylessWitness)
           , PseudoAffineWitness (SemimanifoldWitness BoundarylessWitness) )
        mex [(Local x₁, Shade' y₁ ey₁),(Local x₀, Shade' y₀ ey₀)]
         = return $ Shade' (dx-+|>δy)
                          (Norm . LinearFunction $ \δj -> δx ⊗ (σey<$|δj $ δx))
        where Just δx = x₁.-~.x₀
              δx' = (mex<$|δx)
              dx = δx'^/(δx'<.>^δx)
              Just δy = y₁.-~.y₀
              σey = convolveMetric ([]::[y]) ey₀ ey₁
       elj _ mex (po:ps)
           | DualSpaceWitness <- dualSpaceWitness :: DualNeedleWitness y
           , length ps > 1
               = mixShade's =<< (:|) <$> estimateLocalJacobian mex ps 
                             <*> sequenceA [estimateLocalJacobian mex [po,pi] | pi<-ps]
       elj _ _ _ = return $ Shade' zeroV mempty


data AffineModel x y = AffineModel {
         _affineModelOffset :: Shade                      y
       , _affineModelLCoeff :: Shade ( Needle x  +>Needle y)
       }
makeLenses ''AffineModel


data QuadraticModel x y = QuadraticModel {
         _quadraticModelOffset :: Shade                      y
       , _quadraticModelLCoeff :: Shade ( Needle x  +>Needle y)
       , _quadraticModelQCoeff :: Shade (Needle x⊗〃+>Needle y)
       }
makeLenses ''QuadraticModel

type QModelTup s x y = ( Needle y, (Needle x+>Needle y
                                 , SymmetricTensor s (Needle x)+>(Needle y)) )



quadratic_linearRegression :: ∀ s x y .
                      ( WithField s PseudoAffine x
                      , WithField s PseudoAffine y, Geodesic y
                      , SimpleSpace (Needle x), SimpleSpace (Needle y) )
            => NE.NonEmpty (Needle x, Shade' y) -> QuadraticModel x y
quadratic_linearRegression = case ( dualSpaceWitness :: DualSpaceWitness (Needle x)
                                  , dualSpaceWitness :: DualSpaceWitness (Needle y) ) of
    (DualSpaceWitness, DualSpaceWitness) -> gLinearRegression
         (\δx -> lfun $ \(c,(b,a)) -> (a $ squareV δx) ^+^ (b $ δx) ^+^ c )
         (\cmy (cBest, (bBest, aBest)) σ
            -> let (σc, (σb, σa)) = second summandSpaceNorms $ summandSpaceNorms σ
               in QuadraticModel (Shade (cmy⊙+^cBest $ ([]::[y])) σc)
                              (Shade bBest σb)
                              (Shade aBest σa) )

gLinearRegression :: ∀ s x y ㄇ ψ.
                      ( WithField s PseudoAffine x
                      , WithField s PseudoAffine y, Geodesic y
                      , SimpleSpace (Needle x), SimpleSpace (Needle y)
                      , SimpleSpace ψ, Scalar ψ ~ s )
            => (Needle x -> ψ -+> Needle y)
               -> (Interior y -> ψ -> Variance ψ -> ㄇ x y)
               -> NE.NonEmpty (Needle x, Shade' y) -> ㄇ x y
gLinearRegression fwdCalc analyse = qlr (pseudoAffineWitness, geodesicWitness)
 where qlr :: (PseudoAffineWitness y, GeodesicWitness y)
                   -> NE.NonEmpty (Needle x, Shade' y) -> ㄇ x y
       qlr (PseudoAffineWitness (SemimanifoldWitness _), GeodesicWitness _) ps
                 = analyse cmy ψ σψ
        where Just cmy = pointsBarycenter $ _shade'Ctr.snd<$>ps
              Just vsxy = Hask.mapM (\(x, Shade' y ey) -> (x,).(,ey)<$>y.-~.cmy) ps
              ψ = linearFit_bestModel regResult
              σψ = dualNorm . (case linearFit_χν² regResult of
                                     χν² | χν² > 0, recip χν² > 0
                                            -> scaleNorm (recip $ 1 + sqrt χν²)
                                     _ -> {-Dbg.trace ("Fit for regression model requires"
               ++" well-defined χν² (which needs positive number of degrees of freedom)."
               ++"\n Data: "++show (length ps
                                * subbasisDimension (entireBasis :: SubBasis (Needle y)))
               ++"\n Model parameters: "++show (subbasisDimension
                                        (entireBasis :: SubBasis ψ)) )-}
                                          id)
                                $ linearFit_modelUncertainty regResult
              regResult = linearRegression (arr . fwdCalc) (NE.toList vsxy)

quadraticModel_derivatives :: ∀ x y .
          ( PseudoAffine x, PseudoAffine y
          , SimpleSpace (Needle x), SimpleSpace (Needle y)
          , Scalar (Needle y) ~ Scalar (Needle x) ) =>
     QuadraticModel x y -> (Shade' y, (Shade' (LocalLinear x y), Shade' (LocalBilinear x y))) 
quadraticModel_derivatives (QuadraticModel sh shð shð²)
    | (PseudoAffineWitness (SemimanifoldWitness BoundarylessWitness))
                                     :: PseudoAffineWitness y <- pseudoAffineWitness
    , DualSpaceWitness :: DualSpaceWitness (Needle x) <- dualSpaceWitness
    , DualSpaceWitness :: DualSpaceWitness (Needle y) <- dualSpaceWitness
             = (dualShade sh, ( dualShade shð
                              , linIsoTransformShade (2*^id) $ dualShade shð² ))

{-# DEPRECATED estimateLocalHessian "Use `fitLocally`" #-}
estimateLocalHessian :: ∀ x y . ( WithField ℝ Manifold x, Refinable y, Geodesic y
                                , FlatSpace (Needle x), FlatSpace (Needle y) )
            => NonEmpty (Local x, Shade' y) -> QuadraticModel x y
estimateLocalHessian pts = quadratic_linearRegression $ first getLocalOffset <$> pts


propagationCenteredModel :: ∀ x y ㄇ .
                         ( WithField ℝ Manifold x, Refinable y, Geodesic y
                         , FlatSpace (Needle x), FlatSpace (Needle y)
                         , LocalModel ㄇ )
         => LocalDataPropPlan x (Shade' y) -> ㄇ x y
propagationCenteredModel propPlan = case fitLocally (NE.toList ptsFromCenter) of
                                       Just ㄇ->ㄇ
 where ctrOffset = propPlan^.targetPosOffset^/2
       ptsFromCenter = (Local $ negateV ctrOffset :: Local x, propPlan^.sourceData)
                     :| [(Local $ δx^-^ctrOffset, shy)
                        | (δx, shy)
                            <- (propPlan^.targetPosOffset, propPlan^.targetAPrioriData)
                               : propPlan^.relatedData
                        ]


propagationCenteredQuadraticModel :: ∀ x y .
                         ( WithField ℝ Manifold x, Refinable y, Geodesic y
                         , FlatSpace (Needle x), FlatSpace (Needle y) )
         => LocalDataPropPlan x (Shade' y) -> QuadraticModel x y
propagationCenteredQuadraticModel = propagationCenteredModel


propagateDEqnSolution_loc :: ∀ x y ㄇ . (ModellableRelation x y, LocalModel ㄇ)
           => DifferentialEqn ㄇ x y
               -> LocalDataPropPlan x (Shade' y)
               -> Maybe (Shade' y)
propagateDEqnSolution_loc f propPlan
                  = pdesl (dualSpaceWitness :: DualNeedleWitness x)
                          (dualSpaceWitness :: DualNeedleWitness y)
                          (boundarylessWitness :: BoundarylessWitness x)
                          (pseudoAffineWitness :: PseudoAffineWitness y)
                          (geodesicWitness :: GeodesicWitness y)
 where pdesl DualSpaceWitness DualSpaceWitness BoundarylessWitness
             (PseudoAffineWitness (SemimanifoldWitness BoundarylessWitness))
             (GeodesicWitness _)
          | Nothing <- jacobian  = Nothing
          | otherwise            = pure result
         where (_,jacobian) = f shxy ^. rescanDifferentialEqn
                               $ propagationCenteredModel propPlan
               Just (Shade' j₀ jExpa) = jacobian
               jacobianSh :: Shade (LocalLinear x y)
               Just jacobianSh = dualShade' <$> jacobian
               mx = propPlan^.sourcePosition .+~^ propPlan^.targetPosOffset ^/ 2 :: x
               (Shade _ expax' :: Shade x)
                    = coverAllAround (propPlan^.sourcePosition)
                                     [δx | (δx,_) <- propPlan^.relatedData]
               shxy = coverAllAround (mx, mυ)
                                     [ (δx ^-^ propPlan^.targetPosOffset ^/ 2, pυ ^+^ v)
                                     | (δx,neυ) <- (zeroV, propPlan^.sourceData)
                                                  : (second id
                                                      <$> propPlan^.relatedData)
                                     , let Just pυ = neυ^.shadeCtr .-~. mυ
                                     , v <- normSpanningSystem' (neυ^.shadeNarrowness)
                                     ]
                where Just mυ = middleBetween (propPlan^.sourceData.shadeCtr)
                                              (propPlan^.targetAPrioriData.shadeCtr)
               expax = dualNorm expax'
               result :: Shade' y
               Just result = wellDefinedShade' $ convolveShade'
                        (case wellDefinedShade' $ propPlan^.sourceData of {Just s->s})
                        (case wellDefinedShade' . dualShade
                               . linearProjectShade (lfun ($ δx))
                                $ jacobianSh
                           of {Just s->s})
                where δyb = j₀ $ δx
               δx = propPlan^.targetPosOffset


type ModellableRelation x y = ( WithField ℝ Manifold x
                              , Refinable y, Geodesic y
                              , FlatSpace (Needle x), FlatSpace (Needle y) )

class LocalModel ㄇ where
  fitLocally :: ModellableRelation x y
                  => [(Local x, Shade' y)] -> Maybe (ㄇ x y)
  tweakLocalOffset :: ModellableRelation x y
                  => Lens' (ㄇ x y) (Shade y)

modelParametersOverdetMargin :: Int -> Int
modelParametersOverdetMargin n = n + round (sqrt $ fromIntegral n)


-- | Dimension of the space of affine functions on @v@.
p¹Dimension :: ∀ v p . FiniteDimensional v => p v -> Int
p¹Dimension _ = 1 + d
 where d = subbasisDimension (entireBasis :: SubBasis v)

-- | Dimension of the space of quadratic functions on @v@.
p²Dimension :: ∀ v p . FiniteDimensional v => p v -> Int
p²Dimension _ = 1 + d + (d*(d+1))`div`2
 where d = subbasisDimension (entireBasis :: SubBasis v)

instance LocalModel AffineModel where
  fitLocally = aFitL dualSpaceWitness
   where aFitL :: ∀ x y . ModellableRelation x y
                    => DualSpaceWitness (Needle y)
                      -> [(Local x, Shade' y)] -> Maybe (AffineModel x y)
         aFitL DualSpaceWitness dataPts
          | (p₀:ps, pω:_) <- splitAt (modelParametersOverdetMargin
                                        $ p¹Dimension ([]::[Needle x])) dataPts
                 = Just . gLinearRegression
                            (\δx -> lfun $ \(b,a) -> (a $ δx) ^+^ b )
                            (\cmy (bBest, aBest) σ
                               -> let (σb, σa) = summandSpaceNorms σ
                                  in AffineModel (Shade (cmy⊙+^bBest $ ([]::[y])) σb)
                                                 (Shade aBest σa) )
                     $ first getLocalOffset <$> (p₀:|ps++[pω])
  tweakLocalOffset = affineModelOffset

instance LocalModel QuadraticModel where
  fitLocally = qFitL
   where qFitL :: ∀ x y . ModellableRelation x y
                    => [(Local x, Shade' y)] -> Maybe (QuadraticModel x y)
         qFitL dataPts
          | (p₀:ps, pω:_) <- splitAt (modelParametersOverdetMargin
                                        $ p²Dimension ([]::[Needle x])) dataPts
                 = Just . quadratic_linearRegression
                     $ first getLocalOffset <$> (p₀:|ps++[pω])
  tweakLocalOffset = quadraticModelOffset
