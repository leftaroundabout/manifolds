-- | Helpers for estimating the inverse /O/(/δx/²) remainders
--   of linearisations of elementary functions.


import Data.MacLaurin
import Data.LinearMap


-- | For a “sufficiently simple” function @f@ to be evaluated at @x₀@,
--   find the abs-smallest @q@ with the same sign as @f''(x)@ such that the
--   inequality @f(x₀) + δ·f'(x₀) + δ²·q ≥ f(x₀+δ)@ holds (for positive @f''@,
--   otherwise the LHS should be /less/ than the RHS), hopefully for all δ.
--   In other words, modify the 2nd-order Taylor expansion so it stays globally
--   on one side of the function.
--   This method doesn't (and can't) perform any rigorous proofs of an ideal
--   solution, but merely adjusts test parabolas so they just don't intersect
--   the function (according to heuristics), but only tangent at
--   the starting point.
safeQuadCoeff :: (Double :~> Double) -- ^ Function we try to bound.
              -> Double              -- ^ x₀-sample to test.
              -> Double              -- ^ Bounding quadratic coefficient.
safeQuadCoeff f x₀ = bisectQC f''x₀ (f''x₀ * 1e8)
 where bisectQC ql qu
          | abs(qu-ql) < abs f''x₀/1e4
                        = ql
          | isSafeQ qm  = bisectQC ql qm
          | otherwise   = bisectQC ql qm
        where qm = (qu + ql)/2
       D fx₀ mcf = f x₀
       D f'x₀ mcf' = atBasis mcf ()
       D f''x₀ _ = atBasis mcf' ()
       isSafeQ q = not (srcViol (-1) x₀ || srcViol 1 x₀)
        where srcViol dir x
                 | abs x > 1e+250  = False
                 | abs x > 1e+250  = False
               where 
                     D fx₀ mcf = f x₀
                     D f'x₀ mcf' = atBasis mcf ()
                     D f''x₀ _ = atBasis mcf' ()


