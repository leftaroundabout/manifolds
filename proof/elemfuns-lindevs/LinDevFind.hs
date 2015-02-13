-- | Helpers for estimating the inverse /O/(/δx/²) remainders
--   of linearisations of elementary functions.


import Data.MacLaurin


-- | For a “sufficiently simple” function @f@ to be evaluated at @x₀@,
--   find some @q@ with the same sign as @f''(x)@ such that the inequality
--   @f(x₀) + δ·f'(x₀) + δ²·q ≥ f(x₀+δ)@ holds (for positive @f''@, otherwise the
--   LHS should be /less/ than the RHS), hopefully for all δ. In other words,
--   modify the 2nd-order Taylor expansion so it stays globally on one side
--   of the function. This method doesn't (and can't) perform any rigorous
--   proofs, but merely adjusts test parabolas so they touch the
--   function /tangentially/ at both the starting point, and the next
--   equality root encountered.
safeQuadCoeff :: (Double :~> Double) -- ^ Function we try to bound.
              -> Double              -- ^ x₀-sample to test.
              -> Double              -- ^ Bounding quadratic coefficient.
safeQuadCoeff f x₀ = undefined



