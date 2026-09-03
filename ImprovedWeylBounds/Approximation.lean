import ImprovedWeylBounds.External.Statements

/-!
# Exact simultaneous-approximation records

The paper writes these conclusions with Vinogradov notation.  These records
keep the constants, loss exponent, denominator and every coefficient bound
explicit.
-/

namespace ImprovedWeylBounds

/-- Preliminary denominator data at Baker's canonical accuracy. -/
structure PreliminaryApproximation (k N : ℕ) (α : CoefficientVector k) where
  r : ℕ
  r_pos : 0 < r
  numerator : Fin k → ℤ
  primitive : External.TailPrimitive r numerator
  accurate : ∀ j : Fin k, 1 ≤ j.val →
    |(r : ℝ) * α j - (numerator j : ℝ)| ≤
      Real.rpow (N : ℝ) (1 - ((j.val + 1 : ℕ) : ℝ)) /
        (4 * (k : ℝ) ^ 4)

/-- The common-denominator conclusion, with an explicit multiplicative
constant and an explicit power loss. -/
structure SimultaneousApproximation (k N : ℕ) (α : CoefficientVector k)
    (A loss C : ℝ) where
  q : ℕ
  q_pos : 0 < q
  numerator : Fin k → ℤ
  denominator_bound :
    (q : ℝ) ≤ C * (((N : ℝ) / A) ^ k) * Real.rpow (N : ℝ) loss
  coefficient_bound : ∀ j : Fin k,
    |(q : ℝ) * α j - (numerator j : ℝ)| ≤
      C * (((N : ℝ) / A) ^ k) *
        Real.rpow (N : ℝ) (-((j.val + 1 : ℕ) : ℝ) + loss)

end ImprovedWeylBounds
