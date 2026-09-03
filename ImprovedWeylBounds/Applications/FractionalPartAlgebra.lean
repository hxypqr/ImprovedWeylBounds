import ImprovedWeylBounds.Approximation

/-!
# Algebra for the small-fractional-parts application

These lemmas verify the internal step that turns simultaneous approximation
of `n α_j` into a small fractional part for
`α₁ n + ⋯ + αₖ nᵏ`.
-/

open scoped BigOperators

namespace ImprovedWeylBounds
namespace Applications

noncomputable section

/-- Distance modulo one satisfies the triangle inequality. -/
theorem distToInt_add_le (x y : ℝ) :
    distToInt (x + y) ≤ distToInt x + distToInt y := by
  change ‖((x + y : ℝ) : UnitAddCircle)‖ ≤
    ‖((x : ℝ) : UnitAddCircle)‖ + ‖((y : ℝ) : UnitAddCircle)‖
  simpa using norm_add_le ((x : ℝ) : UnitAddCircle) ((y : ℝ) : UnitAddCircle)

/-- Finite-sum form of the triangle inequality modulo one. -/
theorem distToInt_sum_le {ι : Type*}
    (s : Finset ι) (f : ι → ℝ) :
    distToInt (∑ i ∈ s, f i) ≤ ∑ i ∈ s, distToInt (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [distToInt]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (distToInt_add_le (f i) (∑ x ∈ s, f x)).trans
        (by simpa [add_comm] using add_le_add_left ih (distToInt (f i)))

/-- If `n α` is close to an integer, then `α n^j` is at most
`n^(j-1)` times as far from an integer. -/
theorem distToInt_monomial_le
    (α : ℝ) (n j : ℕ) (hj : 1 ≤ j) :
    distToInt (α * (n : ℝ) ^ j) ≤
      (n : ℝ) ^ (j - 1) * distToInt ((n : ℝ) * α) := by
  let z : ℤ := (n ^ (j - 1) : ℤ) * round ((n : ℝ) * α)
  have hpow : (n : ℝ) ^ j = (n : ℝ) ^ (j - 1) * (n : ℝ) := by
    conv_lhs => rw [show j = (j - 1) + 1 by omega]
    rw [pow_succ]
  calc
    distToInt (α * (n : ℝ) ^ j) ≤
        |α * (n : ℝ) ^ j - (z : ℝ)| :=
      distToInt_le_abs_sub_int _ z
    _ = |(n : ℝ) ^ (j - 1) *
          ((n : ℝ) * α - (round ((n : ℝ) * α) : ℝ))| := by
      congr 1
      rw [hpow]
      simp only [z, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
      ring_nf
    _ = (n : ℝ) ^ (j - 1) *
          |(n : ℝ) * α - (round ((n : ℝ) * α) : ℝ)| := by
      rw [abs_mul, abs_of_nonneg (pow_nonneg (Nat.cast_nonneg n) _)]
    _ = (n : ℝ) ^ (j - 1) * distToInt ((n : ℝ) * α) := by
      rw [distToInt_eq_abs_sub_round]

/-- Coefficientwise simultaneous approximations control the complete
polynomial value modulo one.  Index `j` represents degree `j+1`. -/
theorem distToInt_nonconstantPhase_le
    {k : ℕ} (α : CoefficientVector k) (n : ℕ) :
    distToInt (nonconstantPhase α n) ≤
      ∑ j : Fin k, (n : ℝ) ^ j.val * distToInt ((n : ℝ) * α j) := by
  calc
    distToInt (nonconstantPhase α n) ≤
        ∑ j : Fin k, distToInt (α j * (n : ℝ) ^ (j.val + 1)) := by
      exact distToInt_sum_le Finset.univ
        (fun j : Fin k => α j * (n : ℝ) ^ (j.val + 1))
    _ ≤ ∑ j : Fin k,
        (n : ℝ) ^ j.val * distToInt ((n : ℝ) * α j) := by
      apply Finset.sum_le_sum
      intro j _
      simpa using distToInt_monomial_le (α j) n (j.val + 1) (by omega)

/-- An approximation to the coefficient vector `m α` is an approximation to
`(qm) α`, with exactly the same integer numerators. -/
theorem distToInt_scaled_coefficient_le
    {k N : ℕ} (α : CoefficientVector k) (m : ℕ)
    {A loss C : ℝ}
    (approx : SimultaneousApproximation k N
      (fun j => (m : ℝ) * α j) A loss C) (j : Fin k) :
    distToInt (((approx.q * m : ℕ) : ℝ) * α j) ≤
      C * (((N : ℝ) / A) ^ k) *
        Real.rpow (N : ℝ) (-((j.val + 1 : ℕ) : ℝ) + loss) := by
  calc
    distToInt (((approx.q * m : ℕ) : ℝ) * α j) ≤
        |(((approx.q * m : ℕ) : ℝ) * α j) -
          (approx.numerator j : ℝ)| :=
      distToInt_le_abs_sub_int _ (approx.numerator j)
    _ = |(approx.q : ℝ) * ((m : ℝ) * α j) -
          (approx.numerator j : ℝ)| := by
      rw [Nat.cast_mul]
      ring_nf
    _ ≤ C * (((N : ℝ) / A) ^ k) *
        Real.rpow (N : ℝ) (-((j.val + 1 : ℕ) : ℝ) + loss) :=
      approx.coefficient_bound j

/-- Exact coefficientwise error bound for the polynomial value at the
integer `n = qm`.  The later exponent estimates in the manuscript are now
ordinary real inequalities applied to this finite sum. -/
theorem distToInt_polynomial_at_denominator_multiple_le
    {k N : ℕ} (α : CoefficientVector k) (m : ℕ)
    {A loss C : ℝ}
    (approx : SimultaneousApproximation k N
      (fun j => (m : ℝ) * α j) A loss C) :
    distToInt (nonconstantPhase α (approx.q * m)) ≤
      ∑ j : Fin k,
        ((approx.q * m : ℕ) : ℝ) ^ j.val *
          (C * (((N : ℝ) / A) ^ k) *
            Real.rpow (N : ℝ) (-((j.val + 1 : ℕ) : ℝ) + loss)) := by
  calc
    distToInt (nonconstantPhase α (approx.q * m)) ≤
        ∑ j : Fin k,
          ((approx.q * m : ℕ) : ℝ) ^ j.val *
            distToInt (((approx.q * m : ℕ) : ℝ) * α j) :=
      distToInt_nonconstantPhase_le α (approx.q * m)
    _ ≤ ∑ j : Fin k,
        ((approx.q * m : ℕ) : ℝ) ^ j.val *
          (C * (((N : ℝ) / A) ^ k) *
            Real.rpow (N : ℝ) (-((j.val + 1 : ℕ) : ℝ) + loss)) := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left
        (distToInt_scaled_coefficient_le α m approx j)
        (pow_nonneg (Nat.cast_nonneg _) _)

end

end Applications
end ImprovedWeylBounds
