import ImprovedWeylBounds.Basic

/-!
# Elementary facts about Weyl sums

These estimates use only the triangle inequality and the fact that the
additive character has modulus one.
-/

open scoped BigOperators

namespace ImprovedWeylBounds

/-- The trivial bound `|gₖ(α;N)| ≤ N`. -/
theorem norm_g_le {k : ℕ} (α : CoefficientVector k) (N : ℕ) :
    ‖g α N‖ ≤ N := by
  calc
    ‖g α N‖ ≤ ∑ n ∈ Finset.Icc 1 N, ‖e (nonconstantPhase α n)‖ := by
      simpa [g] using norm_sum_le (s := Finset.Icc 1 N)
        (fun n : ℕ ↦ e (nonconstantPhase α n))
    _ = ∑ _n ∈ Finset.Icc 1 N, (1 : ℝ) := by simp
    _ = N := by simp

/-- If `A` is a positive lower bound for a Weyl sum, then `N/A ≥ 1`. -/
theorem one_le_length_div_amplitude {k N : ℕ} {α : CoefficientVector k} {A : ℝ}
    (hA : 0 < A) (hlarge : A ≤ ‖g α N‖) :
    1 ≤ (N : ℝ) / A := by
  have hAN : A ≤ (N : ℝ) := hlarge.trans (norm_g_le α N)
  exact (le_div_iff₀ hA).2 (by simpa using hAN)

/-- Raising `N/A` to any positive natural power can only increase it. -/
theorem length_div_amplitude_le_pow {k N : ℕ} {α : CoefficientVector k} {A : ℝ}
    (hA : 0 < A) (hlarge : A ≤ ‖g α N‖)
    {m : ℕ} (hm : 1 ≤ m) :
    (N : ℝ) / A ≤ ((N : ℝ) / A) ^ m := by
  exact le_self_pow₀ (one_le_length_div_amplitude hA hlarge)
    (Nat.one_le_iff_ne_zero.mp hm)

end ImprovedWeylBounds
