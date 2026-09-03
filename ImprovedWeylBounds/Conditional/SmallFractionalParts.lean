import ImprovedWeylBounds.Applications.LargeMultiple
import ImprovedWeylBounds.Applications.FractionalPartAlgebra
import ImprovedWeylBounds.Conditional.Inverse

/-!
# Conditional small-fractional-parts reduction

This module joins Baker's external large-multiple lemma to the combined
inverse principle.  The choice of `M` and the final power-exponent estimates
remain explicit numerical hypotheses, rather than being hidden behind
“harmless adjustment of parameters”.
-/

namespace ImprovedWeylBounds.Conditional

open ImprovedWeylBounds External Applications

/-- If the average term `N/(6M)` already clears the inverse-theorem
threshold, failure to find a small fractional part produces a simultaneous
approximation for one scaled coefficient vector `m α`. -/
theorem largeMultiple_to_simultaneousApproximation
    (hLargeMultiple : LargeMultiple) {k : ℕ} {D : ℕ}
    (hInverse : InversePrinciple k D)
    (thresholdMargin loss : ℝ)
    (hmargin : 0 < thresholdMargin) (hloss : 0 < loss) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
      ∀ (N M : ℕ), N₀ ≤ N → 2 ≤ M →
        Real.rpow (N : ℝ)
            (1 - 1 / (D : ℝ) + thresholdMargin) <
          (N : ℝ) / (6 * M) →
        ∀ α : CoefficientVector k,
          (∀ n : Fin N,
            1 / (M : ℝ) <
              distToInt (nonconstantPhase α (n.val + 1))) →
          ∃ m ∈ Finset.Icc 1 M,
            Nonempty (SimultaneousApproximation k N
              (fun j => (m : ℝ) * α j)
              ((N : ℝ) / (6 * M)) loss C) := by
  obtain ⟨C, hC, N₀, hN₀, hinv⟩ :=
    hInverse thresholdMargin loss hmargin hloss
  refine ⟨C, hC, N₀, hN₀, ?_⟩
  intro N M hN hM hthreshold α haway
  have hNone : 1 ≤ N := hN₀.trans hN
  obtain ⟨m, hm, hlarge⟩ :=
    exists_large_scaled_weyl_sum hLargeMultiple α N M hNone hM haway
  have hApos : 0 < (N : ℝ) / (6 * M) := by positivity
  have happ := hinv N hN (fun j => (m : ℝ) * α j)
    ((N : ℝ) / (6 * M)) hApos hlarge.le hthreshold
  exact ⟨m, hm, happ⟩

end ImprovedWeylBounds.Conditional
