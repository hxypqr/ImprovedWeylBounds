import ImprovedWeylBounds.Approximation

/-!
# Exact inverse-principle interfaces and the combined branch

The new argument has denominator `K k`; classical Weyl differencing has
denominator `2^(k-1)`.  This file proves the entirely internal step at
`main.tex:1063-1065`: choosing the stronger branch gives denominator
`Delta k = min (2^(k-1)) (K k)`.
-/

namespace ImprovedWeylBounds.Conditional

open ImprovedWeylBounds External

/-- A uniformly quantified large-value inverse principle with threshold
denominator `D`.  The threshold margin and conclusion loss are independent. -/
def InversePrinciple (k D : ℕ) : Prop :=
  ∀ thresholdMargin loss : ℝ, 0 < thresholdMargin → 0 < loss →
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
      ∀ (N : ℕ), N₀ ≤ N → ∀ (α : CoefficientVector k) (A : ℝ),
        0 < A → A ≤ ‖g α N‖ →
        Real.rpow (N : ℝ)
            (1 - 1 / (D : ℝ) + thresholdMargin) < A →
        Nonempty (SimultaneousApproximation k N α A loss C)

/-- The cited classical inverse theorem supplies the corresponding exact
principle with denominator `2^(k-1)`. -/
theorem inversePrinciple_of_classical
    (hClassical : ClassicalInverse) (k : ℕ) (hk : 3 ≤ k) :
    InversePrinciple k (2 ^ (k - 1)) := by
  intro δ η hδ hη
  obtain ⟨C, hC, N₀, hN₀, hmain⟩ := hClassical k hk δ η hδ hη
  refine ⟨C, hC, N₀, hN₀, fun N hN α A hA hlarge hamp ↦ ?_⟩
  obtain ⟨q, a, hq, _hprimitive, hqBound, haBound⟩ :=
    hmain N hN α A hA hlarge hamp
  exact ⟨⟨q, hq, a, hqBound, haBound⟩⟩

/-- Corollary 1.4: taking the appropriate one of the new and classical
branches yields the threshold governed by `Delta k`. -/
theorem combinedInverse
    (k : ℕ) (hk : 3 ≤ k)
    (hNew : InversePrinciple k (K k))
    (hClassical : ClassicalInverse) :
    InversePrinciple k (Delta k) := by
  by_cases hbranch : K k ≤ 2 ^ (k - 1)
  · have hDelta : Delta k = K k := by simp [Delta, hbranch]
    simpa [hDelta] using hNew
  · have hpow : 2 ^ (k - 1) ≤ K k := Nat.le_of_not_ge hbranch
    have hDelta : Delta k = 2 ^ (k - 1) := by simp [Delta, hpow]
    simpa [hDelta] using inversePrinciple_of_classical hClassical k hk

end ImprovedWeylBounds.Conditional
