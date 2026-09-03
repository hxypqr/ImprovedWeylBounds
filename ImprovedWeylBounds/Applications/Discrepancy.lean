import ImprovedWeylBounds.External.Statements

/-!
# Internal discrepancy deduction

This file checks the finite inequality used after the externally quoted
Erdős--Turán theorem.  A uniform exponential-sum bound at all frequencies
`1 ≤ h ≤ M` is converted into an explicit count-discrepancy bound.
-/

open scoped BigOperators

namespace ImprovedWeylBounds
namespace Applications

noncomputable section

/-- A discrepancy upper bound may be enlarged. -/
theorem halfOpenDiscrepancyAtMost_mono
    {H : ℕ} {x : Fin H → ℝ} {B B' : ℝ}
    (h : External.HalfOpenDiscrepancyAtMost x B) (hBB' : B ≤ B') :
    External.HalfOpenDiscrepancyAtMost x B' := by
  intro a b ha hab hb
  exact (h a b ha hab hb).trans hBB'

/-- Exact specialization of Erdős--Turán under a uniform bound `E` for all
frequencies through `M`. -/
theorem discrepancy_of_uniform_exponential_bound
    (hErdosTuran : External.ErdosTuran)
    (H M : ℕ) (hM : 1 ≤ M) (x : Fin H → ℝ) (E : ℝ)
    (hfreq : ∀ h ∈ Finset.Icc 1 M,
      ‖∑ n : Fin H, e ((h : ℝ) * x n)‖ ≤ E) :
    External.HalfOpenDiscrepancyAtMost x
      (3 * (H : ℝ) / (M + 1 : ℕ) +
        3 * E * ∑ h ∈ Finset.Icc 1 M, 1 / (h : ℝ)) := by
  apply halfOpenDiscrepancyAtMost_mono (hErdosTuran H M hM x)
  have hsum :
    ∑ h ∈ Finset.Icc 1 M,
        (1 / (h : ℝ)) * ‖∑ n : Fin H, e ((h : ℝ) * x n)‖
        ≤ ∑ h ∈ Finset.Icc 1 M, (1 / (h : ℝ)) * E := by
          apply Finset.sum_le_sum
          intro h hh
          have hh1 : 1 ≤ h := (Finset.mem_Icc.mp hh).1
          exact mul_le_mul_of_nonneg_left (hfreq h hh) (by positivity)
  have hrewrite :
      (∑ h ∈ Finset.Icc 1 M, (1 / (h : ℝ)) * E) =
        E * ∑ h ∈ Finset.Icc 1 M, 1 / (h : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      ring
  rw [hrewrite] at hsum
  calc
    3 * (H : ℝ) / (M + 1 : ℕ) +
        3 * ∑ h ∈ Finset.Icc 1 M,
          (1 / (h : ℝ)) * ‖∑ n : Fin H, e ((h : ℝ) * x n)‖
        ≤ 3 * (H : ℝ) / (M + 1 : ℕ) +
            3 * (E * ∑ h ∈ Finset.Icc 1 M, 1 / (h : ℝ)) := by
          gcongr
    _ = 3 * (H : ℝ) / (M + 1 : ℕ) +
          3 * E * ∑ h ∈ Finset.Icc 1 M, 1 / (h : ℝ) := by ring

/-- The same bound with the harmonic sum replaced by `1 + log M`. -/
theorem discrepancy_of_uniform_exponential_bound_log
    (hErdosTuran : External.ErdosTuran)
    (H M : ℕ) (hM : 1 ≤ M) (x : Fin H → ℝ) (E : ℝ) (hE : 0 ≤ E)
    (hfreq : ∀ h ∈ Finset.Icc 1 M,
      ‖∑ n : Fin H, e ((h : ℝ) * x n)‖ ≤ E) :
    External.HalfOpenDiscrepancyAtMost x
      (3 * (H : ℝ) / (M + 1 : ℕ) +
        3 * E * (1 + Real.log M)) := by
  apply halfOpenDiscrepancyAtMost_mono
    (discrepancy_of_uniform_exponential_bound
      hErdosTuran H M hM x E hfreq)
  have hharm :
      (∑ h ∈ Finset.Icc 1 M, 1 / (h : ℝ)) ≤ 1 + Real.log M := by
    have hb := harmonic_le_one_add_log M
    rw [harmonic_eq_sum_Icc] at hb
    simpa only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div] using hb
  gcongr

/-- An explicit version of the customary absorption of a logarithm into an
arbitrarily small power. -/
theorem one_add_log_nat_le_rpow
    (H : ℕ) (hH : 1 ≤ H) (ε : ℝ) (hε : 0 < ε) :
    1 + Real.log H ≤
      (1 + 1 / ε) * Real.rpow (H : ℝ) ε := by
  have hpow : 1 ≤ Real.rpow (H : ℝ) ε := by
    have hp := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1)
      (by exact_mod_cast hH : (1 : ℝ) ≤ H) hε.le
    change Real.rpow 1 ε ≤ Real.rpow (H : ℝ) ε at hp
    have hone : Real.rpow 1 ε = 1 := by simp [Real.rpow]
    rw [hone] at hp
    exact hp
  have hlog := Real.log_natCast_le_rpow_div H hε
  calc
    1 + Real.log H ≤
        Real.rpow (H : ℝ) ε + Real.rpow (H : ℝ) ε / ε :=
      add_le_add hpow hlog
    _ = (1 + 1 / ε) * Real.rpow (H : ℝ) ε := by ring

/-- An ordinary interval with no sample point cannot be longer than the
count-discrepancy divided by the sample size.  This is the exact algebraic
core of the omitted-interval corollary (a cyclic interval is first split at
zero, losing at most a factor two). -/
theorem empty_interval_length_le
    {H : ℕ} (hH : 1 ≤ H) {x : Fin H → ℝ} {B a b : ℝ}
    (hdisc : External.HalfOpenDiscrepancyAtMost x B)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (hempty : External.countInHalfOpenModOne x a b = 0) :
    b - a ≤ B / H := by
  have h := hdisc a b ha hab hb
  rw [hempty, Nat.cast_zero, zero_sub, abs_neg,
    abs_of_nonneg (mul_nonneg (Nat.cast_nonneg H) (sub_nonneg.mpr hab))] at h
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < H)).2
  simpa [mul_comm] using h

end

end Applications
end ImprovedWeylBounds
