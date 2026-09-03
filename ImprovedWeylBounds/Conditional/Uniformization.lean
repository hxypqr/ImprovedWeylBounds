import ImprovedWeylBounds.Conditional.Main

/-!
# Removing the sufficiently-large interval threshold

Analytic arguments naturally produce a threshold `H₀`.  The manuscript's
displayed theorems are stated for every `H ≥ 1`; the finitely many smaller
lengths are absorbed into the implied constant using the trivial bound.  This
file checks that last uniformization step explicitly.
-/

open scoped BigOperators
open Polynomial

namespace ImprovedWeylBounds.Conditional

open ImprovedWeylBounds External

/-- Trivial bound for a polynomial sum over exactly `H` integers. -/
theorem norm_polynomialShortSum_le
    (P : ℝ[X]) (M : ℤ) (H : ℕ) :
    ‖polynomialShortSum P M H‖ ≤ H := by
  rw [polynomialShortSum]
  calc
    ‖∑ n ∈ Finset.Icc 1 H,
        e (P.eval ((M : ℝ) + (n : ℝ)))‖ ≤
        ∑ n ∈ Finset.Icc 1 H,
          ‖e (P.eval ((M : ℝ) + (n : ℝ)))‖ := norm_sum_le _ _
    _ = ∑ _n ∈ Finset.Icc 1 H, (1 : ℝ) := by simp
    _ = H := by simp

/-- Literal all-`H` version of Theorem 1.1. -/
def RationalShortIntervalBoundAll (d : ℕ) (ε : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (q H : ℕ) (M : ℤ) (P : ℝ[X]) (a : ℤ),
      1 ≤ H → H ≤ q → a.natAbs.Coprime q →
      P.natDegree = d → P.coeff d = (a : ℝ) / (q : ℝ) →
      ‖polynomialShortSum P M H‖ ≤
        C *
          (Real.rpow (q : ℝ) (1 / (d : ℝ)) * Real.rpow (H : ℝ) ε +
            Real.rpow (H : ℝ) (1 - 1 / (Delta d : ℝ) + ε))

private theorem one_le_raw_rpow {x a : ℝ} (hx : 1 ≤ x) (ha : 0 ≤ a) :
    1 ≤ Real.rpow x a := by
  have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hx ha
  change Real.rpow 1 a ≤ Real.rpow x a at h
  have hone : Real.rpow 1 a = 1 := by simp [Real.rpow]
  rwa [hone] at h

/-- The large-`H` estimate plus the trivial bound gives the theorem for every
positive interval length. -/
theorem rationalShortIntervalBoundAll_of_eventual
    (d : ℕ) (hd : 3 ≤ d) (ε : ℝ) (hε : 0 < ε)
    (hEventual : RationalShortIntervalBound d ε) :
    RationalShortIntervalBoundAll d ε := by
  obtain ⟨C, hC, H₀, hH₀, hbound⟩ := hEventual
  let C' : ℝ := max C H₀
  have hC'C : C ≤ C' := le_max_left _ _
  have hC'H₀ : (H₀ : ℝ) ≤ C' := le_max_right _ _
  have hC' : 0 < C' := hC.trans_le hC'C
  refine ⟨C', hC', ?_⟩
  intro q H M P a hH hHq hcop hdeg hlead
  let Q : ℝ :=
    Real.rpow (q : ℝ) (1 / (d : ℝ)) * Real.rpow (H : ℝ) ε +
      Real.rpow (H : ℝ) (1 - 1 / (Delta d : ℝ) + ε)
  have hQnonneg : 0 ≤ Q := by
    dsimp [Q]
    positivity
  by_cases hHlarge : H₀ ≤ H
  · have h := hbound q H M P a hHlarge hH hHq hcop hdeg hlead
    exact h.trans (mul_le_mul_of_nonneg_right hC'C hQnonneg)
  · have hqone : (1 : ℝ) ≤ q := by exact_mod_cast hH.trans hHq
    have hHone : (1 : ℝ) ≤ H := by exact_mod_cast hH
    have hdR : (0 : ℝ) < d := by positivity
    have hqpow : 1 ≤ Real.rpow (q : ℝ) (1 / (d : ℝ)) :=
      one_le_raw_rpow hqone (by positivity)
    have hHpow : 1 ≤ Real.rpow (H : ℝ) ε :=
      one_le_raw_rpow hHone hε.le
    have hfirst : 1 ≤
        Real.rpow (q : ℝ) (1 / (d : ℝ)) * Real.rpow (H : ℝ) ε :=
      one_le_mul_of_one_le_of_one_le hqpow hHpow
    have hQone : 1 ≤ Q := by
      dsimp [Q]
      exact hfirst.trans (le_add_of_nonneg_right (Real.rpow_nonneg (by positivity) _))
    have hHH₀ : (H : ℝ) ≤ H₀ := by
      exact_mod_cast (Nat.le_of_lt (lt_of_not_ge hHlarge))
    calc
      ‖polynomialShortSum P M H‖ ≤ H := norm_polynomialShortSum_le P M H
      _ ≤ H₀ := hHH₀
      _ ≤ C' := hC'H₀
      _ = C' * 1 := by ring
      _ ≤ C' * Q := mul_le_mul_of_nonneg_left hQone hC'.le

/-- Literal all-`H` finite-field statement. -/
def FiniteFieldShortIntervalBoundAll (d : ℕ) (ε : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (p H : ℕ), p.Prime → d < p →
      ∀ (M : ℤ) (P : (ZMod p)[X]),
        1 ≤ H → H ≤ p → P.natDegree = d →
        ‖finiteFieldShortSum d p P M H‖ ≤
          C *
            (Real.rpow (p : ℝ) (1 / (d : ℝ)) * Real.rpow (H : ℝ) ε +
              Real.rpow (H : ℝ) (1 - 1 / (Delta d : ℝ) + ε))

/-- The all-`H` prime-field corollary follows by coefficient lifting from the
literal all-`H` rational statement. -/
theorem finiteFieldShortIntervalBoundAll_of_rational
    (d : ℕ) (hd : 3 ≤ d) (ε : ℝ) (_hε : 0 < ε)
    (hRational : RationalShortIntervalBoundAll d ε) :
    FiniteFieldShortIntervalBoundAll d ε := by
  obtain ⟨C, hC, hrat⟩ := hRational
  refine ⟨C, hC, ?_⟩
  intro p H hp hdp M P hH hHp hdeg
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hPne : P ≠ 0 := by
    intro hzero
    rw [hzero] at hdeg
    simp at hdeg
    omega
  have hcoeff : P.coeff d ≠ 0 := by
    rw [← hdeg]
    exact Polynomial.leadingCoeff_ne_zero.mpr hPne
  have hcop : (P.coeff d).val.Coprime p :=
    coprime_val_of_prime hp (P.coeff d) hcoeff
  have hliftdeg : (normalizedZModLift d p P).natDegree = d :=
    natDegree_normalizedZModLift d p (by omega) P hdeg
  have hliftcoeff :
      (normalizedZModLift d p P).coeff d =
        ((P.coeff d).val : ℝ) / (p : ℝ) :=
    coeff_normalizedZModLift_top d p P
  simpa [finiteFieldShortSum] using
    hrat p H M (normalizedZModLift d p P) (P.coeff d).val
      hH hHp hcop hliftdeg hliftcoeff

/-- Fully assembled all-`H` rational theorem with the explicit external and
preliminary-approximation boundary. -/
theorem rationalShortIntervalBoundAll_of_external_and_preliminary
    (hBaker : BakerCompression) (hClassical : ClassicalInverse)
    (d : ℕ) (hd : 3 ≤ d) (ε : ℝ) (hε : 0 < ε)
    (hPreliminary : PreliminaryApproximationPrinciple d) :
    RationalShortIntervalBoundAll d ε :=
  rationalShortIntervalBoundAll_of_eventual d hd ε hε
    (rationalShortIntervalBound_of_external_and_preliminary
      hBaker hClassical d hd ε hε hPreliminary)

/-- Fully assembled all-`H` prime-field theorem with the same boundary. -/
theorem finiteFieldShortIntervalBoundAll_of_external_and_preliminary
    (hBaker : BakerCompression) (hClassical : ClassicalInverse)
    (d : ℕ) (hd : 3 ≤ d) (ε : ℝ) (hε : 0 < ε)
    (hPreliminary : PreliminaryApproximationPrinciple d) :
    FiniteFieldShortIntervalBoundAll d ε :=
  finiteFieldShortIntervalBoundAll_of_rational d hd ε hε
    (rationalShortIntervalBoundAll_of_external_and_preliminary
      hBaker hClassical d hd ε hε hPreliminary)

end ImprovedWeylBounds.Conditional
