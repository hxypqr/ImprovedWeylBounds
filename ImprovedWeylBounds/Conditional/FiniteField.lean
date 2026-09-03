import ImprovedWeylBounds.Conditional.RationalBound

open scoped BigOperators
open Polynomial

namespace ImprovedWeylBounds.Conditional

noncomputable def zmodRealLift (d p : ℕ) (P : (ZMod p)[X]) : ℝ[X] :=
  ∑ n ∈ Finset.range (d + 1),
    Polynomial.monomial n ((P.coeff n).val : ℝ)

theorem coeff_zmodRealLift_of_le (d p : ℕ) (P : (ZMod p)[X])
    (n : ℕ) (hn : n ≤ d) :
    (zmodRealLift d p P).coeff n = ((P.coeff n).val : ℝ) := by
  classical
  simp [zmodRealLift, Polynomial.coeff_monomial, hn]

theorem natDegree_zmodRealLift (d p : ℕ) (hd : 0 < d) [NeZero p] (P : (ZMod p)[X])
    (hdeg : P.natDegree = d) :
    (zmodRealLift d p P).natDegree = d := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro n hn
    simp [zmodRealLift, Polynomial.coeff_monomial]
    omega
  · rw [coeff_zmodRealLift_of_le d p P d le_rfl]
    have hPne : P ≠ 0 := by
      intro hzero
      rw [hzero] at hdeg
      simp at hdeg
      omega
    have hcoeff : P.coeff d ≠ 0 := by
      rw [← hdeg]
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr hPne
    have hval : (P.coeff d).val ≠ 0 := (ZMod.val_ne_zero _).2 hcoeff
    exact_mod_cast hval

noncomputable def normalizedZModLift (d p : ℕ) (P : (ZMod p)[X]) : ℝ[X] :=
  Polynomial.C (1 / (p : ℝ)) * zmodRealLift d p P

theorem natDegree_normalizedZModLift (d p : ℕ) (hd : 0 < d) [NeZero p]
    (P : (ZMod p)[X])
    (hdeg : P.natDegree = d) :
    (normalizedZModLift d p P).natDegree = d := by
  have hLiftDegree := natDegree_zmodRealLift d p hd P hdeg
  have hLiftNe : zmodRealLift d p P ≠ 0 := by
    intro hzero
    rw [hzero] at hLiftDegree
    simp at hLiftDegree
    omega
  rw [normalizedZModLift, Polynomial.natDegree_mul]
  · simp [natDegree_zmodRealLift d p hd P hdeg]
  · simp [NeZero.ne p]
  · exact hLiftNe

theorem coeff_normalizedZModLift_top (d p : ℕ) [NeZero p]
    (P : (ZMod p)[X]) :
    (normalizedZModLift d p P).coeff d =
      ((P.coeff d).val : ℝ) / (p : ℝ) := by
  rw [normalizedZModLift, Polynomial.coeff_C_mul]
  rw [coeff_zmodRealLift_of_le d p P d le_rfl]
  ring

/-- The finite-field interval sum, realized exactly as in `main.tex:1104-1105`:
choose the canonical integer representatives of all coefficients and divide
the resulting real polynomial by `p`. -/
noncomputable def finiteFieldShortSum (d p : ℕ) (P : (ZMod p)[X])
    (M : ℤ) (H : ℕ) : ℂ :=
  polynomialShortSum (normalizedZModLift d p P) M H

/-- Fully quantified finite-field version of the short-interval bound. -/
def FiniteFieldShortIntervalBound (d : ℕ) (ε : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ H₀ : ℕ, 1 ≤ H₀ ∧
    ∀ (p H : ℕ), p.Prime → d < p →
      ∀ (M : ℤ) (P : (ZMod p)[X]),
        H₀ ≤ H → 1 ≤ H → H ≤ p → P.natDegree = d →
        ‖finiteFieldShortSum d p P M H‖ ≤
          C *
            (Real.rpow (p : ℝ) (1 / (d : ℝ)) * Real.rpow (H : ℝ) ε +
              Real.rpow (H : ℝ) (1 - 1 / (Delta d : ℝ) + ε))

theorem coprime_val_of_prime {p : ℕ} [NeZero p] (hp : p.Prime)
    (c : ZMod p) (hc : c ≠ 0) : c.val.Coprime p := by
  have hval0 : c.val ≠ 0 := (ZMod.val_ne_zero _).2 hc
  apply Nat.Coprime.symm
  apply (hp.coprime_iff_not_dvd).2
  intro hdvd
  exact (not_lt_of_ge (Nat.le_of_dvd (Nat.pos_of_ne_zero hval0) hdvd)) c.val_lt

/-- The prime-field corollary is an internal coefficient-lifting consequence
of the rational short-interval theorem. -/
theorem finiteFieldShortIntervalBound_of_rational
    (d : ℕ) (hd : 3 ≤ d) (ε : ℝ) (_hε : 0 < ε)
    (hRational : RationalShortIntervalBound d ε) :
    FiniteFieldShortIntervalBound d ε := by
  obtain ⟨C, hC, H₀, hH₀, hrat⟩ := hRational
  refine ⟨C, hC, H₀, hH₀, ?_⟩
  intro p H hp hdp M P hH₀H hHpos hHp hdeg
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hPne : P ≠ 0 := by
    intro hzero
    rw [hzero] at hdeg
    simp at hdeg
    omega
  have hcoeff : P.coeff d ≠ 0 := by
    rw [← hdeg, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hPne
  have hcop : (P.coeff d).val.Coprime p :=
    coprime_val_of_prime hp _ hcoeff
  have hliftdeg : (normalizedZModLift d p P).natDegree = d :=
    natDegree_normalizedZModLift d p (by omega) P hdeg
  have hliftcoeff :
      (normalizedZModLift d p P).coeff d =
        ((P.coeff d).val : ℝ) / (p : ℝ) :=
    coeff_normalizedZModLift_top d p P
  simpa [finiteFieldShortSum] using
    hrat p H M (normalizedZModLift d p P) (P.coeff d).val
      hH₀H hHpos hHp hcop hliftdeg hliftcoeff

/-- Combined prime-field corollary directly from the inverse principle. -/
theorem finiteFieldShortIntervalBound_of_inverse
    (d : ℕ) (hd : 3 ≤ d) (ε : ℝ) (hε : 0 < ε)
    (hInverse : InversePrinciple d (Delta d)) :
    FiniteFieldShortIntervalBound d ε :=
  finiteFieldShortIntervalBound_of_rational d hd ε hε
    (rationalShortIntervalBound_of_inverse d hd ε hε hInverse)

end ImprovedWeylBounds.Conditional
