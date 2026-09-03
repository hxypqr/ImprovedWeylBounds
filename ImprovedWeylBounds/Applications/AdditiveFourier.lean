import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-!
# Finite additive Fourier inversion

This file verifies the algebraic Fourier-inversion step used in the proof of
the additive-basis corollary.  The analytic estimate for the nonzero
frequencies is deliberately a separate input; orthogonality and the exact
representation formula are proved here.
-/

open scoped BigOperators

namespace ImprovedWeylBounds
namespace Applications

noncomputable section

/-- The exponential sum attached to a finite parametrised subset of
`ZMod p`. -/
def finiteFieldExpSum {p : ℕ} [NeZero p] {ι : Type*} [Fintype ι]
    (P : ι → ZMod p) (t : ZMod p) : ℂ :=
  ∑ n : ι, ZMod.stdAddChar (t * P n)

/-- The number of ordered `s`-term representations of `a` by the values of
`P`. -/
def representationCount {p s : ℕ} {ι : Type*} [Fintype ι]
    (P : ι → ZMod p) (a : ZMod p) : ℕ :=
  Fintype.card {v : Fin s → ι // ∑ i, P (v i) = a}

/-- Orthogonality of the standard additive character, with the normalization
used in finite Fourier inversion. -/
theorem normalized_stdAddChar_sum (p : ℕ) [NeZero p] (b : ZMod p) :
    (1 / (p : ℂ)) * ∑ t : ZMod p, ZMod.stdAddChar (t * b) =
      if b = 0 then 1 else 0 := by
  rw [AddChar.sum_mulShift b (ZMod.isPrimitive_stdAddChar p)]
  by_cases hb : b = 0
  · simp [hb, ZMod.card, NeZero.ne p]
  · simp [hb]

/-- Exact Fourier inversion for the ordered representation count.  This is
Equation (7.6) of the paper before estimating its nonzero-frequency part. -/
theorem representationCount_eq_fourier
    (p s : ℕ) [NeZero p] {ι : Type*} [Fintype ι]
    (P : ι → ZMod p) (a : ZMod p) :
    (representationCount (s := s) P a : ℂ) =
      (1 / (p : ℂ)) * ∑ t : ZMod p,
        ZMod.stdAddChar (-t * a) * (finiteFieldExpSum P t) ^ s := by
  classical
  rw [representationCount, Fintype.card_subtype]
  rw [← Finset.sum_boole]
  simp only [finiteFieldExpSum, Fintype.sum_pow]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  rw [← Finset.mul_sum]
  have hprod (t : ZMod p) :
      ∏ i, ZMod.stdAddChar (t * P (v i)) =
        ZMod.stdAddChar (t * ∑ i, P (v i)) := by
    rw [Finset.mul_sum]
    symm
    induction (Finset.univ : Finset (Fin s)) using Finset.induction_on with
    | empty => simp
    | @insert i u hi ih =>
        rw [Finset.sum_insert hi, ZMod.stdAddChar.map_add_eq_mul,
          Finset.prod_insert hi, ih]
  simp_rw [hprod]
  have hphase (t : ZMod p) :
      ZMod.stdAddChar (-t * a) *
          ZMod.stdAddChar (t * ∑ i, P (v i)) =
        ZMod.stdAddChar (t * ((∑ i, P (v i)) - a)) := by
    rw [← ZMod.stdAddChar.map_add_eq_mul]
    congr 1
    ring
  simp_rw [hphase]
  rw [normalized_stdAddChar_sum]
  simp only [sub_eq_zero]

/-- The total contribution of the nonzero Fourier modes is bounded by the
largest nonzero exponential sum to the `s`th power.  The factor `p-1` from
the triangle inequality is cancelled by the Fourier normalization `1/p`. -/
theorem representationCount_error_le
    (p s : ℕ) [NeZero p] {ι : Type*} [Fintype ι]
    (P : ι → ZMod p) (a : ZMod p) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ t : ZMod p, t ≠ 0 → ‖finiteFieldExpSum P t‖ ≤ B) :
    ‖(representationCount (s := s) P a : ℂ) -
        (1 / (p : ℂ)) * (Fintype.card ι : ℂ) ^ s‖ ≤ B ^ s := by
  classical
  let term : ZMod p → ℂ := fun t =>
    ZMod.stdAddChar (-t * a) * (finiteFieldExpSum P t) ^ s
  have hzero : term 0 = (Fintype.card ι : ℂ) ^ s := by
    simp [term, finiteFieldExpSum]
  have hdecomp :
      (representationCount (s := s) P a : ℂ) -
          (1 / (p : ℂ)) * (Fintype.card ι : ℂ) ^ s =
        (1 / (p : ℂ)) * ∑ t ∈ (Finset.univ.erase (0 : ZMod p)), term t := by
    rw [representationCount_eq_fourier]
    change (1 / (p : ℂ)) * ∑ t, term t -
        (1 / (p : ℂ)) * (Fintype.card ι : ℂ) ^ s = _
    rw [← Finset.sum_erase_add Finset.univ term
      (Finset.mem_univ (0 : ZMod p)), hzero]
    ring
  rw [hdecomp, norm_mul]
  calc
    ‖(1 / (p : ℂ))‖ * ‖∑ t ∈ Finset.univ.erase (0 : ZMod p), term t‖
        ≤ ‖(1 / (p : ℂ))‖ *
            ∑ t ∈ Finset.univ.erase (0 : ZMod p), ‖term t‖ := by
          gcongr
          exact norm_sum_le _ _
    _ ≤ ‖(1 / (p : ℂ))‖ *
          ∑ _t ∈ Finset.univ.erase (0 : ZMod p), B ^ s := by
        gcongr with t ht
        have ht0 : t ≠ 0 := by simpa using ht
        simp only [term, norm_mul, norm_pow]
        have hchar : ‖ZMod.stdAddChar (-t * a)‖ = 1 := by
          rw [ZMod.stdAddChar_apply]
          exact Circle.norm_coe _
        rw [hchar, one_mul]
        exact pow_le_pow_left₀ (norm_nonneg _) (hbound t ht0) s
    _ ≤ B ^ s := by
      have hp : 0 < p := NeZero.pos p
      have hcard : (Finset.univ.erase (0 : ZMod p)).card = p - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ (0 : ZMod p)),
          Finset.card_univ, ZMod.card]
      rw [Finset.sum_const, nsmul_eq_mul, hcard]
      have hpR : (0 : ℝ) < p := by exact_mod_cast hp
      have hpow : 0 ≤ B ^ s := pow_nonneg hB s
      have hnorm : ‖(1 / (p : ℂ))‖ = 1 / (p : ℝ) := by
        rw [norm_div, norm_one, norm_natCast]
      rw [hnorm, one_div, inv_mul_eq_div]
      exact (div_le_iff₀ hpR).2 (by
        calc
          ((p - 1 : ℕ) : ℝ) * B ^ s ≤ (p : ℝ) * B ^ s := by
            gcongr
            exact_mod_cast Nat.sub_le p 1
          _ = B ^ s * p := by ring)

/-- A clean exact positivity criterion for the additive-basis argument.  It
contains no asymptotic notation: any analytic bound `B` satisfying the
displayed strict inequality forces every residue to be represented. -/
theorem representationCount_pos_of_nonzero_bound
    (p s : ℕ) [NeZero p] {ι : Type*} [Fintype ι]
    (P : ι → ZMod p) (a : ZMod p) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ t : ZMod p, t ≠ 0 → ‖finiteFieldExpSum P t‖ ≤ B)
    (hmain : B ^ s < (Fintype.card ι : ℝ) ^ s / (p : ℝ)) :
    0 < representationCount (s := s) P a := by
  have herr := representationCount_error_le p s P a B hB hbound
  by_contra hnot
  have hcount : representationCount (s := s) P a = 0 := Nat.eq_zero_of_not_pos hnot
  rw [hcount, Nat.cast_zero, zero_sub, norm_neg] at herr
  have hnormmain :
      ‖(1 / (p : ℂ)) * (Fintype.card ι : ℂ) ^ s‖ =
        (Fintype.card ι : ℝ) ^ s / (p : ℝ) := by
    rw [norm_mul, norm_div, norm_one, norm_natCast, norm_pow, norm_natCast]
    ring
  rw [hnormmain] at herr
  exact (not_le_of_gt hmain) herr

end

end Applications
end ImprovedWeylBounds
