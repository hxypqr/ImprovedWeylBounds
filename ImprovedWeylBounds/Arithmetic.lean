import ImprovedWeylBounds.Basic

/-!
# Elementary rational separation

This file proves the arithmetic fact used at `main.tex:1096-1099`: a
nonintegral rational with denominator `q` is at distance at least `1/q` from
the integers.  No analytic-number-theory input is involved.
-/

namespace ImprovedWeylBounds

theorem distToInt_nonneg (x : ℝ) : 0 ≤ distToInt x := by
  simp [distToInt]

/-- A rational whose numerator is not divisible by its positive denominator
is separated from every integer by at least the reciprocal denominator. -/
theorem one_div_le_distToInt_int_div
    {num : ℤ} {q : ℕ} (hq : 0 < q) (hnot : ¬ (q : ℤ) ∣ num) :
    1 / (q : ℝ) ≤ distToInt ((num : ℝ) / (q : ℝ)) := by
  let z : ℤ := round ((num : ℝ) / (q : ℝ))
  have hdiff : num - z * (q : ℤ) ≠ 0 := by
    intro hzero
    apply hnot
    refine ⟨z, ?_⟩
    have hz : num = z * (q : ℤ) := sub_eq_zero.mp hzero
    simpa [mul_comm] using hz
  have hone : (1 : ℝ) ≤ |((num - z * (q : ℤ) : ℤ) : ℝ)| := by
    exact_mod_cast (Int.one_le_abs hdiff)
  have hqreal : 0 < (q : ℝ) := by exact_mod_cast hq
  have hdiv :
      1 / (q : ℝ) ≤
        |((num - z * (q : ℤ) : ℤ) : ℝ)| / (q : ℝ) :=
    (div_le_div_iff_of_pos_right hqreal).2 hone
  dsimp [z] at hdiv
  rw [distToInt_eq_abs_sub_round]
  calc
    1 / (q : ℝ) ≤
        |((num - round ((num : ℝ) / (q : ℝ)) * (q : ℤ) : ℤ) : ℝ)| /
          (q : ℝ) := hdiv
    _ = |((num - round ((num : ℝ) / (q : ℝ)) * (q : ℤ) : ℤ) : ℝ) /
          (q : ℝ)| := by rw [abs_div, abs_of_pos hqreal]
    _ = |(num : ℝ) / (q : ℝ) - (round ((num : ℝ) / (q : ℝ)) : ℝ)| := by
      congr 1
      push_cast
      field_simp

/-- Coprimality and `1 ≤ r < q` imply that `q` does not divide `ra`. -/
theorem not_intCast_dvd_mul_of_coprime_lt
    {a r q : ℕ} (haq : a.Coprime q) (hr : 0 < r) (hrq : r < q) :
    ¬ (q : ℤ) ∣ (r * a : ℕ) := by
  intro hdvd
  have hdvdNat : q ∣ r * a := by exact_mod_cast hdvd
  have hqr : q ∣ r := (haq.symm.dvd_mul_right).mp hdvdNat
  have hle : q ≤ r := Nat.le_of_dvd hr hqr
  exact (not_le_of_gt hrq) hle

/-- The reduced-fraction separation used in the rational short-interval
argument. -/
theorem reduced_fraction_separation
    {a r q : ℕ} (haq : a.Coprime q) (hr : 0 < r) (hrq : r < q) :
    1 / (q : ℝ) ≤
      distToInt (((r : ℝ) * (a : ℝ)) / (q : ℝ)) := by
  have hq : 0 < q := lt_trans hr hrq
  have hnot : ¬ (q : ℤ) ∣ (r * a : ℕ) :=
    not_intCast_dvd_mul_of_coprime_lt haq hr hrq
  have h := one_div_le_distToInt_int_div (num := ((r * a : ℕ) : ℤ)) hq hnot
  simpa [Nat.cast_mul] using h

/-- Integer-numerator form of reduced-fraction separation.  This is the
literal form needed for a real polynomial whose leading numerator may be
negative. -/
theorem reduced_fraction_separation_int
    {a : ℤ} {r q : ℕ} (haq : a.natAbs.Coprime q)
    (hr : 0 < r) (hrq : r < q) :
    1 / (q : ℝ) ≤
      distToInt (((r : ℝ) * (a : ℝ)) / (q : ℝ)) := by
  have hq : 0 < q := lt_trans hr hrq
  have hnot : ¬(q : ℤ) ∣ (r : ℤ) * a := by
    intro hdvd
    have hdvdNat : q ∣ ((r : ℤ) * a).natAbs := Int.natCast_dvd.mp hdvd
    have hqra : q ∣ r * a.natAbs := by
      simpa [Int.natAbs_mul] using hdvdNat
    have hqr : q ∣ r := (haq.symm.dvd_mul_right).mp hqra
    exact (not_le_of_gt hrq) (Nat.le_of_dvd hr hqr)
  have h := one_div_le_distToInt_int_div
    (num := (r : ℤ) * a) hq hnot
  simpa only [Int.cast_mul, Int.cast_natCast] using h

end ImprovedWeylBounds
