import ImprovedWeylBounds.Approximation
import ImprovedWeylBounds.WeylSum

/-!
# Internal assembly after Baker compression

This module formalizes `main.tex:1046-1060`.  Baker's quoted lemma remains an
explicit argument.  The construction `q = tr`, the high-degree numerators
`a_j = t v_j`, the nearest-integer choice for the linear numerator, and the
comparison `(N/A) ≤ (N/A)^k` are all proved here.
-/

namespace ImprovedWeylBounds.Conditional

open ImprovedWeylBounds External

/-- Baker compression, converted into the exact all-coefficient conclusion
used by the paper. -/
theorem simultaneousApproximation_of_bakerCompression
    (hBaker : BakerCompression) (k : ℕ) (hk : 3 ≤ k) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ →
      ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ (N : ℕ), N₀ ≤ N →
        ∀ (α : CoefficientVector k) (A : ℝ), 0 < A → A ≤ ‖g α N‖ →
          ∀ pre : PreliminaryApproximation k N α,
            Real.rpow (pre.r : ℝ) (1 - 1 / (k : ℝ)) *
                Real.rpow (N : ℝ) η < A →
              Nonempty (SimultaneousApproximation k N α A η 1) := by
  obtain ⟨η₀, hη₀, hBakerη⟩ := hBaker k hk
  refine ⟨η₀, hη₀, fun η hη hηle ↦ ?_⟩
  obtain ⟨N₀, hN₀, hBakerN⟩ := hBakerη η hη hηle
  refine ⟨N₀, hN₀, fun N hN α A hA hlarge pre hamp ↦ ?_⟩
  obtain ⟨t, ht, _htUpper, hq, hhigh, hlinear⟩ :=
    hBakerN N hN α A pre.r pre.numerator hA pre.r_pos pre.primitive
      pre.accurate hlarge hamp
  let q : ℕ := t * pre.r
  let a : Fin k → ℤ := fun j ↦
    if hj : j.val = 0 then round ((q : ℝ) * α j)
    else (t : ℤ) * pre.numerator j
  have hqpos : 0 < q := Nat.mul_pos ht pre.r_pos
  have hbase : (N : ℝ) / A ≤ ((N : ℝ) / A) ^ k :=
    length_div_amplitude_le_pow hA hlarge (by omega : 1 ≤ k)
  refine ⟨⟨q, hqpos, a, ?_, ?_⟩⟩
  · simpa [q] using hq
  · intro j
    by_cases hj : j.val = 0
    · have hj0 : j = ⟨0, by omega⟩ := Fin.ext hj
      rw [hj0]
      have hpowNonneg : 0 ≤ Real.rpow (N : ℝ) (-1 + η) :=
        Real.rpow_nonneg (Nat.cast_nonneg N) _
      have hscaled :
          ((N : ℝ) / A) * Real.rpow (N : ℝ) (-1 + η) ≤
            (((N : ℝ) / A) ^ k) * Real.rpow (N : ℝ) (-1 + η) :=
        mul_le_mul_of_nonneg_right hbase hpowNonneg
      calc
        |(q : ℝ) * α ⟨0, by omega⟩ - (a ⟨0, by omega⟩ : ℝ)| =
            distToInt ((q : ℝ) * α ⟨0, by omega⟩) := by
              simp [a, distToInt_eq_abs_sub_round]
        _ ≤ ((N : ℝ) / A) * Real.rpow (N : ℝ) (-1 + η) := by
              simpa [q] using hlinear
        _ ≤ (((N : ℝ) / A) ^ k) * Real.rpow (N : ℝ) (-1 + η) := hscaled
        _ = 1 * (((N : ℝ) / A) ^ k) *
            Real.rpow (N : ℝ)
              (-((((⟨0, by omega⟩ : Fin k).val + 1 : ℕ) : ℝ)) + η) := by simp
    · have hjpos : 1 ≤ j.val := by omega
      have hh := hhigh j hjpos
      calc
        |(q : ℝ) * α j - (a j : ℝ)| =
            (t : ℝ) * |(pre.r : ℝ) * α j - (pre.numerator j : ℝ)| := by
              simp only [q, a, hj, ↓reduceDIte, Nat.cast_mul, Int.cast_mul,
                Int.cast_natCast]
              rw [show (t : ℝ) * (pre.r : ℝ) * α j -
                    (t : ℝ) * (pre.numerator j : ℝ) =
                    (t : ℝ) * ((pre.r : ℝ) * α j -
                      (pre.numerator j : ℝ)) by ring]
              rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg t)]
        _ ≤ (((N : ℝ) / A) ^ k) *
            Real.rpow (N : ℝ) (-((j.val + 1 : ℕ) : ℝ) + η) := hh
        _ = 1 * (((N : ℝ) / A) ^ k) *
            Real.rpow (N : ℝ) (-((j.val + 1 : ℕ) : ℝ) + η) := by ring

end ImprovedWeylBounds.Conditional
