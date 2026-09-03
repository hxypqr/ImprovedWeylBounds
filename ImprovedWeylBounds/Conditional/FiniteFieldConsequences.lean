import ImprovedWeylBounds.Applications.AdditiveFourier
import ImprovedWeylBounds.Applications.Discrepancy
import ImprovedWeylBounds.Applications.FiniteFieldCharacters
import ImprovedWeylBounds.Conditional.Uniformization

/-!
# Exact finite-field distribution and additive consequences

This module connects the canonical finite-field short sum to the generic
Fourier and Erdős--Turán lemmas.  The customary choices of a truncation
parameter and of a sufficiently small epsilon can be made later; all finite
identities and inequalities are already explicit here.
-/

open scoped BigOperators
open Polynomial

namespace ImprovedWeylBounds
namespace Conditional

open External Applications

noncomputable section

private theorem val_pos_of_ne_zero
    {p : ℕ} [NeZero p] {t : ZMod p} (ht : t ≠ 0) : 0 < t.val := by
  exact Nat.pos_of_ne_zero ((ZMod.val_ne_zero t).2 ht)

private theorem natCast_val_eq {p : ℕ} [NeZero p] (t : ZMod p) :
    (t.val : ZMod p) = t :=
  ZMod.natCast_zmod_val t

/-- The additive Fourier sum of the interval image is exactly the canonical
finite-field short sum of `tP`. -/
theorem intervalFiniteFieldExpSum_eq
    (d p : ℕ) [NeZero p] (P : (ZMod p)[X]) (M : ℤ) (H : ℕ)
    (hdeg : P.natDegree ≤ d) (t : ZMod p) :
    finiteFieldExpSum (intervalPolynomialValue p P M H) t =
      finiteFieldShortSum d p (Polynomial.C t * P) M H := by
  rw [finiteFieldExpSum, finiteFieldShortSum_eq_stdAddChar]
  · rw [sum_Icc_one_eq_sum_fin]
    apply Finset.sum_congr rfl
    intro n _
    congr 1
    simp only [intervalPolynomialValue, Polynomial.eval_mul,
      Polynomial.eval_C]
  · exact (Polynomial.natDegree_C_mul_le t P).trans hdeg

/-- Every nonzero Fourier mode inherits the prime-field short-interval
estimate, with one constant uniform in the prime, polynomial, interval and
mode. -/
theorem uniform_nonzero_frequency_bound
    (d : ℕ) (ε : ℝ) (hFinite : FiniteFieldShortIntervalBoundAll d ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (p H : ℕ) [NeZero p], p.Prime → d < p →
        ∀ (M : ℤ) (P : (ZMod p)[X]),
          1 ≤ H → H ≤ p → P.natDegree = d →
          ∀ t : ZMod p, t ≠ 0 →
            ‖finiteFieldExpSum (intervalPolynomialValue p P M H) t‖ ≤
              C *
                (Real.rpow (p : ℝ) (1 / (d : ℝ)) *
                    Real.rpow (H : ℝ) ε +
                  Real.rpow (H : ℝ)
                    (1 - 1 / (Delta d : ℝ) + ε)) := by
  obtain ⟨C, hC, hbound⟩ := hFinite
  refine ⟨C, hC, ?_⟩
  intro p H _ hp hdp M P hH hHp hdeg t ht
  letI : Fact p.Prime := ⟨hp⟩
  have htdeg : (Polynomial.C t * P).natDegree = d := by
    rw [Polynomial.natDegree_C_mul ht, hdeg]
  rw [intervalFiniteFieldExpSum_eq d p P M H hdeg.le t]
  exact hbound p H hp hdp M (Polynomial.C t * P) hH hHp htdeg

/-- Exact Erdős--Turán consequence at an arbitrary truncation `T<p`.
Choosing `T=floor(H/E)` and absorbing the logarithm is now a purely numerical
specialization. -/
theorem finiteFieldDiscrepancyAtTruncation
    (hErdosTuran : ErdosTuran)
    (d : ℕ) (ε : ℝ) (hFinite : FiniteFieldShortIntervalBoundAll d ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (p H : ℕ) [NeZero p], p.Prime → d < p →
        ∀ (M : ℤ) (P : (ZMod p)[X]),
          1 ≤ H → H ≤ p → P.natDegree = d →
          ∀ T : ℕ, 1 ≤ T → T < p →
            HalfOpenDiscrepancyAtMost
              (normalizedIntervalPolynomialValue p P M H)
              (3 * (H : ℝ) / (T + 1 : ℕ) +
                3 *
                  (C *
                    (Real.rpow (p : ℝ) (1 / (d : ℝ)) *
                        Real.rpow (H : ℝ) ε +
                      Real.rpow (H : ℝ)
                        (1 - 1 / (Delta d : ℝ) + ε))) *
                  (1 + Real.log T)) := by
  obtain ⟨C, hC, hfreq⟩ :=
    uniform_nonzero_frequency_bound d ε hFinite
  refine ⟨C, hC, ?_⟩
  intro p H _ hp hdp M P hH hHp hdeg T hT hTp
  let E : ℝ := C *
    (Real.rpow (p : ℝ) (1 / (d : ℝ)) * Real.rpow (H : ℝ) ε +
      Real.rpow (H : ℝ) (1 - 1 / (Delta d : ℝ) + ε))
  have hE : 0 ≤ E := by
    dsimp [E]
    positivity
  apply discrepancy_of_uniform_exponential_bound_log
    hErdosTuran H T hT (normalizedIntervalPolynomialValue p P M H) E hE
  intro h hh
  have hhmem := Finset.mem_Icc.mp hh
  have hhpos : 0 < h := by omega
  have hhltp : h < p := lt_of_le_of_lt hhmem.2 hTp
  have hhne : (h : ZMod p) ≠ 0 := by
    intro hz
    have hv := congrArg ZMod.val hz
    rw [ZMod.val_cast_of_lt hhltp] at hv
    simp at hv
    omega
  rw [intervalFrequencySum_eq_finiteFieldShortSum d p P M H h hdeg.le]
  rw [← intervalFiniteFieldExpSum_eq d p P M H hdeg.le (h : ZMod p)]
  simpa only [E] using
    hfreq p H hp hdp M P hH hHp hdeg (h : ZMod p) hhne

/-- The additive-basis conclusion under the exact finite inequality comparing
the nonzero-mode error with the zero-mode main term. -/
theorem finiteFieldAdditiveBasis_of_shortSum
    (d : ℕ) (ε : ℝ) (hFinite : FiniteFieldShortIntervalBoundAll d ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (p H : ℕ) [NeZero p], p.Prime → d < p →
        ∀ (M : ℤ) (P : (ZMod p)[X]),
          1 ≤ H → H ≤ p → P.natDegree = d →
          ∀ (s : ℕ) (a : ZMod p),
            (C *
                (Real.rpow (p : ℝ) (1 / (d : ℝ)) *
                    Real.rpow (H : ℝ) ε +
                  Real.rpow (H : ℝ)
                    (1 - 1 / (Delta d : ℝ) + ε))) ^ s <
              (H : ℝ) ^ s / (p : ℝ) →
            0 < representationCount (s := s)
              (intervalPolynomialValue p P M H) a := by
  obtain ⟨C, hC, hfreq⟩ :=
    uniform_nonzero_frequency_bound d ε hFinite
  refine ⟨C, hC, ?_⟩
  intro p H _ hp hdp M P hH hHp hdeg s a hmain
  let B : ℝ := C *
    (Real.rpow (p : ℝ) (1 / (d : ℝ)) * Real.rpow (H : ℝ) ε +
      Real.rpow (H : ℝ) (1 - 1 / (Delta d : ℝ) + ε))
  apply representationCount_pos_of_nonzero_bound p s
    (intervalPolynomialValue p P M H) a B
  · dsimp [B]
    positivity
  · intro t ht
    exact hfreq p H hp hdp M P hH hHp hdeg t ht
  · simpa only [B, Fintype.card_fin] using hmain

end

end Conditional
end ImprovedWeylBounds
