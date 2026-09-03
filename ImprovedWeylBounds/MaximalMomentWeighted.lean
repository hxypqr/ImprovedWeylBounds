import ImprovedWeylBounds.MaximalMoment

/-!
# Length-sensitive maximal-moment reduction

The final coarse bound in `MaximalMoment.lean` is convenient for arbitrary
finite block families, but it replaces every block length by the ambient
length before summing.  A dyadic family would then lose a full power of the
ambient length.  This module retains the true length of every block, which is
the form needed for the manuscript's scale-by-scale summation.
-/

open scoped BigOperators
open MeasureTheory

namespace ImprovedWeylBounds

noncomputable local instance : IsProbabilityMeasure unitHaar := by
  dsimp [unitHaar]
  infer_instance

noncomputable local instance (r : ℕ) : IsProbabilityMeasure (torusHaar r) := by
  dsimp [torusHaar]
  infer_instance

/-- Critical-VMVT maximal reduction with the exact weighted sum of block
lengths.  For a concrete dyadic grid, the remaining combinatorial estimate is
`sum_i blockLength(i)^(s+ε) ≪ N^(s+ε)` and the factor `L^(2s-1)` is logarithmic.
-/
theorem maximalTranslatedFixedFibre_criticalVMVT_weighted
    (hVMVT : External.CriticalVMVT)
    (r : ℕ) (hr : 1 ≤ r) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {τ ι : Type*}
        (endpoints : Finset τ) (hendpoints : endpoints.Nonempty)
        (blocks : Finset ι) (pieces : τ → Finset ι)
        (blockStart : ι → ℤ) (blockLength : ι → ℕ)
        (L : ℕ),
        (∀ i ∈ blocks, 1 ≤ blockLength i) →
        ∀ (θ : UnitAddCircle)
          (partialValue : τ → (Fin r → UnitAddCircle) → ℂ),
        (∀ t, pieces t ⊆ blocks) →
        (∀ t, (pieces t).card ≤ L) →
        (∀ t β, partialValue t β =
          ∑ i ∈ pieces t,
            translatedFixedLeadingFibreSum
              r (blockLength i) (blockStart i) θ β) →
        (∫ β, endpoints.sup' hendpoints
            (fun t => ‖partialValue t β‖ ^
              (2 * External.criticalMoment r)) ∂torusHaar r) ≤
          (L : ℝ) ^ (2 * External.criticalMoment r - 1) * C *
            ∑ i ∈ blocks,
              Real.rpow (blockLength i : ℝ)
                ((External.criticalMoment r : ℝ) + ε) := by
  obtain ⟨C, hC, hcritical⟩ := hVMVT r hr ε hε
  refine ⟨C, hC, ?_⟩
  intro τ ι endpoints hendpoints blocks pieces blockStart blockLength L
    hlengthPos θ partialValue hpieces hcard hdecomp
  let p := 2 * External.criticalMoment r
  let blockValue : ι → (Fin r → UnitAddCircle) → ℂ := fun i =>
    translatedFixedLeadingFibreSum
      r (blockLength i) (blockStart i) θ
  have hcritPos : 1 ≤ External.criticalMoment r := by
    have hprod : 2 ≤ r * (r + 1) := by
      calc
        2 = 1 * 2 := by omega
        _ ≤ r * (r + 1) := Nat.mul_le_mul hr (by omega)
    simp only [External.criticalMoment]
    omega
  have hp : 1 ≤ p := by
    dsimp [p]
    omega
  have hblockContinuous (i : ι) : Continuous (blockValue i) := by
    change Continuous (fun β : Fin r → UnitAddCircle =>
      torusPolynomial (ι := Fin (blockLength i))
        (translatedFixedLeadingWeight r (blockStart i) θ)
        (translatedMonomialFrequency r (blockStart i)) β)
    exact continuous_torusPolynomial
      (translatedFixedLeadingWeight r (blockStart i) θ)
      (translatedMonomialFrequency r (blockStart i))
  have hpartialContinuous (t : τ) : Continuous (partialValue t) := by
    have heq : partialValue t = fun β =>
        ∑ i ∈ pieces t, blockValue i β := by
      funext β
      exact hdecomp t β
    rw [heq]
    exact continuous_finsetSum (pieces t) fun i _ => hblockContinuous i
  have hblockIntegrable (i : ι) (hi : i ∈ blocks) :
      Integrable (fun β => ‖blockValue i β‖ ^ p) (torusHaar r) := by
    simpa [blockValue, translatedFixedLeadingFibreSum] using
      (integrable_norm_torusPolynomial_pow
        (translatedFixedLeadingWeight r (blockStart i) θ)
        (translatedMonomialFrequency r (blockStart i)) p)
  have hmaxContinuous : Continuous (fun β =>
      endpoints.sup' hendpoints (fun t => ‖partialValue t β‖ ^ p)) := by
    apply Continuous.finset_sup'_apply hendpoints
    intro t _
    change Continuous ((fun β => ‖partialValue t β‖) ^ p)
    exact (hpartialContinuous t).norm.pow p
  have hmaxIntegrable : Integrable (fun β =>
      endpoints.sup' hendpoints (fun t => ‖partialValue t β‖ ^ p))
      (torusHaar r) := by
    simpa using
      hmaxContinuous.continuousOn.integrableOn_compact isCompact_univ
  have hmoment (i : ι) (hi : i ∈ blocks) :
      (∫ β, ‖blockValue i β‖ ^ p ∂torusHaar r) ≤
        C * Real.rpow (blockLength i : ℝ)
          ((External.criticalMoment r : ℝ) + ε) := by
    calc
      (∫ β, ‖blockValue i β‖ ^ p ∂torusHaar r) ≤
          External.vinogradovMeanValue
            (External.criticalMoment r) r (blockLength i) := by
        simpa only [p, blockValue] using
          (translatedFixedLeadingFibre_moment_le_vinogradovMeanValue
            (External.criticalMoment r) r (blockLength i)
            (blockStart i) θ)
      _ ≤ C * Real.rpow (blockLength i : ℝ)
          ((External.criticalMoment r : ℝ) + ε) :=
        hcritical (blockLength i) (hlengthPos i hi)
  calc
    (∫ β, endpoints.sup' hendpoints
        (fun t => ‖partialValue t β‖ ^
          (2 * External.criticalMoment r)) ∂torusHaar r) ≤
        (L : ℝ) ^ (2 * External.criticalMoment r - 1) *
          ∑ i ∈ blocks, ∫ β, ‖blockValue i β‖ ^ p ∂torusHaar r := by
      simpa only [p] using
        (integral_dyadic_finiteMax_pow_le_sum_intervalMoments
          (torusHaar r) endpoints hendpoints blocks pieces blockValue partialValue
          p L hp hpieces hcard hdecomp hblockIntegrable hmaxIntegrable)
    _ ≤ (L : ℝ) ^ (2 * External.criticalMoment r - 1) *
          ∑ i ∈ blocks,
            (C * Real.rpow (blockLength i : ℝ)
              ((External.criticalMoment r : ℝ) + ε)) := by
      gcongr with i hi
      exact hmoment i hi
    _ = (L : ℝ) ^ (2 * External.criticalMoment r - 1) * C *
          ∑ i ∈ blocks,
            Real.rpow (blockLength i : ℝ)
              ((External.criticalMoment r : ℝ) + ε) := by
      rw [Finset.mul_sum]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

end ImprovedWeylBounds
