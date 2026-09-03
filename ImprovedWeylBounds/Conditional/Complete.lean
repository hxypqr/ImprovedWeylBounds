import ImprovedWeylBounds.OrbitCollision
import ImprovedWeylBounds.Conditional.Final
import ImprovedWeylBounds.Conditional.FiniteFieldCorollaries

/-!
# End-to-end assembly

This module removes the last manuscript-internal interface from the main
theorems.  Every assumption below is one of the explicitly stated external
results in `External.Statements`; the all-cuts, maximal-moment, sampling,
orbit-collision, triangular extraction, compression bookkeeping, interval
translation, and finite-field lifting steps are all proved in this project.
-/

open scoped BigOperators
open Polynomial

namespace ImprovedWeylBounds
namespace Conditional

open External Applications

/-- Proposition 5.2, exposed at the external VMVT boundary only. -/
theorem clusterCollisionPrinciple_of_external
    (hVMVT : CriticalVMVT) {k : ℕ} (hk : 3 ≤ k) :
    ClusterCollisionPrinciple k :=
  OrbitCollision.clusterCollisionPrinciple_of_criticalVMVT hVMVT hk

/-- Theorem 1.3: the new inverse principle with denominator `K(k)`. -/
theorem inversePrinciple_of_external_inputs
    (hVMVT : CriticalVMVT) (hBaker : BakerCompression)
    {k : ℕ} (hk : 3 ≤ k) :
    InversePrinciple k (K k) :=
  inversePrinciple_of_external_and_orbit hBaker k hk
    (orbitCollisionPrinciple_of_clusterCollision
      (clusterCollisionPrinciple_of_external hVMVT hk))

/-- Corollary 1.4: the combined inverse principle with denominator
`Delta(k) = min (2^(k-1)) (k(k-1))`. -/
theorem combinedInverse_of_external_inputs
    (hVMVT : CriticalVMVT) (hBaker : BakerCompression)
    (hClassical : ClassicalInverse) {k : ℕ} (hk : 3 ≤ k) :
    InversePrinciple k (Delta k) :=
  combinedInverse k hk
    (inversePrinciple_of_external_inputs hVMVT hBaker hk) hClassical

/-- Theorem 1.1, literally for every positive interval length. -/
theorem rationalShortIntervalBoundAll_of_external_inputs
    (hVMVT : CriticalVMVT) (hBaker : BakerCompression)
    (hClassical : ClassicalInverse)
    (d : ℕ) (hd : 3 ≤ d) (ε : ℝ) (hε : 0 < ε) :
    RationalShortIntervalBoundAll d ε :=
  rationalShortIntervalBoundAll_of_external_and_clusterCollision
    hBaker hClassical d hd ε hε
      (clusterCollisionPrinciple_of_external hVMVT hd)

/-- Corollary 1.2, literally for every `1 ≤ H ≤ p`. -/
theorem finiteFieldShortIntervalBoundAll_of_external_inputs
    (hVMVT : CriticalVMVT) (hBaker : BakerCompression)
    (hClassical : ClassicalInverse)
    (d : ℕ) (hd : 3 ≤ d) (ε : ℝ) (hε : 0 < ε) :
    FiniteFieldShortIntervalBoundAll d ε :=
  finiteFieldShortIntervalBoundAll_of_external_and_clusterCollision
    hBaker hClassical d hd ε hε
      (clusterCollisionPrinciple_of_external hVMVT hd)

/-- The prime-field short-sum bound simultaneously for every positive loss;
this is the exact reusable input of Corollaries 7.1--7.3. -/
theorem finiteFieldShortIntervalBoundsAllLosses_of_external_inputs
    (hVMVT : CriticalVMVT) (hBaker : BakerCompression)
    (hClassical : ClassicalInverse) (d : ℕ) (hd : 3 ≤ d) :
    FiniteFieldShortIntervalBoundsAllLosses d := by
  intro ε hε
  exact finiteFieldShortIntervalBoundAll_of_external_inputs
    hVMVT hBaker hClassical d hd ε hε

/-- Theorem 1.4 in its literal all-positive-`N` Vinogradov-bound form. -/
theorem smallFractionalPartsAll_of_external_inputs
    (hVMVT : CriticalVMVT) (hBaker : BakerCompression)
    (hClassical : ClassicalInverse) (hLargeMultiple : LargeMultiple)
    {k : ℕ} (hk : 3 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 1 ≤ N →
      ∀ alpha : CoefficientVector k,
        ∃ n ∈ Finset.Icc 1 N,
          distToInt (nonconstantPhase alpha n) ≤
            C * Real.rpow (N : ℝ) (-1 / (Delta k : ℝ) + ε) :=
  smallFractionalParts_all hLargeMultiple hk
    (combinedInverse_of_external_inputs hVMVT hBaker hClassical hk) hε

/-- Corollary 7.1, assembled directly from the four external analytic inputs
that it uses. -/
theorem finiteFieldDiscrepancyCorollary_of_external_inputs
    (hVMVT : CriticalVMVT) (hBaker : BakerCompression)
    (hClassical : ClassicalInverse) (hErdosTuran : ErdosTuran)
    (d : ℕ) (hd : 3 ≤ d) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (p H : ℕ) [NeZero p], p.Prime → d < p →
        ∀ (M : ℤ) (P : (ZMod p)[X]),
          1 ≤ H → H ≤ p → P.natDegree = d →
          HalfOpenDiscrepancyAtMost
            (normalizedIntervalPolynomialValue p P M H)
            (C * finiteFieldScale d p H * Real.rpow (H : ℝ) ε) :=
  finiteFieldDiscrepancyCorollary hErdosTuran d hd ε hε
    (finiteFieldShortIntervalBoundsAllLosses_of_external_inputs
      hVMVT hBaker hClassical d hd)

/-- Corollary 7.2, assembled directly from the four external analytic inputs
that it uses. -/
theorem finiteFieldGapCorollary_of_external_inputs
    (hVMVT : CriticalVMVT) (hBaker : BakerCompression)
    (hClassical : ClassicalInverse) (hErdosTuran : ErdosTuran)
    (d : ℕ) (hd : 3 ≤ d) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (p H : ℕ) [NeZero p], p.Prime → d < p →
        ∀ (M : ℤ) (P : (ZMod p)[X]),
          1 ≤ H → H ≤ p → P.natDegree = d →
          CyclicResidueGapAtMost p
            (normalizedIntervalPolynomialValue p P M H)
            (C * ((p : ℝ) / H) * finiteFieldScale d p H *
              Real.rpow (H : ℝ) ε) :=
  finiteFieldGapCorollary hErdosTuran d hd ε hε
    (finiteFieldShortIntervalBoundsAllLosses_of_external_inputs
      hVMVT hBaker hClassical d hd)

/-- Corollary 7.3, assembled directly from the three external analytic inputs
that it uses.  Erdős--Turán is not needed for this additive-basis argument. -/
theorem finiteFieldAdditiveBasisCorollary_of_external_inputs
    (hVMVT : CriticalVMVT) (hBaker : BakerCompression)
    (hClassical : ClassicalInverse)
    (d : ℕ) (hd : 3 ≤ d) (s : ℕ) (hs : 1 ≤ s)
    (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∃ H₀ : ℕ, 1 ≤ H₀ ∧
      (∀ H : ℕ, H₀ ≤ H →
        C ^ s * Real.rpow (H : ℝ) (η / 2) <
          Real.rpow (H : ℝ) η) ∧
      ∀ (p H : ℕ) [NeZero p], p.Prime → d < p →
        ∀ (M : ℤ) (P : (ZMod p)[X]),
          H₀ ≤ H → H ≤ p → P.natDegree = d →
          (p : ℝ) * Real.rpow (H : ℝ) η ≤
            ((H : ℝ) / finiteFieldScale d p H) ^ s →
          ∀ a : ZMod p,
            0 < representationCount (s := s)
              (intervalPolynomialValue p P M H) a :=
  finiteFieldAdditiveBasisCorollary d hd s hs η hη
    (finiteFieldShortIntervalBoundsAllLosses_of_external_inputs
      hVMVT hBaker hClassical d hd)

end Conditional
end ImprovedWeylBounds
