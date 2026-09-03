import ImprovedWeylBounds.Conditional.OrbitBridge
import ImprovedWeylBounds.Conditional.SmallFractionalPartsFull
import ImprovedWeylBounds.Conditional.Uniformization

/-!
# Final conditional assembly at the exact analytic boundary

The theorems in this file no longer mention the intermediate preliminary
denominator.  Its construction from a collision is internal.  The only
arguments are the genuinely external inverse inputs and the still-to-be-
closed internal orbit-collision proposition.
-/

namespace ImprovedWeylBounds.Conditional

open ImprovedWeylBounds External

/-- Baker compression plus the internally derived preliminary denominator
gives the new inverse theorem. -/
theorem inversePrinciple_of_external_and_orbit
    (hBaker : BakerCompression) (k : ℕ) (hk : 3 ≤ k)
    (hOrbit : OrbitCollisionPrinciple k) :
    InversePrinciple k (K k) :=
  inversePrinciple_of_preliminary hBaker k hk
    (preliminaryApproximationPrinciple_of_orbitCollision hk hOrbit)

/-- The manuscript's combined inverse theorem at the exact remaining
analytic boundary. -/
theorem combinedInverse_of_external_and_orbit
    (hBaker : BakerCompression) (hClassical : ClassicalInverse)
    (k : ℕ) (hk : 3 ≤ k) (hOrbit : OrbitCollisionPrinciple k) :
    InversePrinciple k (Delta k) :=
  combinedInverse k hk
    (inversePrinciple_of_external_and_orbit hBaker k hk hOrbit) hClassical

/-- Literal all-positive-length rational short-interval theorem. -/
theorem rationalShortIntervalBoundAll_of_external_and_orbit
    (hBaker : BakerCompression) (hClassical : ClassicalInverse)
    (d : ℕ) (hd : 3 ≤ d) (ε : ℝ) (hε : 0 < ε)
    (hOrbit : OrbitCollisionPrinciple d) :
    RationalShortIntervalBoundAll d ε :=
  rationalShortIntervalBoundAll_of_external_and_preliminary
    hBaker hClassical d hd ε hε
      (preliminaryApproximationPrinciple_of_orbitCollision hd hOrbit)

/-- Literal all-positive-length prime-field short-interval theorem. -/
theorem finiteFieldShortIntervalBoundAll_of_external_and_orbit
    (hBaker : BakerCompression) (hClassical : ClassicalInverse)
    (d : ℕ) (hd : 3 ≤ d) (ε : ℝ) (hε : 0 < ε)
    (hOrbit : OrbitCollisionPrinciple d) :
    FiniteFieldShortIntervalBoundAll d ε :=
  finiteFieldShortIntervalBoundAll_of_external_and_preliminary
    hBaker hClassical d hd ε hε
      (preliminaryApproximationPrinciple_of_orbitCollision hd hOrbit)

/-- Final rational theorem with only the analytic collision proposition and
the two cited inverse inputs exposed: Lemma 5.1 and Lemmas 5.3--5.4 have all
been discharged internally. -/
theorem rationalShortIntervalBoundAll_of_external_and_clusterCollision
    (hBaker : BakerCompression) (hClassical : ClassicalInverse)
    (d : ℕ) (hd : 3 ≤ d) (ε : ℝ) (hε : 0 < ε)
    (hCluster : ClusterCollisionPrinciple d) :
    RationalShortIntervalBoundAll d ε :=
  rationalShortIntervalBoundAll_of_external_and_orbit
    hBaker hClassical d hd ε hε
      (orbitCollisionPrinciple_of_clusterCollision hCluster)

/-- Prime-field counterpart with the same exact boundary. -/
theorem finiteFieldShortIntervalBoundAll_of_external_and_clusterCollision
    (hBaker : BakerCompression) (hClassical : ClassicalInverse)
    (d : ℕ) (hd : 3 ≤ d) (ε : ℝ) (hε : 0 < ε)
    (hCluster : ClusterCollisionPrinciple d) :
    FiniteFieldShortIntervalBoundAll d ε :=
  finiteFieldShortIntervalBoundAll_of_external_and_orbit
    hBaker hClassical d hd ε hε
      (orbitCollisionPrinciple_of_clusterCollision hCluster)

/-- Complete small-fractional-parts consequence with all internal floor and
exponent bookkeeping discharged. -/
theorem smallFractionalParts_of_external_and_clusterCollision
    (hLargeMultiple : LargeMultiple)
    (hBaker : BakerCompression) (hClassical : ClassicalInverse)
    {k : ℕ} (hk : 3 ≤ k) (hCluster : ClusterCollisionPrinciple k)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ alpha : CoefficientVector k,
      ∃ n ∈ Finset.Icc 1 N,
        distToInt (nonconstantPhase alpha n) ≤
          Real.rpow (N : ℝ) (-1 / (Delta k : ℝ) + ε) :=
  smallFractionalParts hLargeMultiple hk
    (combinedInverse_of_external_and_orbit hBaker hClassical k hk
      (orbitCollisionPrinciple_of_clusterCollision hCluster)) hε

/-- Literal all-positive-`N` form of the small-fractional-parts theorem,
with the Vinogradov implicit constant made explicit. -/
theorem smallFractionalPartsAll_of_external_and_clusterCollision
    (hLargeMultiple : LargeMultiple)
    (hBaker : BakerCompression) (hClassical : ClassicalInverse)
    {k : ℕ} (hk : 3 ≤ k) (hCluster : ClusterCollisionPrinciple k)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 1 ≤ N →
      ∀ alpha : CoefficientVector k,
        ∃ n ∈ Finset.Icc 1 N,
          distToInt (nonconstantPhase alpha n) ≤
            C * Real.rpow (N : ℝ) (-1 / (Delta k : ℝ) + ε) :=
  smallFractionalParts_all hLargeMultiple hk
    (combinedInverse_of_external_and_orbit hBaker hClassical k hk
      (orbitCollisionPrinciple_of_clusterCollision hCluster)) hε

end ImprovedWeylBounds.Conditional
