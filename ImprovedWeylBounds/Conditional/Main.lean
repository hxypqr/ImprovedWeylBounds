import ImprovedWeylBounds.Conditional.NewInverse
import ImprovedWeylBounds.Conditional.RationalBound
import ImprovedWeylBounds.Conditional.FiniteField

/-!
# End-to-end conditional assembly

These theorems expose the exact remaining hypotheses of the main chain.
The Baker compression and classical inverse theorems are cited external
inputs.  `PreliminaryApproximationPrinciple` is the output still to be
assembled from the manuscript's VMVT, sampling, all-cuts and collision
arguments.
-/

namespace ImprovedWeylBounds.Conditional

open ImprovedWeylBounds External

/-- The rational short-interval theorem follows from the two precisely
stated external inverse inputs and the internal preliminary-approximation
principle. -/
theorem rationalShortIntervalBound_of_external_and_preliminary
    (hBaker : BakerCompression) (hClassical : ClassicalInverse)
    (d : ℕ) (hd : 3 ≤ d) (ε : ℝ) (hε : 0 < ε)
    (hPreliminary : PreliminaryApproximationPrinciple d) :
    RationalShortIntervalBound d ε := by
  have hNew : InversePrinciple d (K d) :=
    inversePrinciple_of_preliminary hBaker d hd hPreliminary
  have hCombined : InversePrinciple d (Delta d) :=
    combinedInverse d hd hNew hClassical
  exact rationalShortIntervalBound_of_inverse d hd ε hε hCombined

/-- The prime-field short-interval theorem with the same explicit trust
boundary. -/
theorem finiteFieldShortIntervalBound_of_external_and_preliminary
    (hBaker : BakerCompression) (hClassical : ClassicalInverse)
    (d : ℕ) (hd : 3 ≤ d) (ε : ℝ) (hε : 0 < ε)
    (hPreliminary : PreliminaryApproximationPrinciple d) :
    FiniteFieldShortIntervalBound d ε := by
  have hNew : InversePrinciple d (K d) :=
    inversePrinciple_of_preliminary hBaker d hd hPreliminary
  have hCombined : InversePrinciple d (Delta d) :=
    combinedInverse d hd hNew hClassical
  exact finiteFieldShortIntervalBound_of_inverse d hd ε hε hCombined

end ImprovedWeylBounds.Conditional
