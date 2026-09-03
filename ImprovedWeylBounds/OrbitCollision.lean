import ImprovedWeylBounds.AllCuts
import ImprovedWeylBounds.Asymptotics
import ImprovedWeylBounds.Collision
import ImprovedWeylBounds.CollisionApproximation
import ImprovedWeylBounds.DyadicMaximalMoment
import ImprovedWeylBounds.MaximalMomentWeighted
import ImprovedWeylBounds.Sampling
import ImprovedWeylBounds.Conditional.OrbitBridge

/-!
# Translation-orbit collisions

This file assembles the internal part of Proposition 5.2.  It identifies the
translation-orbit centres with points of the coefficient torus, certifies the
Fourier boxes of all variable-length fibre sums, and turns failure of a
collision into anisotropic separation.  The final section combines the
sampling inequality with the concrete maximal critical-moment estimate.
-/

open scoped BigOperators
open MeasureTheory
open Polynomial

namespace ImprovedWeylBounds
namespace OrbitCollision

noncomputable section

noncomputable local instance (r : ℕ) : IsProbabilityMeasure (torusHaar r) := by
  dsimp [torusHaar, unitHaar]
  infer_instance

/-- The canonical degree-`j+1` sampling scale. -/
def canonicalScale {r : ℕ} (N : ℕ) (j : Fin r) : ℕ :=
  N ^ (j.1 + 1)

/-- The first `k-1` coefficients of `P(X+x)`, reduced modulo one. -/
def forwardOrbitPoint {k : ℕ} (alpha : CoefficientVector k) (x : ℤ) :
    Fin (k - 1) → UnitAddCircle :=
  fun j ↦ (translationCentre alpha x j : UnitAddCircle)

/-- The first `k-1` coefficients of `P(x-X)`, reduced modulo one. -/
def backwardOrbitPoint {k : ℕ} (alpha : CoefficientVector k) (x : ℤ) :
    Fin (k - 1) → UnitAddCircle :=
  fun j ↦
    ((reflect (translate x (coefficientPolynomial alpha))).coeff (j.1 + 1) :
      UnitAddCircle)

theorem norm_forwardOrbitPoint_sub {k : ℕ} (alpha : CoefficientVector k)
    (x y : ℤ) (j : Fin (k - 1)) :
    ‖forwardOrbitPoint alpha x j - forwardOrbitPoint alpha y j‖ =
      distToInt (centreDifference alpha x y j) := by
  simp only [forwardOrbitPoint, centreDifference, translationCentre, distToInt,
    QuotientAddGroup.mk_sub]

theorem norm_backwardOrbitPoint_sub {k : ℕ} (alpha : CoefficientVector k)
    (x y : ℤ) (j : Fin (k - 1)) :
    ‖backwardOrbitPoint alpha x j - backwardOrbitPoint alpha y j‖ =
      distToInt (reflectedCentreDifference alpha x y j) := by
  simp only [backwardOrbitPoint, reflectedCentreDifference, distToInt,
    QuotientAddGroup.mk_sub]

/-- An anisotropic non-separation witness is exactly a collision at the
canonical coefficient scales. -/
theorem forward_collision_of_scaled_lt
    {k N : ℕ} (hN : 0 < N) {delta : ℝ}
    (alpha : CoefficientVector k) {x y : ℤ}
    (hsmall : ∀ j : Fin (k - 1),
      (canonicalScale (r := k - 1) N j : ℝ) *
          ‖forwardOrbitPoint alpha x j - forwardOrbitPoint alpha y j‖ < delta) :
    ∀ j : Fin (k - 1),
      distToInt (centreDifference alpha x y j) <
        delta * ((N : ℝ)⁻¹) ^ (j.1 + 1) := by
  intro j
  have hj := hsmall j
  rw [norm_forwardOrbitPoint_sub] at hj
  have hpow : 0 < ((N : ℝ) ^ (j.1 + 1)) := by positivity
  have hdiv : distToInt (centreDifference alpha x y j) <
      delta / ((N : ℝ) ^ (j.1 + 1)) :=
    (lt_div_iff₀ hpow).2 (by simpa [canonicalScale, mul_comm] using hj)
  simpa [div_eq_mul_inv, inv_pow] using hdiv

/-- The reflected analogue of `collision_of_not_separated`. -/
theorem reflected_collision_of_scaled_lt
    {k N : ℕ} (hN : 0 < N) {delta : ℝ}
    (alpha : CoefficientVector k) {x y : ℤ}
    (hsmall : ∀ j : Fin (k - 1),
      (canonicalScale (r := k - 1) N j : ℝ) *
          ‖backwardOrbitPoint alpha x j - backwardOrbitPoint alpha y j‖ < delta) :
    ∀ j : Fin (k - 1),
      distToInt (reflectedCentreDifference alpha x y j) <
        delta * ((N : ℝ)⁻¹) ^ (j.1 + 1) := by
  intro j
  have hj := hsmall j
  rw [norm_backwardOrbitPoint_sub] at hj
  have hpow : 0 < ((N : ℝ) ^ (j.1 + 1)) := by positivity
  have hdiv : distToInt (reflectedCentreDifference alpha x y j) <
      delta / ((N : ℝ) ^ (j.1 + 1)) :=
    (lt_div_iff₀ hpow).2 (by simpa [canonicalScale, mul_comm] using hj)
  simpa [div_eq_mul_inv, inv_pow] using hdiv

/-- If no pair in a finite forward cluster collides at the canonical scales,
then its coefficient-torus points satisfy the sampling separation hypothesis. -/
theorem forward_separated_of_no_collision
    {k N : ℕ} (hN : 0 < N) {delta : ℝ}
    (alpha : CoefficientVector k) (X : Finset (Fin (N + 2)))
    (hno : ∀ x ∈ X, ∀ y ∈ X, x ≠ y →
      ¬ ∀ j : Fin (k - 1),
        distToInt (centreDifference alpha (x.1 : ℤ) (y.1 : ℤ) j) <
          delta * ((N : ℝ)⁻¹) ^ (j.1 + 1)) :
    Sampling.AnisotropicallySeparated delta
      (canonicalScale (r := k - 1) N)
      (fun x : {x // x ∈ X} ↦ forwardOrbitPoint alpha (x.1.1 : ℤ)) := by
  intro x y hxy
  by_contra hnot
  push Not at hnot
  have hclose := forward_collision_of_scaled_lt hN alpha hnot
  apply hno x.1 x.2 y.1 y.2
  · intro hval
    apply hxy
    exact Subtype.ext hval
  · exact hclose

/-- Reflected version of `forward_separated_of_no_collision`. -/
theorem backward_separated_of_no_collision
    {k N : ℕ} (hN : 0 < N) {delta : ℝ}
    (alpha : CoefficientVector k) (X : Finset (Fin (N + 2)))
    (hno : ∀ x ∈ X, ∀ y ∈ X, x ≠ y →
      ¬ ∀ j : Fin (k - 1),
        distToInt
            (reflectedCentreDifference alpha (x.1 : ℤ) (y.1 : ℤ) j) <
          delta * ((N : ℝ)⁻¹) ^ (j.1 + 1)) :
    Sampling.AnisotropicallySeparated delta
      (canonicalScale (r := k - 1) N)
      (fun x : {x // x ∈ X} ↦ backwardOrbitPoint alpha (x.1.1 : ℤ)) := by
  intro x y hxy
  by_contra hnot
  push Not at hnot
  have hclose := reflected_collision_of_scaled_lt hN alpha hnot
  apply hno x.1 x.2 y.1 y.2
  · intro hval
    apply hxy
    exact Subtype.ext hval
  · exact hclose

/-! ## Fourier support of the variable-length fibre sums -/

/-- Every fixed-leading fibre sum of length `R ≤ N` has its spectrum in
the common canonical box `|m_j| ≤ N^(j+1)`. -/
theorem fixedLeadingFibreSum_hasBoundedSpectrum
    {r R N : ℕ} (hRN : R ≤ N) (theta : UnitAddCircle) :
    Sampling.HasBoundedSpectrum (canonicalScale (r := r) N)
      (fixedLeadingFibreSum r R theta) := by
  classical
  refine ⟨{
    Index := Fin R
    indexFintype := inferInstance
    frequency := monomialFrequency r
    coefficient := fixedLeadingWeight r theta
    frequency_le := ?_
    eq_sum := ?_ }⟩
  · intro n j
    simp only [monomialFrequency, Int.natAbs_pow, Int.natAbs_natCast,
      canonicalScale]
    apply Nat.pow_le_pow_left
    exact (Nat.succ_le_iff.mpr n.2).trans hRN
  · intro beta
    rfl

/-- The reflected branch uses the same spectral box; only the fixed leading
circle coefficient changes. -/
theorem reflectedFixedLeadingFibreSum_hasBoundedSpectrum
    {r R N : ℕ} (hRN : R ≤ N) (theta : UnitAddCircle) :
    Sampling.HasBoundedSpectrum (canonicalScale (r := r) N)
      (fixedLeadingFibreSum r R theta) :=
  fixedLeadingFibreSum_hasBoundedSpectrum hRN theta

/-! ## Exact evaluation at a translated coefficient centre -/

lemma fourier_int_coe_eq_e (n : ℤ) (x : ℝ) :
    fourier n (x : UnitAddCircle) = e ((n : ℝ) * x) := by
  rw [fourier_coe_apply]
  simp only [e, Real.fourierChar_apply]
  congr 1
  push_cast
  ring

lemma prod_e_eq_e_sum {r : ℕ} (f : Fin r → ℝ) :
    (∏ j : Fin r, e (f j)) = e (∑ j : Fin r, f j) := by
  classical
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Fin.prod_univ_succ, Fin.sum_univ_succ, ih, e_add]

/-- One summand of the fixed-leading fibre polynomial is the additive
character of the polynomial reconstructed from its positive coefficients. -/
theorem fixedLeadingFibre_summand_eq
    (r R : ℕ) (P : ℝ[X]) (n : Fin R) :
    fixedLeadingWeight r (P.coeff (r + 1) : UnitAddCircle) n *
        torusCharacter (monomialFrequency r n)
          (fun j ↦ (P.coeff (j.1 + 1) : UnitAddCircle)) =
      e (P.coeff (r + 1) * (n.1 + 1 : ℝ) ^ (r + 1) +
        ∑ j : Fin r, P.coeff (j.1 + 1) * (n.1 + 1 : ℝ) ^ (j.1 + 1)) := by
  classical
  simp only [fixedLeadingWeight, torusCharacter, monomialFrequency]
  rw [fourier_int_coe_eq_e]
  simp_rw [fourier_int_coe_eq_e]
  rw [prod_e_eq_e_sum, ← e_add]
  congr 1
  push_cast
  ring

/-- Evaluation minus the constant term is exactly the sum of the positive
coefficient monomials, split into the leading term and the first `r` terms. -/
theorem eval_sub_eval_zero_eq_coefficients
    (r : ℕ) (P : ℝ[X]) (hP : P.natDegree ≤ r + 1) (x : ℝ) :
    P.eval x - P.eval 0 =
      P.coeff (r + 1) * x ^ (r + 1) +
        ∑ j : Fin r, P.coeff (j.1 + 1) * x ^ (j.1 + 1) := by
  have hdeg : P.natDegree < r + 2 := by omega
  rw [P.eval_eq_sum_range' hdeg]
  rw [Finset.sum_range_succ]
  rw [Finset.sum_range_succ']
  rw [← Fin.sum_univ_eq_sum_range]
  rw [← P.coeff_zero_eq_eval_zero]
  simp only [pow_zero, mul_one]
  ring

/-- Exact fibre evaluation for the positive-degree coefficients of any
polynomial of degree at most `r+1`. -/
theorem fixedLeadingFibreSum_coefficients_eq
    (r R : ℕ) (P : ℝ[X]) (hP : P.natDegree ≤ r + 1) :
    fixedLeadingFibreSum r R (P.coeff (r + 1) : UnitAddCircle)
        (fun j ↦ (P.coeff (j.1 + 1) : UnitAddCircle)) =
      ∑ n : Fin R, e (P.eval (n.1 + 1 : ℝ) - P.eval 0) := by
  classical
  unfold fixedLeadingFibreSum torusPolynomial
  apply Finset.sum_congr rfl
  intro n hn
  rw [fixedLeadingFibre_summand_eq]
  congr 1
  rw [eval_sub_eval_zero_eq_coefficients r P hP]

lemma sum_fin_succ_eq_sum_Icc (R : ℕ) (f : ℕ → ℂ) :
    (∑ n : Fin R, f (n.1 + 1)) = ∑ n ∈ Finset.Icc 1 R, f n := by
  classical
  apply Finset.sum_bij (fun n _ ↦ n.1 + 1)
  · intro n hn
    simp only [Finset.mem_Icc]
    omega
  · intro a ha b hb hab
    apply Fin.ext
    omega
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    refine ⟨⟨n - 1, by omega⟩, Finset.mem_univ _, ?_⟩
    · change n - 1 + 1 = n
      omega
  · intro n hn
    rfl

/-- The fixed leading coefficient in the forward orientation. -/
def forwardTheta {k : ℕ} (alpha : CoefficientVector k) : UnitAddCircle :=
  ((coefficientPolynomial alpha).coeff k : UnitAddCircle)

/-- The fixed leading coefficient after reversing a prefix. -/
def backwardTheta {k : ℕ} (alpha : CoefficientVector k) : UnitAddCircle :=
  ((-1 : ℝ) ^ k * (coefficientPolynomial alpha).coeff k : UnitAddCircle)

theorem coeff_k_translate_coefficientPolynomial
    {k : ℕ} (alpha : CoefficientVector k) (x : ℤ) :
    (translate x (coefficientPolynomial alpha)).coeff k =
      (coefficientPolynomial alpha).coeff k := by
  rw [coeff_translate_eq_sum_Icc x (coefficientPolynomial alpha) k k
    (natDegree_coefficientPolynomial_le alpha)]
  simp

theorem coeff_k_reflect_translate_coefficientPolynomial
    {k : ℕ} (alpha : CoefficientVector k) (x : ℤ) :
    (reflect (translate x (coefficientPolynomial alpha))).coeff k =
      (-1 : ℝ) ^ k * (coefficientPolynomial alpha).coeff k := by
  rw [coeff_reflect, coeff_k_translate_coefficientPolynomial]

/-- At a forward translation-orbit centre, the abstract fibre sum is
literally the normalized forward partial sum from Lemma 5.1. -/
theorem fixedLeadingFibreSum_forwardOrbitPoint
    {k : ℕ} (hk : 1 ≤ k) (alpha : CoefficientVector k) (x R : ℕ) :
    fixedLeadingFibreSum (k - 1) R (forwardTheta alpha)
        (forwardOrbitPoint alpha (x : ℤ)) =
      AllCuts.forwardPartial (nonconstantPhase alpha) x R := by
  let P := translate (x : ℤ) (coefficientPolynomial alpha)
  have hP : P.natDegree ≤ (k - 1) + 1 := by
    simpa [P, Nat.sub_add_cancel hk] using
      (natDegree_coefficientPolynomial_le alpha)
  have hgeneric := fixedLeadingFibreSum_coefficients_eq (k - 1) R P hP
  have htop : P.coeff ((k - 1) + 1) =
      (coefficientPolynomial alpha).coeff k := by
    simpa [P, Nat.sub_add_cancel hk] using
      coeff_k_translate_coefficientPolynomial alpha (x : ℤ)
  rw [htop] at hgeneric
  have hgeneric' :
      fixedLeadingFibreSum (k - 1) R (forwardTheta alpha)
          (forwardOrbitPoint alpha (x : ℤ)) =
        ∑ n : Fin R, e (P.eval (n.1 + 1 : ℝ) - P.eval 0) := by
    change fixedLeadingFibreSum (k - 1) R
      ((coefficientPolynomial alpha).coeff k : UnitAddCircle)
      (fun j ↦ ((translate (x : ℤ) (coefficientPolynomial alpha)).coeff
        (j.1 + 1) : UnitAddCircle)) = _
    exact hgeneric
  rw [hgeneric']
  calc
    (∑ n : Fin R, e (P.eval (n.1 + 1 : ℝ) - P.eval 0)) =
        ∑ n ∈ Finset.Icc 1 R, e (P.eval (n : ℝ) - P.eval 0) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (sum_fin_succ_eq_sum_Icc R
          (fun n ↦ e (P.eval (n : ℝ) - P.eval 0)))
    _ = AllCuts.forwardPartial (nonconstantPhase alpha) x R := by
      rw [AllCuts.forwardPartial_eq_translate]
      rfl

/-- At a reflected translation-orbit centre, the abstract fibre sum is
literally the normalized backwards partial sum from Lemma 5.1. -/
theorem fixedLeadingFibreSum_backwardOrbitPoint
    {k : ℕ} (hk : 1 ≤ k) (alpha : CoefficientVector k)
    (x R : ℕ) (hRx : R ≤ x) :
    fixedLeadingFibreSum (k - 1) R (backwardTheta alpha)
        (backwardOrbitPoint alpha (x : ℤ)) =
      AllCuts.backwardPartial (nonconstantPhase alpha) x R := by
  let P := reflect (translate (x : ℤ) (coefficientPolynomial alpha))
  have hP : P.natDegree ≤ (k - 1) + 1 := by
    simpa [P, Nat.sub_add_cancel hk] using
      (natDegree_coefficientPolynomial_le alpha)
  have hgeneric := fixedLeadingFibreSum_coefficients_eq (k - 1) R P hP
  have htop : P.coeff ((k - 1) + 1) =
      (-1 : ℝ) ^ k * (coefficientPolynomial alpha).coeff k := by
    simpa [P, Nat.sub_add_cancel hk] using
      coeff_k_reflect_translate_coefficientPolynomial alpha (x : ℤ)
  rw [htop] at hgeneric
  have hgeneric' :
      fixedLeadingFibreSum (k - 1) R (backwardTheta alpha)
          (backwardOrbitPoint alpha (x : ℤ)) =
        ∑ n : Fin R, e (P.eval (n.1 + 1 : ℝ) - P.eval 0) := by
    change fixedLeadingFibreSum (k - 1) R
      (((-1 : ℝ) ^ k * (coefficientPolynomial alpha).coeff k : ℝ) :
        UnitAddCircle)
      (fun j ↦ ((reflect (translate (x : ℤ)
        (coefficientPolynomial alpha))).coeff (j.1 + 1) : UnitAddCircle)) = _
    exact hgeneric
  rw [hgeneric']
  calc
    (∑ n : Fin R, e (P.eval (n.1 + 1 : ℝ) - P.eval 0)) =
        ∑ n ∈ Finset.Icc 1 R, e (P.eval (n : ℝ) - P.eval 0) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (sum_fin_succ_eq_sum_Icc R
          (fun n ↦ e (P.eval (n : ℝ) - P.eval 0)))
    _ = AllCuts.backwardPartial (nonconstantPhase alpha) x R := by
      rw [AllCuts.backwardPartial_eq_reflect_translate alpha x R hRx]
      rfl

/-! ## Families attached to the two clusters -/

noncomputable def forwardCut
    {k N : ℕ} {alpha : CoefficientVector k}
    (cluster : AllCuts.ForwardCluster k N alpha)
    (x : {x // x ∈ cluster.X}) : Fin (N + 1) :=
  Classical.choose (cluster.partial_sum x.1 x.2)

theorem forwardCut_spec
    {k N : ℕ} {alpha : CoefficientVector k}
    (cluster : AllCuts.ForwardCluster k N alpha)
    (x : {x // x ∈ cluster.X}) :
    forwardCut cluster x ∈
        largeTailCuts (AllCuts.weylSequence alpha N) ‖g alpha N‖ ∧
      AllCuts.forwardCentre (forwardCut cluster x) = x.1 ∧
      1 ≤ N - (forwardCut cluster x).1 ∧
      ‖AllCuts.forwardPartial (nonconstantPhase alpha)
          (forwardCut cluster x).1 (N - (forwardCut cluster x).1)‖ ≥
        ‖g alpha N‖ / 2 :=
  Classical.choose_spec (cluster.partial_sum x.1 x.2)

def forwardLength
    {k N : ℕ} {alpha : CoefficientVector k}
    (cluster : AllCuts.ForwardCluster k N alpha)
    (x : {x // x ∈ cluster.X}) : ℕ :=
  N - (forwardCut cluster x).1

theorem forwardLength_pos
    {k N : ℕ} {alpha : CoefficientVector k}
    (cluster : AllCuts.ForwardCluster k N alpha)
    (x : {x // x ∈ cluster.X}) : 1 ≤ forwardLength cluster x :=
  (forwardCut_spec cluster x).2.2.1

theorem forwardLength_le
    {k N : ℕ} {alpha : CoefficientVector k}
    (cluster : AllCuts.ForwardCluster k N alpha)
    (x : {x // x ∈ cluster.X}) : forwardLength cluster x ≤ N := by
  exact Nat.sub_le _ _

noncomputable def forwardFamily
    {k N : ℕ} {alpha : CoefficientVector k}
    (cluster : AllCuts.ForwardCluster k N alpha)
    (x : {x // x ∈ cluster.X}) :
    (Fin (k - 1) → UnitAddCircle) → ℂ :=
  fixedLeadingFibreSum (k - 1) (forwardLength cluster x) (forwardTheta alpha)

theorem norm_forwardFamily_at_centre
    {k N : ℕ} (hk : 1 ≤ k) {alpha : CoefficientVector k}
    (cluster : AllCuts.ForwardCluster k N alpha)
    (x : {x // x ∈ cluster.X}) :
    ‖forwardFamily cluster x (forwardOrbitPoint alpha (x.1.1 : ℤ))‖ ≥
      ‖g alpha N‖ / 2 := by
  have hs := forwardCut_spec cluster x
  have hval : (forwardCut cluster x).1 = x.1.1 :=
    congrArg Fin.val hs.2.1
  rw [forwardFamily, fixedLeadingFibreSum_forwardOrbitPoint hk]
  simpa [forwardLength, hval] using hs.2.2.2

noncomputable def backwardCut
    {k N : ℕ} {alpha : CoefficientVector k}
    (cluster : AllCuts.BackwardCluster k N alpha)
    (x : {x // x ∈ cluster.X}) : Fin (N + 1) :=
  Classical.choose (cluster.partial_sum x.1 x.2)

theorem backwardCut_spec
    {k N : ℕ} {alpha : CoefficientVector k}
    (cluster : AllCuts.BackwardCluster k N alpha)
    (x : {x // x ∈ cluster.X}) :
    backwardCut cluster x ∈
        largePrefixCuts (AllCuts.weylSequence alpha N) ‖g alpha N‖ ∧
      AllCuts.backwardCentre (backwardCut cluster x) = x.1 ∧
      1 ≤ (backwardCut cluster x).1 ∧
      ‖AllCuts.backwardPartial (nonconstantPhase alpha)
          ((backwardCut cluster x).1 + 1) (backwardCut cluster x).1‖ ≥
        ‖g alpha N‖ / 2 :=
  Classical.choose_spec (cluster.partial_sum x.1 x.2)

def backwardLength
    {k N : ℕ} {alpha : CoefficientVector k}
    (cluster : AllCuts.BackwardCluster k N alpha)
    (x : {x // x ∈ cluster.X}) : ℕ :=
  (backwardCut cluster x).1

theorem backwardLength_pos
    {k N : ℕ} {alpha : CoefficientVector k}
    (cluster : AllCuts.BackwardCluster k N alpha)
    (x : {x // x ∈ cluster.X}) : 1 ≤ backwardLength cluster x :=
  (backwardCut_spec cluster x).2.2.1

theorem backwardLength_le
    {k N : ℕ} {alpha : CoefficientVector k}
    (cluster : AllCuts.BackwardCluster k N alpha)
    (x : {x // x ∈ cluster.X}) : backwardLength cluster x ≤ N :=
  Nat.le_of_lt_succ (backwardCut cluster x).2

noncomputable def backwardFamily
    {k N : ℕ} {alpha : CoefficientVector k}
    (cluster : AllCuts.BackwardCluster k N alpha)
    (x : {x // x ∈ cluster.X}) :
    (Fin (k - 1) → UnitAddCircle) → ℂ :=
  fixedLeadingFibreSum (k - 1) (backwardLength cluster x) (backwardTheta alpha)

theorem norm_backwardFamily_at_centre
    {k N : ℕ} (hk : 1 ≤ k) {alpha : CoefficientVector k}
    (cluster : AllCuts.BackwardCluster k N alpha)
    (x : {x // x ∈ cluster.X}) :
    ‖backwardFamily cluster x (backwardOrbitPoint alpha (x.1.1 : ℤ))‖ ≥
      ‖g alpha N‖ / 2 := by
  have hs := backwardCut_spec cluster x
  have hval : (backwardCut cluster x).1 + 1 = x.1.1 :=
    congrArg Fin.val hs.2.1
  have hle : backwardLength cluster x ≤ x.1.1 := by
    simp only [backwardLength, ← hval]
    omega
  rw [backwardFamily,
    fixedLeadingFibreSum_backwardOrbitPoint hk alpha x.1.1
      (backwardLength cluster x) hle]
  simpa [backwardLength, hval] using hs.2.2.2

theorem forwardFamily_hasBoundedSpectrum
    {k N : ℕ} {alpha : CoefficientVector k}
    (cluster : AllCuts.ForwardCluster k N alpha)
    (x : {x // x ∈ cluster.X}) :
    Sampling.HasBoundedSpectrum (canonicalScale (r := k - 1) N)
      (forwardFamily cluster x) :=
  fixedLeadingFibreSum_hasBoundedSpectrum (forwardLength_le cluster x)
    (forwardTheta alpha)

theorem backwardFamily_hasBoundedSpectrum
    {k N : ℕ} {alpha : CoefficientVector k}
    (cluster : AllCuts.BackwardCluster k N alpha)
    (x : {x // x ∈ cluster.X}) :
    Sampling.HasBoundedSpectrum (canonicalScale (r := k - 1) N)
      (backwardFamily cluster x) :=
  fixedLeadingFibreSum_hasBoundedSpectrum (backwardLength_le cluster x)
    (backwardTheta alpha)

theorem forwardCluster_nonempty
    {k N : ℕ} {alpha : CoefficientVector k}
    (hsize : 8 * k.factorial ≤ N + 1)
    (cluster : AllCuts.ForwardCluster k N alpha) : cluster.X.Nonempty := by
  have hq : 1 ≤ (N + 1) / (8 * k.factorial) := by
    apply (Nat.le_div_iff_mul_le (by positivity : 0 < 8 * k.factorial)).2
    simpa using hsize
  apply Finset.card_pos.mp
  exact lt_of_lt_of_le Nat.zero_lt_one (hq.trans cluster.card_lower)

theorem backwardCluster_nonempty
    {k N : ℕ} {alpha : CoefficientVector k}
    (hsize : 8 * k.factorial ≤ N + 1)
    (cluster : AllCuts.BackwardCluster k N alpha) : cluster.X.Nonempty := by
  have hq : 1 ≤ (N + 1) / (8 * k.factorial) := by
    apply (Nat.le_div_iff_mul_le (by positivity : 0 < 8 * k.factorial)).2
    simpa using hsize
  apply Finset.card_pos.mp
  exact lt_of_lt_of_le Nat.zero_lt_one (hq.trans cluster.card_lower)

/-! ## Domination by the common maximal fibre function -/

/-- The exact finite maximum used by the concrete dyadic theorem. -/
noncomputable def fibreMaxPower
    (k N : ℕ) (theta : UnitAddCircle)
    (beta : Fin (k - 1) → UnitAddCircle) : ℝ :=
  (Finset.univ : Finset (Fin (N + 1))).sup' (by simp)
    (fun L ↦ ‖fixedLeadingFibreSum (k - 1) L.1 theta beta‖ ^ K k)

theorem continuous_fibreMaxPower
    (k N : ℕ) (theta : UnitAddCircle) :
    Continuous (fibreMaxPower k N theta) := by
  unfold fibreMaxPower
  apply Continuous.finset_sup'_apply (by simp)
  intro L hL
  exact (continuous_torusPolynomial
    (fixedLeadingWeight (k - 1) theta)
    (monomialFrequency (k - 1))).norm.pow (K k)

theorem forward_familyMaxPower_le_fibreMaxPower
    {k N : ℕ} {alpha : CoefficientVector k}
    (cluster : AllCuts.ForwardCluster k N alpha)
    (hX : cluster.X.Nonempty)
    (beta : Fin (k - 1) → UnitAddCircle) :
    letI : Nonempty {x // x ∈ cluster.X} :=
      ⟨⟨hX.choose, hX.choose_spec⟩⟩
    Sampling.familyMaxPower (K k) (forwardFamily cluster) beta ≤
      fibreMaxPower k N (forwardTheta alpha) beta := by
  letI : Nonempty {x // x ∈ cluster.X} :=
    ⟨⟨hX.choose, hX.choose_spec⟩⟩
  unfold Sampling.familyMaxPower fibreMaxPower
  apply Finset.sup'_le Finset.univ_nonempty
  intro x hx
  let L : Fin (N + 1) :=
    ⟨forwardLength cluster x, Nat.lt_succ_of_le (forwardLength_le cluster x)⟩
  exact Finset.le_sup' (fun L : Fin (N + 1) ↦
    ‖fixedLeadingFibreSum (k - 1) L.1 (forwardTheta alpha) beta‖ ^ K k)
    (Finset.mem_univ L)

theorem backward_familyMaxPower_le_fibreMaxPower
    {k N : ℕ} {alpha : CoefficientVector k}
    (cluster : AllCuts.BackwardCluster k N alpha)
    (hX : cluster.X.Nonempty)
    (beta : Fin (k - 1) → UnitAddCircle) :
    letI : Nonempty {x // x ∈ cluster.X} :=
      ⟨⟨hX.choose, hX.choose_spec⟩⟩
    Sampling.familyMaxPower (K k) (backwardFamily cluster) beta ≤
      fibreMaxPower k N (backwardTheta alpha) beta := by
  letI : Nonempty {x // x ∈ cluster.X} :=
    ⟨⟨hX.choose, hX.choose_spec⟩⟩
  unfold Sampling.familyMaxPower fibreMaxPower
  apply Finset.sup'_le Finset.univ_nonempty
  intro x hx
  let L : Fin (N + 1) :=
    ⟨backwardLength cluster x, Nat.lt_succ_of_le (backwardLength_le cluster x)⟩
  exact Finset.le_sup' (fun L : Fin (N + 1) ↦
    ‖fixedLeadingFibreSum (k - 1) L.1 (backwardTheta alpha) beta‖ ^ K k)
    (Finset.mem_univ L)

theorem samplingTorusHaar_eq_torusHaar (r : ℕ) :
    Sampling.torusHaarMeasure r = torusHaar r := by
  rfl

theorem integral_forward_familyMaxPower_le
    {k N : ℕ} {alpha : CoefficientVector k}
    (cluster : AllCuts.ForwardCluster k N alpha)
    (hX : cluster.X.Nonempty) :
    letI : Nonempty {x // x ∈ cluster.X} :=
      ⟨⟨hX.choose, hX.choose_spec⟩⟩
    (∫ beta, Sampling.familyMaxPower (K k) (forwardFamily cluster) beta
        ∂Sampling.torusHaarMeasure (k - 1)) ≤
      ∫ beta, fibreMaxPower k N (forwardTheta alpha) beta
        ∂torusHaar (k - 1) := by
  letI : Nonempty {x // x ∈ cluster.X} :=
    ⟨⟨hX.choose, hX.choose_spec⟩⟩
  rw [samplingTorusHaar_eq_torusHaar]
  apply integral_mono
  · exact (Sampling.continuous_familyMaxPower (K k) (forwardFamily cluster)
      (forwardFamily_hasBoundedSpectrum cluster)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact (continuous_fibreMaxPower k N (forwardTheta alpha)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact forward_familyMaxPower_le_fibreMaxPower cluster hX

theorem integral_backward_familyMaxPower_le
    {k N : ℕ} {alpha : CoefficientVector k}
    (cluster : AllCuts.BackwardCluster k N alpha)
    (hX : cluster.X.Nonempty) :
    letI : Nonempty {x // x ∈ cluster.X} :=
      ⟨⟨hX.choose, hX.choose_spec⟩⟩
    (∫ beta, Sampling.familyMaxPower (K k) (backwardFamily cluster) beta
        ∂Sampling.torusHaarMeasure (k - 1)) ≤
      ∫ beta, fibreMaxPower k N (backwardTheta alpha) beta
        ∂torusHaar (k - 1) := by
  letI : Nonempty {x // x ∈ cluster.X} :=
    ⟨⟨hX.choose, hX.choose_spec⟩⟩
  rw [samplingTorusHaar_eq_torusHaar]
  apply integral_mono
  · exact (Sampling.continuous_familyMaxPower (K k) (backwardFamily cluster)
      (backwardFamily_hasBoundedSpectrum cluster)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact (continuous_fibreMaxPower k N (backwardTheta alpha)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact backward_familyMaxPower_le_fibreMaxPower cluster hX

/-! ## Sampling contradiction at a fixed `N` -/

noncomputable def criticalSamplingPrefactor (k : ℕ) (delta : ℝ) : ℝ :=
  (130 * (Sampling.criticalHalfExponent k : ℝ) *
    Sampling.cellComparisonFactor delta) ^ (k - 1)

lemma sum_range_succ_eq_choose_two (r : ℕ) :
    ∑ i ∈ Finset.range r, (i + 1) = (r + 1).choose 2 := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Finset.sum_range_succ, ih]
      calc
        (r + 1).choose 2 + (r + 1) =
            (r + 1) + (r + 1).choose 2 := Nat.add_comm _ _
        _ = (r + 2).choose 2 := by
          symm
          simpa only [Nat.choose_one_right] using
            (Nat.choose_succ_succ' (r + 1) 1)

theorem sum_fin_succ_eq_criticalMoment (r : ℕ) :
    (∑ j : Fin r, (j.1 + 1)) = External.criticalMoment r := by
  calc
    (∑ j : Fin r, (j.1 + 1)) =
        ∑ i ∈ Finset.range r, (i + 1) :=
      Fin.sum_univ_eq_sum_range (fun i ↦ i + 1) r
    _ = (r + 1).choose 2 := sum_range_succ_eq_choose_two r
    _ = External.criticalMoment r := by
      simp only [External.criticalMoment, Nat.choose_two_right]
      simp [Nat.mul_comm]

theorem criticalMoment_pred_eq_criticalHalfExponent
    {k : ℕ} (hk : 1 ≤ k) :
    External.criticalMoment (k - 1) = Sampling.criticalHalfExponent k := by
  simp only [External.criticalMoment, Sampling.criticalHalfExponent, K]
  rw [Nat.sub_add_cancel hk]
  congr 1
  ring

theorem two_mul_criticalMoment_pred
    {k : ℕ} (hk : 2 ≤ k) :
    2 * External.criticalMoment (k - 1) = K k := by
  rw [criticalMoment_pred_eq_criticalHalfExponent (by omega : 1 ≤ k)]
  exact Sampling.two_mul_criticalHalfExponent k

theorem prod_canonicalScale_cast (r N : ℕ) :
    (∏ j : Fin r, (canonicalScale N j : ℝ)) =
      (N : ℝ) ^ External.criticalMoment r := by
  calc
    (∏ j : Fin r, (canonicalScale N j : ℝ)) =
        ∏ j : Fin r, (N : ℝ) ^ (j.1 + 1) := by
      apply Finset.prod_congr rfl
      intro j hj
      simp only [canonicalScale, Nat.cast_pow]
    _ = (N : ℝ) ^ (∑ j : Fin r, (j.1 + 1)) := by
      simpa only using
        (Finset.prod_pow_eq_pow_sum (Finset.univ : Finset (Fin r))
          (fun j : Fin r ↦ j.1 + 1) (N : ℝ))
    _ = (N : ℝ) ^ External.criticalMoment r := by
      rw [sum_fin_succ_eq_criticalMoment]

/-- The concrete dyadic theorem in the exact exponent notation used by the
collision argument. -/
theorem fibreMaxPower_criticalVMVT_eventual
    (hVMVT : External.CriticalVMVT)
    (k : ℕ) (hk : 3 ≤ k) (eta : ℝ) (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
      ∀ (N : ℕ), N₀ ≤ N → ∀ theta : UnitAddCircle,
        (∫ beta, fibreMaxPower k N theta beta ∂torusHaar (k - 1)) ≤
          C * Real.rpow (N : ℝ)
            ((Sampling.criticalHalfExponent k : ℝ) + eta) := by
  obtain ⟨C, hC, N₀, hN₀, hbound⟩ :=
    maximalFixedLeadingFibre_criticalVMVT_eventual hVMVT (k - 1)
      (by omega : 1 ≤ k - 1) eta heta
  refine ⟨C, hC, N₀, hN₀, ?_⟩
  intro N hN theta
  have hb := hbound N hN theta
  simpa only [fibreMaxPower,
    criticalMoment_pred_eq_criticalHalfExponent (by omega : 1 ≤ k),
    Sampling.two_mul_criticalHalfExponent] using hb

theorem sampling_expression_le_rpow
    {k N : ℕ} (hk : 2 ≤ k) (hN : 0 < N)
    {delta eta C I : ℝ}
    (hI : I ≤ C * Real.rpow (N : ℝ)
      ((Sampling.criticalHalfExponent k : ℝ) + eta)) :
    (criticalSamplingPrefactor k delta *
        ∏ j : Fin (k - 1), (canonicalScale N j : ℝ)) * I ≤
      criticalSamplingPrefactor k delta * C *
        Real.rpow (N : ℝ) ((K k : ℝ) + eta) := by
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hS : 0 ≤ criticalSamplingPrefactor k delta := by
    exact pow_nonneg (by
      exact mul_nonneg
        (mul_nonneg (by norm_num) (by positivity))
        (Sampling.cellComparisonFactor_nonneg delta)) _
  have hscale :
      (∏ j : Fin (k - 1), (canonicalScale N j : ℝ)) =
        Real.rpow (N : ℝ) (Sampling.criticalHalfExponent k : ℝ) := by
    rw [prod_canonicalScale_cast]
    rw [criticalMoment_pred_eq_criticalHalfExponent (by omega : 1 ≤ k)]
    exact (Real.rpow_natCast (N : ℝ)
      (Sampling.criticalHalfExponent k)).symm
  have htwoR :
      (Sampling.criticalHalfExponent k : ℝ) +
          (Sampling.criticalHalfExponent k : ℝ) = (K k : ℝ) := by
    have htwoMul :
        (2 : ℝ) * (Sampling.criticalHalfExponent k : ℝ) = (K k : ℝ) := by
      exact_mod_cast Sampling.two_mul_criticalHalfExponent k
    linarith
  rw [hscale]
  calc
    (criticalSamplingPrefactor k delta *
        Real.rpow (N : ℝ) (Sampling.criticalHalfExponent k : ℝ)) * I ≤
      (criticalSamplingPrefactor k delta *
        Real.rpow (N : ℝ) (Sampling.criticalHalfExponent k : ℝ)) *
          (C * Real.rpow (N : ℝ)
            ((Sampling.criticalHalfExponent k : ℝ) + eta)) := by
      apply mul_le_mul_of_nonneg_left hI
      exact mul_nonneg hS (Real.rpow_nonneg hNreal.le _)
    _ = criticalSamplingPrefactor k delta * C *
        (Real.rpow (N : ℝ) (Sampling.criticalHalfExponent k : ℝ) *
          Real.rpow (N : ℝ)
            ((Sampling.criticalHalfExponent k : ℝ) + eta)) := by ring
    _ = criticalSamplingPrefactor k delta * C *
        Real.rpow (N : ℝ)
          ((Sampling.criticalHalfExponent k : ℝ) +
            ((Sampling.criticalHalfExponent k : ℝ) + eta)) := by
      congr 1
      exact (Real.rpow_add hNreal _ _).symm
    _ = criticalSamplingPrefactor k delta * C *
        Real.rpow (N : ℝ) ((K k : ℝ) + eta) := by
      congr 2
      linarith

/-- The floor in the cluster cardinality loses at most the harmless factor
`16 * k!` once the quotient is nonzero. -/
theorem le_sixteen_factorial_mul_of_div_le
    {k N card : ℕ}
    (hsize : 8 * k.factorial ≤ N + 1)
    (hcard : (N + 1) / (8 * k.factorial) ≤ card) :
    N ≤ 16 * k.factorial * card := by
  let D := 8 * k.factorial
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hq : 0 < (N + 1) / D := Nat.div_pos hsize hD
  have hlt : N + 1 < D * ((N + 1) / D + 1) :=
    Nat.lt_mul_div_succ (N + 1) hD
  calc
    N ≤ N + 1 := Nat.le_succ N
    _ ≤ D * ((N + 1) / D + 1) := hlt.le
    _ ≤ D * (2 * ((N + 1) / D)) := by
      apply Nat.mul_le_mul_left
      omega
    _ = 16 * k.factorial * ((N + 1) / (8 * k.factorial)) := by
      dsimp [D]
      ring
    _ ≤ 16 * k.factorial * card :=
      Nat.mul_le_mul_left (16 * k.factorial) hcard

/-- The explicit numerical comparison which converts the maximal-moment
bound and a large Weyl sum into the strict sampling inequality. -/
theorem sampling_strict_of_power_bounds
    {k N card : ℕ} (hk : 2 ≤ k) (hN : 0 < N)
    {delta eta thresholdMargin C I G : ℝ}
    (hcard : N ≤ 16 * k.factorial * card)
    (hI : I ≤ C * Real.rpow (N : ℝ)
      ((Sampling.criticalHalfExponent k : ℝ) + eta))
    (hlarge : Real.rpow (N : ℝ)
      (1 - 1 / (K k : ℝ) + thresholdMargin) < G)
    (hpower :
      (((16 * k.factorial : ℕ) : ℝ) * (2 : ℝ) ^ K k *
          (criticalSamplingPrefactor k delta * C)) *
        Real.rpow (N : ℝ) ((K k : ℝ) + eta) <
      Real.rpow (N : ℝ)
        ((K k : ℝ) + (K k : ℝ) * thresholdMargin)) :
    (criticalSamplingPrefactor k delta *
        ∏ j : Fin (k - 1), (canonicalScale N j : ℝ)) * I <
      (card : ℝ) * (G / 2) ^ K k := by
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hKnat : 0 < K k := by
    simp only [K]
    apply Nat.mul_pos
    · omega
    · omega
  have hKreal : 0 < (K k : ℝ) := by exact_mod_cast hKnat
  have hbase : 0 < Real.rpow (N : ℝ)
      (1 - 1 / (K k : ℝ) + thresholdMargin) :=
    Real.rpow_pos_of_pos hNreal _
  have hG : 0 < G := hbase.trans hlarge
  have hlargePow :
      (Real.rpow (N : ℝ)
        (1 - 1 / (K k : ℝ) + thresholdMargin)) ^ K k < G ^ K k :=
    pow_lt_pow_left₀ hlarge hbase.le (Nat.ne_of_gt hKnat)
  have hexponent :
      (1 - 1 / (K k : ℝ) + thresholdMargin) * (K k : ℝ) =
        (K k : ℝ) - 1 + (K k : ℝ) * thresholdMargin := by
    field_simp [hKreal.ne']
  have hlargeRpow :
      Real.rpow (N : ℝ)
          ((K k : ℝ) - 1 + (K k : ℝ) * thresholdMargin) <
        G ^ K k := by
    calc
      Real.rpow (N : ℝ)
          ((K k : ℝ) - 1 + (K k : ℝ) * thresholdMargin) =
          Real.rpow (N : ℝ)
            ((1 - 1 / (K k : ℝ) + thresholdMargin) * (K k : ℝ)) := by
        rw [hexponent]
      _ = (Real.rpow (N : ℝ)
          (1 - 1 / (K k : ℝ) + thresholdMargin)) ^ K k :=
        Real.rpow_mul_natCast hNreal.le _ _
      _ < G ^ K k := hlargePow
  have hcardR :
      (N : ℝ) ≤ (((16 * k.factorial : ℕ) : ℝ) * (card : ℝ)) := by
    exact_mod_cast hcard
  have htarget :
      Real.rpow (N : ℝ)
          ((K k : ℝ) + (K k : ℝ) * thresholdMargin) <
        (((16 * k.factorial : ℕ) : ℝ) * (card : ℝ)) * G ^ K k := by
    calc
      Real.rpow (N : ℝ)
          ((K k : ℝ) + (K k : ℝ) * thresholdMargin) =
          Real.rpow (N : ℝ)
            (1 + ((K k : ℝ) - 1 + (K k : ℝ) * thresholdMargin)) := by
        congr 1
        ring
      _ = Real.rpow (N : ℝ) 1 *
          Real.rpow (N : ℝ)
            ((K k : ℝ) - 1 + (K k : ℝ) * thresholdMargin) :=
        Real.rpow_add hNreal _ _
      _ = (N : ℝ) * Real.rpow (N : ℝ)
            ((K k : ℝ) - 1 + (K k : ℝ) * thresholdMargin) := by
        have hone : Real.rpow (N : ℝ) 1 = (N : ℝ) := by simp
        rw [hone]
      _ < (N : ℝ) * G ^ K k :=
        mul_lt_mul_of_pos_left hlargeRpow hNreal
      _ ≤ (((16 * k.factorial : ℕ) : ℝ) * (card : ℝ)) * G ^ K k :=
        mul_le_mul_of_nonneg_right hcardR (pow_nonneg hG.le _)
  have hupper := sampling_expression_le_rpow hk hN
    (delta := delta) (eta := eta) (C := C) (I := I) hI
  let E : ℝ := ((16 * k.factorial : ℕ) : ℝ) * (2 : ℝ) ^ K k
  have hE : 0 < E := by
    dsimp [E]
    positivity
  have hscaledUpper :
      E * ((criticalSamplingPrefactor k delta *
          ∏ j : Fin (k - 1), (canonicalScale N j : ℝ)) * I) <
        Real.rpow (N : ℝ)
          ((K k : ℝ) + (K k : ℝ) * thresholdMargin) := by
    calc
      E * ((criticalSamplingPrefactor k delta *
          ∏ j : Fin (k - 1), (canonicalScale N j : ℝ)) * I) ≤
          E * (criticalSamplingPrefactor k delta * C *
            Real.rpow (N : ℝ) ((K k : ℝ) + eta)) :=
        mul_le_mul_of_nonneg_left hupper hE.le
      _ = (E * (criticalSamplingPrefactor k delta * C)) *
          Real.rpow (N : ℝ) ((K k : ℝ) + eta) := by ring
      _ < Real.rpow (N : ℝ)
          ((K k : ℝ) + (K k : ℝ) * thresholdMargin) := by
        simpa only [E] using hpower
  have hscaledLower :
      E * ((card : ℝ) * (G / 2) ^ K k) =
        (((16 * k.factorial : ℕ) : ℝ) * (card : ℝ)) * G ^ K k := by
    dsimp [E]
    rw [div_pow]
    field_simp
  apply lt_of_mul_lt_mul_left _ hE.le
  calc
    E * ((criticalSamplingPrefactor k delta *
        ∏ j : Fin (k - 1), (canonicalScale N j : ℝ)) * I) <
        Real.rpow (N : ℝ)
          ((K k : ℝ) + (K k : ℝ) * thresholdMargin) := hscaledUpper
    _ < (((16 * k.factorial : ℕ) : ℝ) * (card : ℝ)) * G ^ K k := htarget
    _ = E * ((card : ℝ) * (G / 2) ^ K k) := hscaledLower.symm

theorem exists_forward_collision_of_sampling_strict
    {k N : ℕ} (hk : 2 ≤ k) (hN : 0 < N)
    {delta : ℝ} (hdelta : 0 < delta)
    {alpha : CoefficientVector k}
    (cluster : AllCuts.ForwardCluster k N alpha)
    (hX : cluster.X.Nonempty)
    (hstrict :
      (criticalSamplingPrefactor k delta *
          ∏ j : Fin (k - 1), (canonicalScale N j : ℝ)) *
        (∫ beta, fibreMaxPower k N (forwardTheta alpha) beta
          ∂torusHaar (k - 1)) <
      (cluster.X.card : ℝ) * (‖g alpha N‖ / 2) ^ K k) :
    ∃ x ∈ cluster.X, ∃ y ∈ cluster.X, x ≠ y ∧
      ∀ j : Fin (k - 1),
        distToInt (centreDifference alpha (x.1 : ℤ) (y.1 : ℤ) j) <
          delta * ((N : ℝ)⁻¹) ^ (j.1 + 1) := by
  classical
  letI : Nonempty {x // x ∈ cluster.X} :=
    ⟨⟨hX.choose, hX.choose_spec⟩⟩
  let point : {x // x ∈ cluster.X} → Fin (k - 1) → UnitAddCircle :=
    fun x ↦ forwardOrbitPoint alpha (x.1.1 : ℤ)
  let separated : {x // x ∈ cluster.X} → {x // x ∈ cluster.X} → Prop :=
    fun x y ↦ ∃ j : Fin (k - 1),
      delta ≤ (canonicalScale N j : ℝ) * ‖point x j - point y j‖
  let value : {x // x ∈ cluster.X} → ℝ :=
    fun x ↦ ‖forwardFamily cluster x (point x)‖
  have hupper :
      ((Finset.univ : Finset {x // x ∈ cluster.X}) :
          Set {x // x ∈ cluster.X}).Pairwise separated →
        ∑ x : {x // x ∈ cluster.X}, value x ^ K k ≤
          (criticalSamplingPrefactor k delta *
              ∏ j : Fin (k - 1), (canonicalScale N j : ℝ)) *
            (∫ beta, fibreMaxPower k N (forwardTheta alpha) beta
              ∂torusHaar (k - 1)) := by
    intro hpair
    have hsep : Sampling.AnisotropicallySeparated delta
        (canonicalScale (r := k - 1) N) point := by
      intro x y hxy
      exact hpair (Finset.mem_univ x) (Finset.mem_univ y) hxy
    have hsamp := Sampling.anisotropicSampling_criticalExponent hdelta k hk
      (canonicalScale (r := k - 1) N)
      (fun j ↦ by simp only [canonicalScale]; positivity)
      point hsep (forwardFamily cluster)
      (forwardFamily_hasBoundedSpectrum cluster)
    calc
      (∑ x : {x // x ∈ cluster.X}, value x ^ K k) ≤
          (criticalSamplingPrefactor k delta *
              ∏ j : Fin (k - 1), (canonicalScale N j : ℝ)) *
            (∫ beta,
              Sampling.familyMaxPower (K k) (forwardFamily cluster) beta
                ∂Sampling.torusHaarMeasure (k - 1)) := by
        simpa only [value, point, criticalSamplingPrefactor] using hsamp
      _ ≤ (criticalSamplingPrefactor k delta *
              ∏ j : Fin (k - 1), (canonicalScale N j : ℝ)) *
            (∫ beta, fibreMaxPower k N (forwardTheta alpha) beta
              ∂torusHaar (k - 1)) := by
        apply mul_le_mul_of_nonneg_left
        · exact integral_forward_familyMaxPower_le cluster hX
        · exact mul_nonneg
            (pow_nonneg (by
              exact mul_nonneg
                (mul_nonneg (by norm_num) (by positivity))
                (Sampling.cellComparisonFactor_nonneg delta)) _)
            (Finset.prod_nonneg fun _ _ ↦ by positivity)
  have hlarge : ∀ x ∈ (Finset.univ : Finset {x // x ∈ cluster.X}),
      ‖g alpha N‖ / 2 ≤ value x := by
    intro x hx
    exact norm_forwardFamily_at_centre (by omega : 1 ≤ k) cluster x
  have hstrict' :
      (criticalSamplingPrefactor k delta *
          ∏ j : Fin (k - 1), (canonicalScale N j : ℝ)) *
        (∫ beta, fibreMaxPower k N (forwardTheta alpha) beta
          ∂torusHaar (k - 1)) <
      (((Finset.univ : Finset {x // x ∈ cluster.X}).card : ℝ) *
        (‖g alpha N‖ / 2) ^ K k) := by
    simpa using hstrict
  obtain ⟨x, hx, y, hy, hxy, hnot⟩ :=
    exists_collision_of_moment_bound
      (Finset.univ : Finset {x // x ∈ cluster.X}) separated value (K k)
      (A := ‖g alpha N‖)
      (upper := (criticalSamplingPrefactor k delta *
          ∏ j : Fin (k - 1), (canonicalScale N j : ℝ)) *
        (∫ beta, fibreMaxPower k N (forwardTheta alpha) beta
          ∂torusHaar (k - 1)))
      (norm_nonneg _) hlarge hupper hstrict'
  have hscaled : ∀ j : Fin (k - 1),
      (canonicalScale N j : ℝ) *
          ‖forwardOrbitPoint alpha (x.1.1 : ℤ) j -
            forwardOrbitPoint alpha (y.1.1 : ℤ) j‖ < delta := by
    simp only [separated, point] at hnot
    push Not at hnot
    exact hnot
  refine ⟨x.1, x.2, y.1, y.2, ?_,
    forward_collision_of_scaled_lt hN alpha hscaled⟩
  intro hval
  apply hxy
  exact Subtype.ext hval

theorem exists_backward_collision_of_sampling_strict
    {k N : ℕ} (hk : 2 ≤ k) (hN : 0 < N)
    {delta : ℝ} (hdelta : 0 < delta)
    {alpha : CoefficientVector k}
    (cluster : AllCuts.BackwardCluster k N alpha)
    (hX : cluster.X.Nonempty)
    (hstrict :
      (criticalSamplingPrefactor k delta *
          ∏ j : Fin (k - 1), (canonicalScale N j : ℝ)) *
        (∫ beta, fibreMaxPower k N (backwardTheta alpha) beta
          ∂torusHaar (k - 1)) <
      (cluster.X.card : ℝ) * (‖g alpha N‖ / 2) ^ K k) :
    ∃ x ∈ cluster.X, ∃ y ∈ cluster.X, x ≠ y ∧
      ∀ j : Fin (k - 1),
        distToInt
            (reflectedCentreDifference alpha (x.1 : ℤ) (y.1 : ℤ) j) <
          delta * ((N : ℝ)⁻¹) ^ (j.1 + 1) := by
  classical
  letI : Nonempty {x // x ∈ cluster.X} :=
    ⟨⟨hX.choose, hX.choose_spec⟩⟩
  let point : {x // x ∈ cluster.X} → Fin (k - 1) → UnitAddCircle :=
    fun x ↦ backwardOrbitPoint alpha (x.1.1 : ℤ)
  let separated : {x // x ∈ cluster.X} → {x // x ∈ cluster.X} → Prop :=
    fun x y ↦ ∃ j : Fin (k - 1),
      delta ≤ (canonicalScale N j : ℝ) * ‖point x j - point y j‖
  let value : {x // x ∈ cluster.X} → ℝ :=
    fun x ↦ ‖backwardFamily cluster x (point x)‖
  have hupper :
      ((Finset.univ : Finset {x // x ∈ cluster.X}) :
          Set {x // x ∈ cluster.X}).Pairwise separated →
        ∑ x : {x // x ∈ cluster.X}, value x ^ K k ≤
          (criticalSamplingPrefactor k delta *
              ∏ j : Fin (k - 1), (canonicalScale N j : ℝ)) *
            (∫ beta, fibreMaxPower k N (backwardTheta alpha) beta
              ∂torusHaar (k - 1)) := by
    intro hpair
    have hsep : Sampling.AnisotropicallySeparated delta
        (canonicalScale (r := k - 1) N) point := by
      intro x y hxy
      exact hpair (Finset.mem_univ x) (Finset.mem_univ y) hxy
    have hsamp := Sampling.anisotropicSampling_criticalExponent hdelta k hk
      (canonicalScale (r := k - 1) N)
      (fun j ↦ by simp only [canonicalScale]; positivity)
      point hsep (backwardFamily cluster)
      (backwardFamily_hasBoundedSpectrum cluster)
    calc
      (∑ x : {x // x ∈ cluster.X}, value x ^ K k) ≤
          (criticalSamplingPrefactor k delta *
              ∏ j : Fin (k - 1), (canonicalScale N j : ℝ)) *
            (∫ beta,
              Sampling.familyMaxPower (K k) (backwardFamily cluster) beta
                ∂Sampling.torusHaarMeasure (k - 1)) := by
        simpa only [value, point, criticalSamplingPrefactor] using hsamp
      _ ≤ (criticalSamplingPrefactor k delta *
              ∏ j : Fin (k - 1), (canonicalScale N j : ℝ)) *
            (∫ beta, fibreMaxPower k N (backwardTheta alpha) beta
              ∂torusHaar (k - 1)) := by
        apply mul_le_mul_of_nonneg_left
        · exact integral_backward_familyMaxPower_le cluster hX
        · exact mul_nonneg
            (pow_nonneg (by
              exact mul_nonneg
                (mul_nonneg (by norm_num) (by positivity))
                (Sampling.cellComparisonFactor_nonneg delta)) _)
            (Finset.prod_nonneg fun _ _ ↦ by positivity)
  have hlarge : ∀ x ∈ (Finset.univ : Finset {x // x ∈ cluster.X}),
      ‖g alpha N‖ / 2 ≤ value x := by
    intro x hx
    exact norm_backwardFamily_at_centre (by omega : 1 ≤ k) cluster x
  have hstrict' :
      (criticalSamplingPrefactor k delta *
          ∏ j : Fin (k - 1), (canonicalScale N j : ℝ)) *
        (∫ beta, fibreMaxPower k N (backwardTheta alpha) beta
          ∂torusHaar (k - 1)) <
      (((Finset.univ : Finset {x // x ∈ cluster.X}).card : ℝ) *
        (‖g alpha N‖ / 2) ^ K k) := by
    simpa using hstrict
  obtain ⟨x, hx, y, hy, hxy, hnot⟩ :=
    exists_collision_of_moment_bound
      (Finset.univ : Finset {x // x ∈ cluster.X}) separated value (K k)
      (A := ‖g alpha N‖)
      (upper := (criticalSamplingPrefactor k delta *
          ∏ j : Fin (k - 1), (canonicalScale N j : ℝ)) *
        (∫ beta, fibreMaxPower k N (backwardTheta alpha) beta
          ∂torusHaar (k - 1)))
      (norm_nonneg _) hlarge hupper hstrict'
  have hscaled : ∀ j : Fin (k - 1),
      (canonicalScale N j : ℝ) *
          ‖backwardOrbitPoint alpha (x.1.1 : ℤ) j -
            backwardOrbitPoint alpha (y.1.1 : ℤ) j‖ < delta := by
    simp only [separated, point] at hnot
    push Not at hnot
    exact hnot
  refine ⟨x.1, x.2, y.1, y.2, ?_,
    reflected_collision_of_scaled_lt hN alpha hscaled⟩
  intro hval
  apply hxy
  exact Subtype.ext hval

/-- Proposition 5.2, with every internal bridge discharged.  The only
analytic input is the externally stated critical Vinogradov mean-value
theorem; the dyadic maximal theorem, anisotropic sampling, cluster
cardinality loss, and absorption of fixed constants are all invoked through
proved results. -/
theorem clusterCollisionPrinciple_of_criticalVMVT
    (hVMVT : External.CriticalVMVT) {k : ℕ} (hk : 3 ≤ k) :
    Conditional.ClusterCollisionPrinciple k := by
  intro thresholdMargin hmargin delta hdelta
  have hkTwo : 2 ≤ k := by omega
  have hKnat : 0 < K k := by
    simp only [K]
    apply Nat.mul_pos
    · omega
    · omega
  have hKreal : 0 < (K k : ℝ) := by exact_mod_cast hKnat
  let eta : ℝ := (K k : ℝ) * thresholdMargin / 2
  have heta : 0 < eta := by
    dsimp [eta]
    positivity
  obtain ⟨C, hC, Nvmvt, hNvmvt, hmoment⟩ :=
    fibreMaxPower_criticalVMVT_eventual hVMVT k hk eta heta
  let absorbConstant : ℝ :=
    (((16 * k.factorial : ℕ) : ℝ) * (2 : ℝ) ^ K k) *
      (criticalSamplingPrefactor k delta * C)
  let lowerExponent : ℝ := (K k : ℝ) + eta
  let upperExponent : ℝ :=
    (K k : ℝ) + (K k : ℝ) * thresholdMargin
  have hexponents : lowerExponent < upperExponent := by
    dsimp [lowerExponent, upperExponent, eta]
    have hprod : 0 < (K k : ℝ) * thresholdMargin :=
      mul_pos hKreal hmargin
    linarith
  obtain ⟨Nabsorb, hNabsorb⟩ := Filter.eventually_atTop.mp
    (eventually_const_mul_rpow_lt_rpow absorbConstant
      lowerExponent upperExponent hexponents)
  let N₀ : ℕ := max 2 (max Nvmvt (max Nabsorb (8 * k.factorial)))
  refine ⟨N₀, by simp only [N₀, le_max_iff]; omega, ?_⟩
  intro N hN alpha hlarge
  have hNtwo : 2 ≤ N := by
    apply le_trans _ hN
    simp only [N₀]
    exact le_max_left _ _
  have hNpos : 0 < N := by omega
  have hNv : Nvmvt ≤ N := by
    apply le_trans _ hN
    simp only [N₀]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hNa : Nabsorb ≤ N := by
    apply le_trans _ hN
    simp only [N₀]
    exact le_trans
      (le_trans (le_max_left _ _) (le_max_right _ _))
      (le_max_right _ _)
  have hfactorialN : 8 * k.factorial ≤ N := by
    apply le_trans _ hN
    simp only [N₀]
    exact le_trans
      (le_trans (le_max_right _ _) (le_max_right _ _))
      (le_max_right _ _)
  have hsize : 8 * k.factorial ≤ N + 1 :=
    hfactorialN.trans (Nat.le_succ N)
  have hpowerN :
      (((16 * k.factorial : ℕ) : ℝ) * (2 : ℝ) ^ K k *
          (criticalSamplingPrefactor k delta * C)) *
        Real.rpow (N : ℝ) ((K k : ℝ) + eta) <
      Real.rpow (N : ℝ)
        ((K k : ℝ) + (K k : ℝ) * thresholdMargin) := by
    simpa only [absorbConstant, lowerExponent, upperExponent, mul_assoc] using
      hNabsorb N hNa
  constructor
  · intro cluster
    have hX : cluster.X.Nonempty :=
      forwardCluster_nonempty hsize cluster
    apply exists_forward_collision_of_sampling_strict hkTwo hNpos hdelta cluster hX
    apply sampling_strict_of_power_bounds hkTwo hNpos
      (hcard := le_sixteen_factorial_mul_of_div_le hsize cluster.card_lower)
      (hI := hmoment N hNv (forwardTheta alpha))
      (hlarge := hlarge)
      (hpower := hpowerN)
  · intro cluster
    have hX : cluster.X.Nonempty :=
      backwardCluster_nonempty hsize cluster
    apply exists_backward_collision_of_sampling_strict hkTwo hNpos hdelta cluster hX
    apply sampling_strict_of_power_bounds hkTwo hNpos
      (hcard := le_sixteen_factorial_mul_of_div_le hsize cluster.card_lower)
      (hI := hmoment N hNv (backwardTheta alpha))
      (hlarge := hlarge)
      (hpower := hpowerN)

end

end OrbitCollision
end ImprovedWeylBounds
