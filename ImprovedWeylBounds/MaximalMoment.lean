import ImprovedWeylBounds.VinogradovTranslation

/-!
# Internal maximal-moment reductions

This module proves the finite Fourier-algebra and measure-theoretic steps
behind the manuscript's maximal-moment argument:

* exact expansion and Haar orthogonality for a `2s` moment;
* reduction on a fixed-leading-coefficient fibre to the Vinogradov mean
  value, including arbitrary integer translates of the summation interval;
* the convexity, finite-maximum, and integration steps that turn a bounded
  block decomposition of every partial interval into interval moments.

The external critical VMVT estimate is deliberately not proved here.  Nor
does this module assert that the manuscript's particular family of partial
intervals has a chosen dyadic decomposition: that combinatorial choice is
represented by the explicit `pieces`, `hpieces`, `hcard`, and `hdecomp`
hypotheses of the final lemmas.  Thus no unproved bridge is hidden as a
global assumption.
-/

open scoped BigOperators
open MeasureTheory

namespace ImprovedWeylBounds

attribute [local instance] Classical.propDecidable

noncomputable def unitHaar : Measure UnitAddCircle :=
  @AddCircle.haarAddCircle 1 (Fact.mk zero_lt_one)

noncomputable local instance : IsProbabilityMeasure unitHaar := by
  dsimp [unitHaar]
  infer_instance

theorem integral_fourier_unit (n : ℤ) :
    (∫ x : UnitAddCircle, fourier n x ∂unitHaar) =
      if n = 0 then 1 else 0 := by
  letI : Fact (0 < (1 : ℝ)) := Fact.mk zero_lt_one
  have h := congrFun (fourierCoeff_fourier (T := (1 : ℝ)) n) 0
  simp [fourierCoeff] at h
  simpa [Pi.single_apply, eq_comm, unitHaar] using h

noncomputable def torusHaar (r : ℕ) : Measure (Fin r → UnitAddCircle) :=
  Measure.pi fun _ => unitHaar

noncomputable local instance (r : ℕ) : IsProbabilityMeasure (torusHaar r) := by
  dsimp [torusHaar]
  infer_instance

noncomputable def torusCharacter {r : ℕ} (m : Fin r → ℤ)
    (β : Fin r → UnitAddCircle) : ℂ :=
  ∏ j, fourier (m j) (β j)

theorem integral_torusCharacter {r : ℕ} (m : Fin r → ℤ) :
    (∫ β, torusCharacter m β ∂torusHaar r) =
      if m = 0 then 1 else 0 := by
  letI : Fact (0 < (1 : ℝ)) := Fact.mk zero_lt_one
  change (∫ β : Fin r → UnitAddCircle,
    ∏ j, fourier (m j) (β j) ∂(Measure.pi fun _ => unitHaar)) = _
  rw [MeasureTheory.integral_fintype_prod_eq_prod]
  simp_rw [integral_fourier_unit]
  by_cases hm : m = 0
  · subst m
    simp
  · rw [if_neg hm]
    have hj : ∃ j, m j ≠ 0 := by simpa [funext_iff] using hm
    obtain ⟨j, hj⟩ := hj
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [hj]

@[simp]
theorem torusCharacter_zero {r : ℕ} (β : Fin r → UnitAddCircle) :
    torusCharacter (0 : Fin r → ℤ) β = 1 := by
  simp [torusCharacter]

theorem torusCharacter_add {r : ℕ} (m n : Fin r → ℤ)
    (β : Fin r → UnitAddCircle) :
    torusCharacter (m + n) β = torusCharacter m β * torusCharacter n β := by
  simp only [torusCharacter, Pi.add_apply, fourier_add]
  exact Finset.prod_mul_distrib

@[simp]
theorem torusCharacter_neg {r : ℕ} (m : Fin r → ℤ)
    (β : Fin r → UnitAddCircle) :
    torusCharacter (-m) β = star (torusCharacter m β) := by
  simp [torusCharacter]

theorem prod_torusCharacter_finset {ι : Type*} {r : ℕ}
    (S : Finset ι) (m : ι → Fin r → ℤ) (β : Fin r → UnitAddCircle) :
    ∏ i ∈ S, torusCharacter (m i) β =
      torusCharacter (fun j => ∑ i ∈ S, m i j) β := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      change 1 = torusCharacter (0 : Fin r → ℤ) β
      rw [torusCharacter_zero]
  | @insert a S ha ih =>
      rw [Finset.prod_insert ha, ih]
      rw [← torusCharacter_add]
      congr 1
      funext j
      simp [ha]

theorem prod_torusCharacter {ι : Type*} [Fintype ι] {r : ℕ}
    (m : ι → Fin r → ℤ) (β : Fin r → UnitAddCircle) :
    ∏ i, torusCharacter (m i) β =
      torusCharacter (fun j => ∑ i, m i j) β := by
  simpa using prod_torusCharacter_finset Finset.univ m β

noncomputable def tupleFrequency {ι : Type*} {r s : ℕ}
    (frequency : ι → Fin r → ℤ) (x : Fin s → ι) : Fin r → ℤ :=
  fun j => ∑ i, frequency (x i) j

noncomputable def tupleWeight {ι : Type*} {s : ℕ}
    (weight : ι → ℂ) (x : Fin s → ι) : ℂ :=
  ∏ i, weight (x i)

noncomputable def torusPolynomial {ι : Type*} [Fintype ι] {r : ℕ}
    (weight : ι → ℂ) (frequency : ι → Fin r → ℤ)
    (β : Fin r → UnitAddCircle) : ℂ :=
  ∑ x, weight x * torusCharacter (frequency x) β

theorem torusPolynomial_pow {ι : Type*} [Fintype ι] {r s : ℕ}
    (weight : ι → ℂ) (frequency : ι → Fin r → ℤ)
    (β : Fin r → UnitAddCircle) :
    torusPolynomial weight frequency β ^ s =
      ∑ x : Fin s → ι,
        tupleWeight weight x * torusCharacter (tupleFrequency frequency x) β := by
  rw [torusPolynomial, Fintype.sum_pow]
  apply Fintype.sum_congr
  intro x
  rw [Finset.prod_mul_distrib]
  rw [prod_torusCharacter]
  rfl

theorem star_torusPolynomial {ι : Type*} [Fintype ι] {r : ℕ}
    (weight : ι → ℂ) (frequency : ι → Fin r → ℤ)
    (β : Fin r → UnitAddCircle) :
    star (torusPolynomial weight frequency β) =
      torusPolynomial (fun x => star (weight x)) (fun x => -frequency x) β := by
  simp [torusPolynomial, torusCharacter_neg]

theorem star_torusPolynomial_pow {ι : Type*} [Fintype ι] {r s : ℕ}
    (weight : ι → ℂ) (frequency : ι → Fin r → ℤ)
    (β : Fin r → UnitAddCircle) :
    star (torusPolynomial weight frequency β) ^ s =
      ∑ y : Fin s → ι,
        star (tupleWeight weight y) * torusCharacter (-tupleFrequency frequency y) β := by
  rw [star_torusPolynomial, torusPolynomial_pow]
  apply Fintype.sum_congr
  intro y
  congr 1
  · simp [tupleWeight]
  · congr 1
    funext j
    simp [tupleFrequency]

theorem torusPolynomial_absMoment_expansion
    {ι : Type*} [Fintype ι] {r s : ℕ}
    (weight : ι → ℂ) (frequency : ι → Fin r → ℤ)
    (β : Fin r → UnitAddCircle) :
    torusPolynomial weight frequency β ^ s *
        star (torusPolynomial weight frequency β) ^ s =
      ∑ x : Fin s → ι, ∑ y : Fin s → ι,
        (tupleWeight weight x * star (tupleWeight weight y)) *
          torusCharacter
            (tupleFrequency frequency x - tupleFrequency frequency y) β := by
  rw [torusPolynomial_pow, star_torusPolynomial_pow]
  rw [Finset.sum_mul]
  apply Fintype.sum_congr
  intro x
  rw [Finset.mul_sum]
  apply Fintype.sum_congr
  intro y
  calc
    (tupleWeight weight x * torusCharacter (tupleFrequency frequency x) β) *
        (star (tupleWeight weight y) *
          torusCharacter (-tupleFrequency frequency y) β) =
      (tupleWeight weight x * star (tupleWeight weight y)) *
        (torusCharacter (tupleFrequency frequency x) β *
          torusCharacter (-tupleFrequency frequency y) β) := by ring
    _ = (tupleWeight weight x * star (tupleWeight weight y)) *
        torusCharacter
          (tupleFrequency frequency x + -tupleFrequency frequency y) β := by
      rw [torusCharacter_add]
    _ = (tupleWeight weight x * star (tupleWeight weight y)) *
        torusCharacter
          (tupleFrequency frequency x - tupleFrequency frequency y) β := by rfl

theorem continuous_torusCharacter {r : ℕ} (m : Fin r → ℤ) :
    Continuous (torusCharacter m) := by
  unfold torusCharacter
  fun_prop

theorem continuous_torusPolynomial
    {ι : Type*} [Fintype ι] {r : ℕ}
    (weight : ι → ℂ) (frequency : ι → Fin r → ℤ) :
    Continuous (torusPolynomial weight frequency) := by
  change Continuous (fun β =>
    ∑ x, weight x * torusCharacter (frequency x) β)
  exact continuous_finsetSum Finset.univ fun x _ =>
    continuous_const.mul (continuous_torusCharacter (frequency x))

theorem integrable_norm_torusPolynomial_pow
    {ι : Type*} [Fintype ι] {r : ℕ}
    (weight : ι → ℂ) (frequency : ι → Fin r → ℤ) (p : ℕ) :
    Integrable (fun β => ‖torusPolynomial weight frequency β‖ ^ p)
      (torusHaar r) := by
  have hc : Continuous
      (fun β => ‖torusPolynomial weight frequency β‖ ^ p) := by
    change Continuous ((fun β => ‖torusPolynomial weight frequency β‖) ^ p)
    exact (continuous_torusPolynomial weight frequency).norm.pow p
  simpa using hc.continuousOn.integrableOn_compact isCompact_univ

theorem integrable_torusCharacter {r : ℕ} (m : Fin r → ℤ) :
    Integrable (torusCharacter m) (torusHaar r) := by
  apply Integrable.of_bound (continuous_torusCharacter m).aestronglyMeasurable 1
  apply Filter.Eventually.of_forall
  intro β
  simp [torusCharacter]

theorem integral_torusPolynomial_absMoment
    {ι : Type*} [Fintype ι] {r s : ℕ}
    (weight : ι → ℂ) (frequency : ι → Fin r → ℤ) :
    (∫ β,
      torusPolynomial weight frequency β ^ s *
        star (torusPolynomial weight frequency β) ^ s ∂torusHaar r) =
      ∑ x : Fin s → ι, ∑ y : Fin s → ι,
        (tupleWeight weight x * star (tupleWeight weight y)) *
          (if tupleFrequency frequency x = tupleFrequency frequency y then 1 else 0) := by
  have hxy (x y : Fin s → ι) : Integrable
      (fun β : Fin r → UnitAddCircle =>
        (tupleWeight weight x * star (tupleWeight weight y)) *
          torusCharacter
            (tupleFrequency frequency x - tupleFrequency frequency y) β)
      (torusHaar r) :=
    (integrable_torusCharacter
      (tupleFrequency frequency x - tupleFrequency frequency y)).const_mul _
  have hx (x : Fin s → ι) : Integrable
      (fun β : Fin r → UnitAddCircle =>
        ∑ y : Fin s → ι,
          (tupleWeight weight x * star (tupleWeight weight y)) *
            torusCharacter
              (tupleFrequency frequency x - tupleFrequency frequency y) β)
      (torusHaar r) := by
    have hs : Integrable
        (∑ y : Fin s → ι, fun β : Fin r → UnitAddCircle =>
          (tupleWeight weight x * star (tupleWeight weight y)) *
            torusCharacter
              (tupleFrequency frequency x - tupleFrequency frequency y) β)
        (torusHaar r) :=
      MeasureTheory.integrable_finsetSum' Finset.univ fun y _ => hxy x y
    apply hs.congr
    filter_upwards [] with β
    simp only [Finset.sum_apply]
  rw [show (fun β =>
      torusPolynomial weight frequency β ^ s *
        star (torusPolynomial weight frequency β) ^ s) =
      (fun β => ∑ x : Fin s → ι, ∑ y : Fin s → ι,
        (tupleWeight weight x * star (tupleWeight weight y)) *
          torusCharacter
            (tupleFrequency frequency x - tupleFrequency frequency y) β) by
        funext β
        exact torusPolynomial_absMoment_expansion weight frequency β]
  rw [MeasureTheory.integral_finsetSum Finset.univ (fun x _ => hx x)]
  apply Fintype.sum_congr
  intro x
  rw [MeasureTheory.integral_finsetSum Finset.univ (fun y _ => hxy x y)]
  apply Fintype.sum_congr
  intro y
  rw [MeasureTheory.integral_const_mul]
  rw [integral_torusCharacter]
  congr 1
  simp [sub_eq_zero]

/-- The number of pairs of `s`-tuples with the same total frequency. -/
noncomputable def frequencyCollisionCount
    {ι : Type*} [Fintype ι] {r s : ℕ}
    (frequency : ι → Fin r → ℤ) : ℕ := by
  classical
  exact Fintype.card
    {xy : (Fin s → ι) × (Fin s → ι) //
      tupleFrequency frequency xy.1 = tupleFrequency frequency xy.2}

private theorem norm_tupleWeight_le_one
    {ι : Type*} {s : ℕ} (weight : ι → ℂ)
    (hweight : ∀ n, ‖weight n‖ ≤ 1) (x : Fin s → ι) :
    ‖tupleWeight weight x‖ ≤ 1 := by
  rw [tupleWeight]
  rw [norm_prod]
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun i _ => hweight (x i))

/-- Orthogonality bounds a fixed-weight torus moment by the number of
frequency collisions.  No analytic estimate enters this finite identity. -/
theorem norm_integral_torusPolynomial_absMoment_le_collisionCount
    {ι : Type*} [Fintype ι] {r s : ℕ}
    (weight : ι → ℂ) (frequency : ι → Fin r → ℤ)
    (hweight : ∀ n, ‖weight n‖ ≤ 1) :
    ‖∫ β,
      torusPolynomial weight frequency β ^ s *
        star (torusPolynomial weight frequency β) ^ s ∂torusHaar r‖ ≤
      frequencyCollisionCount (s := s) frequency := by
  classical
  rw [integral_torusPolynomial_absMoment]
  calc
    ‖∑ x : Fin s → ι, ∑ y : Fin s → ι,
        (tupleWeight weight x * star (tupleWeight weight y)) *
          (if tupleFrequency frequency x = tupleFrequency frequency y then 1 else 0)‖
        ≤ ∑ x : Fin s → ι, ‖∑ y : Fin s → ι,
            (tupleWeight weight x * star (tupleWeight weight y)) *
              (if tupleFrequency frequency x = tupleFrequency frequency y then 1 else 0)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ x : Fin s → ι, ∑ y : Fin s → ι,
          ‖(tupleWeight weight x * star (tupleWeight weight y)) *
            (if tupleFrequency frequency x = tupleFrequency frequency y then 1 else 0)‖ := by
      apply Finset.sum_le_sum
      intro x hx
      exact norm_sum_le _ _
    _ ≤ ∑ x : Fin s → ι, ∑ y : Fin s → ι,
          (if tupleFrequency frequency x = tupleFrequency frequency y then 1 else 0) := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro y hy
      by_cases hxy : tupleFrequency frequency x = tupleFrequency frequency y
      · simp only [hxy, if_true, mul_one, norm_mul, norm_star]
        exact mul_le_one₀ (norm_tupleWeight_le_one weight hweight x)
          (norm_nonneg _) (norm_tupleWeight_le_one weight hweight y)
      · simp [hxy]
    _ = frequencyCollisionCount (s := s) frequency := by
      rw [← Fintype.sum_prod_type']
      rw [Finset.sum_boole]
      rw [frequencyCollisionCount, Fintype.card_subtype]

theorem complex_pow_mul_star_pow (z : ℂ) (s : ℕ) :
    z ^ s * star z ^ s = ((‖z‖ ^ (2 * s) : ℝ) : ℂ) := by
  rw [← mul_pow]
  have hconj : z * star z = (Complex.normSq z : ℂ) := Complex.mul_conj z
  rw [hconj, Complex.normSq_eq_norm_sq]
  rw [← Complex.ofReal_pow]
  congr 1
  rw [← pow_mul]

/-- The vector of the first `r` positive monomial frequencies at `n + 1`. -/
def monomialFrequency (r : ℕ) {N : ℕ} (n : Fin N) : Fin r → ℤ :=
  fun j => ((n.val + 1 : ℕ) : ℤ) ^ (j.val + 1)

/-- The fixed coefficient of degree `r + 1`, regarded as a unit-circle
character weight. -/
noncomputable def fixedLeadingWeight (r : ℕ) {N : ℕ}
    (θ : UnitAddCircle) (n : Fin N) : ℂ :=
  fourier (((n.val + 1 : ℕ) : ℤ) ^ (r + 1)) θ

/-- Weyl polynomial on the fibre where the coefficient of degree `r + 1`
is fixed to `θ`, while the first `r` coefficients range over the torus. -/
noncomputable def fixedLeadingFibreSum (r N : ℕ) (θ : UnitAddCircle)
    (β : Fin r → UnitAddCircle) : ℂ :=
  torusPolynomial (ι := Fin N) (r := r)
    (fixedLeadingWeight r θ) (monomialFrequency r) β

theorem tupleFrequency_monomial_eq_iff
    (s r N : ℕ) (x y : Fin s → Fin N) :
    tupleFrequency (monomialFrequency r) x =
        tupleFrequency (monomialFrequency r) y ↔
      External.VinogradovSystem s r N x y := by
  constructor
  · intro h j
    have hj := congrFun h j
    simp only [tupleFrequency, monomialFrequency] at hj
    exact_mod_cast hj
  · intro h
    funext j
    have hj := h j
    simp only [tupleFrequency, monomialFrequency]
    exact_mod_cast hj

theorem monomial_frequencyCollisionCount_eq_vinogradovMeanValue
    (s r N : ℕ) :
    frequencyCollisionCount (s := s) (monomialFrequency r : Fin N → Fin r → ℤ) =
      External.vinogradovMeanValue s r N := by
  classical
  apply Fintype.card_congr
  exact
    { toFun := fun z =>
        ⟨z.1, (tupleFrequency_monomial_eq_iff s r N z.1.1 z.1.2).1 z.2⟩
      invFun := fun z =>
        ⟨z.1, (tupleFrequency_monomial_eq_iff s r N z.1.1 z.1.2).2 z.2⟩
      left_inv := fun z => by cases z; rfl
      right_inv := fun z => by cases z; rfl }

/-- Exact orthogonality expansion on a fixed-leading-coefficient fibre.
Only pairs satisfying the degree-`r` Vinogradov system survive integration;
their degree-`r+1` phases remain as unit weights. -/
theorem integral_fixedLeadingFibre_absMoment_expansion
    (s r N : ℕ) (θ : UnitAddCircle) :
    (∫ β, fixedLeadingFibreSum r N θ β ^ s *
        star (fixedLeadingFibreSum r N θ β) ^ s ∂torusHaar r) =
      ∑ x : Fin s → Fin N, ∑ y : Fin s → Fin N,
        (tupleWeight (fixedLeadingWeight r θ) x *
          star (tupleWeight (fixedLeadingWeight r θ) y)) *
          (if External.VinogradovSystem s r N x y then 1 else 0) := by
  simpa only [fixedLeadingFibreSum, tupleFrequency_monomial_eq_iff] using
    (integral_torusPolynomial_absMoment
      (s := s) (r := r) (ι := Fin N)
      (fixedLeadingWeight r θ) (monomialFrequency r))

/-- The exact internal moment reduction on a fixed-leading-coefficient fibre:
the `2s`-moment over the lower coefficients is at most `J_{s,r}(N)`. -/
theorem fixedLeadingFibre_moment_le_vinogradovMeanValue
    (s r N : ℕ) (θ : UnitAddCircle) :
    (∫ β, ‖fixedLeadingFibreSum r N θ β‖ ^ (2 * s) ∂torusHaar r) ≤
      External.vinogradovMeanValue s r N := by
  let F := fixedLeadingFibreSum r N θ
  have hcomplex :
      ((∫ β, ‖F β‖ ^ (2 * s) ∂torusHaar r : ℝ) : ℂ) =
        ∫ β, F β ^ s * star (F β) ^ s ∂torusHaar r := by
    calc
      ((∫ β, ‖F β‖ ^ (2 * s) ∂torusHaar r : ℝ) : ℂ) =
          ∫ β, ((‖F β‖ ^ (2 * s) : ℝ) : ℂ) ∂torusHaar r :=
        (integral_ofReal (𝕜 := ℂ)
          (f := fun β => ‖F β‖ ^ (2 * s))).symm
      _ = ∫ β, F β ^ s * star (F β) ^ s ∂torusHaar r := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with β
        exact (complex_pow_mul_star_pow (F β) s).symm
  have hnonneg : 0 ≤ ∫ β, ‖F β‖ ^ (2 * s) ∂torusHaar r := by
    apply MeasureTheory.integral_nonneg
    intro β
    positivity
  calc
    (∫ β, ‖F β‖ ^ (2 * s) ∂torusHaar r) =
        ‖((∫ β, ‖F β‖ ^ (2 * s) ∂torusHaar r : ℝ) : ℂ)‖ := by
      simp [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    _ = ‖∫ β, F β ^ s * star (F β) ^ s ∂torusHaar r‖ :=
      congrArg norm hcomplex
    _ ≤ frequencyCollisionCount (s := s)
          (monomialFrequency r : Fin N → Fin r → ℤ) := by
      simpa [F, fixedLeadingFibreSum] using
        (norm_integral_torusPolynomial_absMoment_le_collisionCount
          (s := s) (r := r) (ι := Fin N)
          (fixedLeadingWeight r θ) (monomialFrequency r) (by
            intro n
            simp [fixedLeadingWeight]))
    _ = External.vinogradovMeanValue s r N := by
      exact_mod_cast monomial_frequencyCollisionCount_eq_vinogradovMeanValue s r N

/-- The first `r` monomial frequencies on the translated integer interval
`{c + 1, ..., c + N}`. -/
def translatedMonomialFrequency (r : ℕ) (c : ℤ) {N : ℕ}
    (n : Fin N) : Fin r → ℤ :=
  fun j => ((n.val + 1 : ℕ) + c) ^ (j.val + 1)

noncomputable def translatedFixedLeadingWeight (r : ℕ) (c : ℤ) {N : ℕ}
    (θ : UnitAddCircle) (n : Fin N) : ℂ :=
  fourier (((n.val + 1 : ℕ) + c) ^ (r + 1)) θ

noncomputable def translatedFixedLeadingFibreSum
    (r N : ℕ) (c : ℤ) (θ : UnitAddCircle)
    (β : Fin r → UnitAddCircle) : ℂ :=
  torusPolynomial (ι := Fin N) (r := r)
    (translatedFixedLeadingWeight r c θ)
    (translatedMonomialFrequency r c) β

private theorem tupleFrequency_translatedMonomial_eq_iff_equalPowerSums
    (s r N : ℕ) (c : ℤ) (x y : Fin s → Fin N) :
    tupleFrequency (translatedMonomialFrequency r c) x =
        tupleFrequency (translatedMonomialFrequency r c) y ↔
      EqualPowerSumsUpTo r
        (fun i => (x i).val.succ + c)
        (fun i => (y i).val.succ + c) := by
  constructor
  · intro h n hn hnr
    have hnfin : n - 1 < r := by omega
    have hj := congrFun h ⟨n - 1, hnfin⟩
    have hexp : n - 1 + 1 = n := by omega
    simpa only [tupleFrequency, translatedMonomialFrequency, hexp,
      Nat.cast_succ] using hj
  · intro h
    funext j
    exact h j.val.succ (by omega) (by omega)

theorem tupleFrequency_translatedMonomial_eq_iff
    (s r N : ℕ) (c : ℤ) (x y : Fin s → Fin N) :
    tupleFrequency (translatedMonomialFrequency r c) x =
        tupleFrequency (translatedMonomialFrequency r c) y ↔
      External.VinogradovSystem s r N x y := by
  rw [tupleFrequency_translatedMonomial_eq_iff_equalPowerSums]
  exact (vinogradovSystem_iff_int_translate s r N x y c).symm

theorem translatedMonomial_frequencyCollisionCount_eq_vinogradovMeanValue
    (s r N : ℕ) (c : ℤ) :
    frequencyCollisionCount (s := s)
        (translatedMonomialFrequency r c : Fin N → Fin r → ℤ) =
      External.vinogradovMeanValue s r N := by
  classical
  apply Fintype.card_congr
  exact
    { toFun := fun z =>
        ⟨z.1,
          (tupleFrequency_translatedMonomial_eq_iff
            s r N c z.1.1 z.1.2).1 z.2⟩
      invFun := fun z =>
        ⟨z.1,
          (tupleFrequency_translatedMonomial_eq_iff
            s r N c z.1.1 z.1.2).2 z.2⟩
      left_inv := fun z => by cases z; rfl
      right_inv := fun z => by cases z; rfl }

/-- The same fixed-fibre moment reduction on every translated interval of
length `N`.  Translation invariance is supplied by the proved theorem in
`VinogradovTranslation`, not by an additional analytic hypothesis. -/
theorem translatedFixedLeadingFibre_moment_le_vinogradovMeanValue
    (s r N : ℕ) (c : ℤ) (θ : UnitAddCircle) :
    (∫ β, ‖translatedFixedLeadingFibreSum r N c θ β‖ ^ (2 * s)
        ∂torusHaar r) ≤
      External.vinogradovMeanValue s r N := by
  let F := translatedFixedLeadingFibreSum r N c θ
  have hcomplex :
      ((∫ β, ‖F β‖ ^ (2 * s) ∂torusHaar r : ℝ) : ℂ) =
        ∫ β, F β ^ s * star (F β) ^ s ∂torusHaar r := by
    calc
      ((∫ β, ‖F β‖ ^ (2 * s) ∂torusHaar r : ℝ) : ℂ) =
          ∫ β, ((‖F β‖ ^ (2 * s) : ℝ) : ℂ) ∂torusHaar r :=
        (integral_ofReal (𝕜 := ℂ)
          (f := fun β => ‖F β‖ ^ (2 * s))).symm
      _ = ∫ β, F β ^ s * star (F β) ^ s ∂torusHaar r := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with β
        exact (complex_pow_mul_star_pow (F β) s).symm
  have hnonneg : 0 ≤ ∫ β, ‖F β‖ ^ (2 * s) ∂torusHaar r := by
    apply MeasureTheory.integral_nonneg
    intro β
    positivity
  calc
    (∫ β, ‖F β‖ ^ (2 * s) ∂torusHaar r) =
        ‖((∫ β, ‖F β‖ ^ (2 * s) ∂torusHaar r : ℝ) : ℂ)‖ := by
      simp [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    _ = ‖∫ β, F β ^ s * star (F β) ^ s ∂torusHaar r‖ :=
      congrArg norm hcomplex
    _ ≤ frequencyCollisionCount (s := s)
          (translatedMonomialFrequency r c : Fin N → Fin r → ℤ) := by
      simpa [F, translatedFixedLeadingFibreSum] using
        (norm_integral_torusPolynomial_absMoment_le_collisionCount
          (s := s) (r := r) (ι := Fin N)
          (translatedFixedLeadingWeight r c θ)
          (translatedMonomialFrequency r c) (by
            intro n
            simp [translatedFixedLeadingWeight]))
    _ = External.vinogradovMeanValue s r N := by
      exact_mod_cast
        translatedMonomial_frequencyCollisionCount_eq_vinogradovMeanValue
          s r N c

/-- Direct consequence of the external critical VMVT at the fixed-leading
fibre.  All Fourier and orthogonality steps preceding the external estimate
are proved in this module. -/
theorem fixedLeadingFibre_criticalVMVT_bound
    (hVMVT : External.CriticalVMVT)
    (r : ℕ) (hr : 1 ≤ r) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 1 ≤ N → ∀ θ : UnitAddCircle,
      (∫ β,
        ‖fixedLeadingFibreSum r N θ β‖ ^
          (2 * External.criticalMoment r) ∂torusHaar r) ≤
        C * Real.rpow (N : ℝ)
          ((External.criticalMoment r : ℝ) + ε) := by
  obtain ⟨C, hC, hbound⟩ := hVMVT r hr ε hε
  refine ⟨C, hC, ?_⟩
  intro N hN θ
  exact (fixedLeadingFibre_moment_le_vinogradovMeanValue
    (External.criticalMoment r) r N θ).trans (hbound N hN)

/-- Critical-VMVT fibre bound, uniform also in the integral translate of the
summation interval. -/
theorem translatedFixedLeadingFibre_criticalVMVT_bound
    (hVMVT : External.CriticalVMVT)
    (r : ℕ) (hr : 1 ≤ r) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 1 ≤ N → ∀ (c : ℤ)
      (θ : UnitAddCircle),
      (∫ β,
        ‖translatedFixedLeadingFibreSum r N c θ β‖ ^
          (2 * External.criticalMoment r) ∂torusHaar r) ≤
        C * Real.rpow (N : ℝ)
          ((External.criticalMoment r : ℝ) + ε) := by
  obtain ⟨C, hC, hbound⟩ := hVMVT r hr ε hε
  refine ⟨C, hC, ?_⟩
  intro N hN c θ
  exact (translatedFixedLeadingFibre_moment_le_vinogradovMeanValue
    (External.criticalMoment r) r N c θ).trans (hbound N hN)

/-! ## Finite dyadic/maximal reduction -/

/-- The explicit combinatorial bridge needed by the dyadic argument.  It
says that every candidate partial value is the sum of at most `L` members of
a common finite block pool.  Establishing this predicate for a concrete
choice of dyadic intervals is logically separate from the moment algebra. -/
def HasFiniteBlockDecomposition
    {τ ι E : Type*} [AddCommMonoid E]
    (blocks : Finset ι) (pieces : τ → Finset ι)
    (blockValue : ι → E) (partialValue : τ → E) (L : ℕ) : Prop :=
  (∀ t, pieces t ⊆ blocks) ∧
  (∀ t, (pieces t).card ≤ L) ∧
  ∀ t, partialValue t = ∑ i ∈ pieces t, blockValue i

/-- Power convexity after the triangle inequality.  This is the algebraic
loss used when a partial interval is written as a union of a bounded number
of dyadic blocks. -/
theorem norm_finset_sum_pow_le_card_mul_sum_norm_pow
    {ι E : Type*} [NormedAddCommGroup E]
    (S : Finset ι) (v : ι → E) (p : ℕ) (hp : 1 ≤ p) :
    ‖∑ i ∈ S, v i‖ ^ p ≤
      (S.card : ℝ) ^ (p - 1) * ∑ i ∈ S, ‖v i‖ ^ p := by
  have hnorm : ‖∑ i ∈ S, v i‖ ≤ ∑ i ∈ S, ‖v i‖ := norm_sum_le _ _
  have hpform : p - 1 + 1 = p := by omega
  calc
    ‖∑ i ∈ S, v i‖ ^ p ≤ (∑ i ∈ S, ‖v i‖) ^ p :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm p
    _ = (∑ i ∈ S, ‖v i‖) ^ (p - 1 + 1) := by rw [hpform]
    _ ≤ (S.card : ℝ) ^ (p - 1) *
        ∑ i ∈ S, ‖v i‖ ^ (p - 1 + 1) :=
      pow_sum_le_card_mul_sum_pow (fun i hi => norm_nonneg (v i)) (p - 1)
    _ = (S.card : ℝ) ^ (p - 1) * ∑ i ∈ S, ‖v i‖ ^ p := by
      rw [hpform]

/-- Pointwise reduction for a family of partial sums.  `pieces t` is the
chosen dyadic decomposition of the partial sum indexed by `t`; `blocks` is
the common pool of all interval blocks whose moments will be estimated. -/
theorem decomposed_partial_sum_pow_le
    {τ ι E : Type*} [NormedAddCommGroup E]
    (blocks : Finset ι) (pieces : τ → Finset ι)
    (blockValue : ι → E) (partialValue : τ → E)
    (p L : ℕ) (hp : 1 ≤ p)
    (hpieces : ∀ t, pieces t ⊆ blocks)
    (hcard : ∀ t, (pieces t).card ≤ L)
    (hdecomp : ∀ t, partialValue t = ∑ i ∈ pieces t, blockValue i)
    (t : τ) :
    ‖partialValue t‖ ^ p ≤
      (L : ℝ) ^ (p - 1) * ∑ i ∈ blocks, ‖blockValue i‖ ^ p := by
  rw [hdecomp t]
  have hlocal := norm_finset_sum_pow_le_card_mul_sum_norm_pow
    (pieces t) blockValue p hp
  calc
    ‖∑ i ∈ pieces t, blockValue i‖ ^ p ≤
        ((pieces t).card : ℝ) ^ (p - 1) *
          ∑ i ∈ pieces t, ‖blockValue i‖ ^ p := hlocal
    _ ≤ (L : ℝ) ^ (p - 1) * ∑ i ∈ pieces t, ‖blockValue i‖ ^ p := by
      gcongr
      exact_mod_cast hcard t
    _ ≤ (L : ℝ) ^ (p - 1) * ∑ i ∈ blocks, ‖blockValue i‖ ^ p := by
      apply mul_le_mul_of_nonneg_left
      · exact Finset.sum_le_sum_of_subset_of_nonneg (hpieces t)
          (fun i hi hnot => by positivity)
      · positivity

/-- Taking the maximum over finitely many candidate endpoints introduces no
additional loss once every endpoint has a bounded block decomposition. -/
theorem dyadic_finiteMax_pow_le
    {τ ι E : Type*} [NormedAddCommGroup E]
    (endpoints : Finset τ) (hendpoints : endpoints.Nonempty)
    (blocks : Finset ι) (pieces : τ → Finset ι)
    (blockValue : ι → E) (partialValue : τ → E)
    (p L : ℕ) (hp : 1 ≤ p)
    (hpieces : ∀ t, pieces t ⊆ blocks)
    (hcard : ∀ t, (pieces t).card ≤ L)
    (hdecomp : ∀ t, partialValue t = ∑ i ∈ pieces t, blockValue i) :
    endpoints.sup' hendpoints (fun t => ‖partialValue t‖ ^ p) ≤
      (L : ℝ) ^ (p - 1) * ∑ i ∈ blocks, ‖blockValue i‖ ^ p := by
  apply Finset.sup'_le hendpoints
  intro t ht
  exact decomposed_partial_sum_pow_le blocks pieces blockValue partialValue
    p L hp hpieces hcard hdecomp t

/-- Measure-theoretic assembly of the finite dyadic reduction.  Once each
candidate partial sum is decomposed into at most `L` blocks, its maximal
`p`-moment is controlled by the sum of the individual block moments.  The
integrability assumptions are explicit and are routine for finite
trigonometric polynomials. -/
theorem integral_dyadic_finiteMax_pow_le_sum_intervalMoments
    {X τ ι E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    (μ : Measure X)
    (endpoints : Finset τ) (hendpoints : endpoints.Nonempty)
    (blocks : Finset ι) (pieces : τ → Finset ι)
    (blockValue : ι → X → E) (partialValue : τ → X → E)
    (p L : ℕ) (hp : 1 ≤ p)
    (hpieces : ∀ t, pieces t ⊆ blocks)
    (hcard : ∀ t, (pieces t).card ≤ L)
    (hdecomp : ∀ t x, partialValue t x =
      ∑ i ∈ pieces t, blockValue i x)
    (hblock : ∀ i ∈ blocks,
      Integrable (fun x => ‖blockValue i x‖ ^ p) μ)
    (hmax : Integrable (fun x =>
      endpoints.sup' hendpoints (fun t => ‖partialValue t x‖ ^ p)) μ) :
    (∫ x, endpoints.sup' hendpoints
        (fun t => ‖partialValue t x‖ ^ p) ∂μ) ≤
      (L : ℝ) ^ (p - 1) *
        ∑ i ∈ blocks, ∫ x, ‖blockValue i x‖ ^ p ∂μ := by
  have hsum : Integrable
      (fun x => ∑ i ∈ blocks, ‖blockValue i x‖ ^ p) μ := by
    have hs : Integrable
        (∑ i ∈ blocks, fun x => ‖blockValue i x‖ ^ p) μ :=
      MeasureTheory.integrable_finsetSum' blocks hblock
    apply hs.congr
    filter_upwards [] with x
    simp only [Finset.sum_apply]
  have hrhs : Integrable
      (fun x => (L : ℝ) ^ (p - 1) *
        ∑ i ∈ blocks, ‖blockValue i x‖ ^ p) μ :=
    hsum.const_mul _
  calc
    (∫ x, endpoints.sup' hendpoints
        (fun t => ‖partialValue t x‖ ^ p) ∂μ) ≤
        ∫ x, (L : ℝ) ^ (p - 1) *
          ∑ i ∈ blocks, ‖blockValue i x‖ ^ p ∂μ := by
      apply MeasureTheory.integral_mono hmax hrhs
      intro x
      exact dyadic_finiteMax_pow_le endpoints hendpoints blocks pieces
        (fun i => blockValue i x) (fun t => partialValue t x)
        p L hp hpieces hcard (fun t => hdecomp t x)
    _ = (L : ℝ) ^ (p - 1) *
        ∫ x, ∑ i ∈ blocks, ‖blockValue i x‖ ^ p ∂μ := by
      rw [MeasureTheory.integral_const_mul]
    _ = (L : ℝ) ^ (p - 1) *
        ∑ i ∈ blocks, ∫ x, ‖blockValue i x‖ ^ p ∂μ := by
      congr 1
      exact MeasureTheory.integral_finsetSum blocks hblock

/-- Uniform-block version: if every interval block has `p`-moment at most
`B`, the maximal moment is bounded by
`L^(p-1) * (#blocks) * B`. -/
theorem integral_dyadic_finiteMax_pow_le_card_mul_momentBound
    {X τ ι E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    (μ : Measure X)
    (endpoints : Finset τ) (hendpoints : endpoints.Nonempty)
    (blocks : Finset ι) (pieces : τ → Finset ι)
    (blockValue : ι → X → E) (partialValue : τ → X → E)
    (p L : ℕ) (B : ℝ) (hp : 1 ≤ p)
    (hpieces : ∀ t, pieces t ⊆ blocks)
    (hcard : ∀ t, (pieces t).card ≤ L)
    (hdecomp : ∀ t x, partialValue t x =
      ∑ i ∈ pieces t, blockValue i x)
    (hblock : ∀ i ∈ blocks,
      Integrable (fun x => ‖blockValue i x‖ ^ p) μ)
    (hmax : Integrable (fun x =>
      endpoints.sup' hendpoints (fun t => ‖partialValue t x‖ ^ p)) μ)
    (hmoment : ∀ i ∈ blocks,
      (∫ x, ‖blockValue i x‖ ^ p ∂μ) ≤ B) :
    (∫ x, endpoints.sup' hendpoints
        (fun t => ‖partialValue t x‖ ^ p) ∂μ) ≤
      (L : ℝ) ^ (p - 1) * (blocks.card : ℝ) * B := by
  calc
    (∫ x, endpoints.sup' hendpoints
        (fun t => ‖partialValue t x‖ ^ p) ∂μ) ≤
        (L : ℝ) ^ (p - 1) *
          ∑ i ∈ blocks, ∫ x, ‖blockValue i x‖ ^ p ∂μ :=
      integral_dyadic_finiteMax_pow_le_sum_intervalMoments
        μ endpoints hendpoints blocks pieces blockValue partialValue p L hp
        hpieces hcard hdecomp hblock hmax
    _ ≤ (L : ℝ) ^ (p - 1) * ∑ _i ∈ blocks, B := by
      gcongr with i hi
      exact hmoment i hi
    _ = (L : ℝ) ^ (p - 1) * (blocks.card : ℝ) * B := by
      simp [mul_assoc]

/-- Concrete maximal-fibre consequence of `CriticalVMVT`, conditional only
on an explicit bounded block decomposition of the chosen partial sums.

The blocks themselves are the translated fixed-leading-coefficient Weyl
sums defined above.  Continuity and integrability of the block moments and
of the finite maximum are discharged internally.  The theorem's name and
hypotheses intentionally record the remaining combinatorial bridge: this is
not a claim that a particular dyadic grid has already been constructed. -/
theorem maximalTranslatedFixedFibre_criticalVMVT_bound_of_blockDecomposition
    (hVMVT : External.CriticalVMVT)
    (r : ℕ) (hr : 1 ≤ r) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {τ ι : Type*}
        (endpoints : Finset τ) (hendpoints : endpoints.Nonempty)
        (blocks : Finset ι) (pieces : τ → Finset ι)
        (blockStart : ι → ℤ) (blockLength : ι → ℕ)
        (N L : ℕ), 1 ≤ N →
        (∀ i ∈ blocks, 1 ≤ blockLength i) →
        (∀ i ∈ blocks, blockLength i ≤ N) →
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
          (L : ℝ) ^ (2 * External.criticalMoment r - 1) *
            (blocks.card : ℝ) * C *
              Real.rpow (N : ℝ)
                ((External.criticalMoment r : ℝ) + ε) := by
  obtain ⟨C, hC, hcritical⟩ := hVMVT r hr ε hε
  refine ⟨C, hC, ?_⟩
  intro τ ι endpoints hendpoints blocks pieces blockStart blockLength N L
    hN hlengthPos hlengthLe θ partialValue hpieces hcard hdecomp
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
    exact continuous_finsetSum (pieces t) fun i hi => hblockContinuous i
  have hblockIntegrable (i : ι) (hi : i ∈ blocks) :
      Integrable (fun β => ‖blockValue i β‖ ^ p) (torusHaar r) := by
    simpa [blockValue, translatedFixedLeadingFibreSum] using
      (integrable_norm_torusPolynomial_pow
        (translatedFixedLeadingWeight r (blockStart i) θ)
        (translatedMonomialFrequency r (blockStart i)) p)
  have hmaxContinuous : Continuous (fun β =>
      endpoints.sup' hendpoints (fun t => ‖partialValue t β‖ ^ p)) := by
    apply Continuous.finset_sup'_apply hendpoints
    intro t ht
    change Continuous ((fun β => ‖partialValue t β‖) ^ p)
    exact (hpartialContinuous t).norm.pow p
  have hmaxIntegrable : Integrable (fun β =>
      endpoints.sup' hendpoints (fun t => ‖partialValue t β‖ ^ p))
      (torusHaar r) := by
    simpa using
      hmaxContinuous.continuousOn.integrableOn_compact isCompact_univ
  have hmoment (i : ι) (hi : i ∈ blocks) :
      (∫ β, ‖blockValue i β‖ ^ p ∂torusHaar r) ≤
        C * Real.rpow (N : ℝ)
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
      _ ≤ C * Real.rpow (N : ℝ)
          ((External.criticalMoment r : ℝ) + ε) := by
        apply mul_le_mul_of_nonneg_left _ hC.le
        apply Real.rpow_le_rpow
        · positivity
        · exact_mod_cast hlengthLe i hi
        · positivity
  simpa only [p, blockValue, mul_assoc] using
    (integral_dyadic_finiteMax_pow_le_card_mul_momentBound
      (torusHaar r) endpoints hendpoints blocks pieces blockValue partialValue
      p L (C * Real.rpow (N : ℝ)
        ((External.criticalMoment r : ℝ) + ε)) hp
      hpieces hcard hdecomp hblockIntegrable hmaxIntegrable hmoment)

end ImprovedWeylBounds
