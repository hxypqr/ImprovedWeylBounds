import ImprovedWeylBounds.Approximation
import ImprovedWeylBounds.Translation
import ImprovedWeylBounds.TriangularExtraction

/-!
# From a translation-orbit collision to a primitive preliminary denominator

This file formalizes the internal argument in Lemma 5.4 of the manuscript.
The statement exposes two geometric hypotheses that the displayed statement
of that lemma inherits only implicitly from the preceding all-cuts lemma:

* the centres lie in the ambient interval, here used as `|y| \le N + 1`;
* they lie in one short block, here used as `k! |x-y| \le N`.

The first hypothesis controls the triangular conjugation by `T_{-y}`.  The
second is the precise bound needed to turn `k! |x-y|` into a denominator at
most `N`.  The last step divides this denominator and all tail numerators by
their common gcd and proves `External.TailPrimitive` rather than assuming it.
-/

open scoped BigOperators
open Polynomial

namespace ImprovedWeylBounds

noncomputable section

/-- The tail `(alpha_2, ..., alpha_k)` of a coefficient vector. -/
def tailCoefficients {k : ℕ} (alpha : CoefficientVector k) :
    Fin (k - 1) → ℝ :=
  fun c => alpha ⟨c.1 + 1, by omega⟩

/-- The polynomial with coefficient vector `alpha` and zero constant term. -/
def coefficientPolynomial {k : ℕ} (alpha : CoefficientVector k) : ℝ[X] :=
  ∑ j : Fin k, Polynomial.monomial (j.1 + 1) (alpha j)

@[simp]
theorem coeff_coefficientPolynomial {k : ℕ} (alpha : CoefficientVector k)
    (j : Fin k) :
    (coefficientPolynomial alpha).coeff (j.1 + 1) = alpha j := by
  classical
  change (Polynomial.lcoeff ℝ (j.1 + 1))
      (∑ i : Fin k, Polynomial.monomial (i.1 + 1) (alpha i)) = alpha j
  rw [map_sum]
  simp only [Polynomial.lcoeff_apply, Polynomial.coeff_monomial]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    split_ifs with h
    · exact (hij (Fin.ext (by omega))).elim
    · rfl
  · simp

theorem natDegree_coefficientPolynomial_le {k : ℕ}
    (alpha : CoefficientVector k) :
    (coefficientPolynomial alpha).natDegree ≤ k := by
  classical
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  exact (Polynomial.natDegree_monomial_le _).trans (by omega)

/-- The lower-coordinate centre of the integer translation orbit.  Coordinate
`r` is the coefficient of degree `r+1` in `P(X+x)`. -/
def translationCentre {k : ℕ} (alpha : CoefficientVector k) (x : ℤ)
    (r : Fin (k - 1)) : ℝ :=
  (translate x (coefficientPolynomial alpha)).coeff (r.1 + 1)

/-- The exact lower-coordinate difference before conjugation. -/
def centreDifference {k : ℕ} (alpha : CoefficientVector k) (x y : ℤ)
    (r : Fin (k - 1)) : ℝ :=
  translationCentre alpha x r - translationCentre alpha y r

/-- The centre difference in the backward (reflected) branch of the all-cuts
lemma. -/
def reflectedCentreDifference {k : ℕ} (alpha : CoefficientVector k)
    (x y : ℤ) (r : Fin (k - 1)) : ℝ :=
  (reflect (translate x (coefficientPolynomial alpha))).coeff (r.1 + 1) -
    (reflect (translate y (coefficientPolynomial alpha))).coeff (r.1 + 1)

@[simp]
theorem distToInt_neg (t : ℝ) : distToInt (-t) = distToInt t := by
  change ‖(-(t : UnitAddCircle))‖ = ‖(t : UnitAddCircle)‖
  exact norm_neg _

/-- Reflection is an integer diagonal isometry, so the backward and forward
centre differences have exactly the same mod-one distance. -/
theorem dist_reflectedCentreDifference_eq
    {k : ℕ} (alpha : CoefficientVector k) (x y : ℤ)
    (r : Fin (k - 1)) :
    distToInt (reflectedCentreDifference alpha x y r) =
      distToInt (centreDifference alpha x y r) := by
  rw [reflectedCentreDifference, coeff_reflect, coeff_reflect]
  have heq :
      (-1 : ℝ) ^ (r.1 + 1) *
          (translate x (coefficientPolynomial alpha)).coeff (r.1 + 1) -
        (-1 : ℝ) ^ (r.1 + 1) *
          (translate y (coefficientPolynomial alpha)).coeff (r.1 + 1) =
      (-1 : ℝ) ^ (r.1 + 1) * centreDifference alpha x y r := by
    simp only [centreDifference, translationCentre]
    ring
  rw [heq]
  rcases Nat.even_or_odd (r.1 + 1) with heven | hodd
  · rw [Even.neg_one_pow heven, one_mul]
  · rw [Odd.neg_one_pow hodd, neg_one_mul, distToInt_neg]

/-- A collision in the reflected branch can therefore be fed directly to the
forward-coordinate version used below. -/
theorem centre_collision_of_reflected_collision
    {k N : ℕ} (alpha : CoefficientVector k) (x y : ℤ) {delta : ℝ}
    (hcollision : ∀ r : Fin (k - 1),
      distToInt (reflectedCentreDifference alpha x y r) ≤
        delta * ((N : ℝ)⁻¹) ^ (r.1 + 1)) :
    ∀ r : Fin (k - 1),
      distToInt (centreDifference alpha x y r) ≤
        delta * ((N : ℝ)⁻¹) ^ (r.1 + 1) := by
  intro r
  rw [← dist_reflectedCentreDifference_eq alpha x y r]
  exact hcollision r

/-- The coefficient of degree `j` obtained by applying `T_{-y}` to the
lower-coordinate difference.  The leading coefficient does not occur because
integer translation leaves it fixed. -/
def conjugatedCentreDifference {k : ℕ} (alpha : CoefficientVector k)
    (x y : ℤ) (j : ℕ) : ℝ :=
  ∑ l ∈ Finset.Icc j (k - 1),
    (l.choose j : ℝ) *
      ((translate x (coefficientPolynomial alpha)).coeff l -
        (translate y (coefficientPolynomial alpha)).coeff l) *
      (-y : ℝ) ^ (l - j)

private theorem translated_difference_natDegree_le
    {k : ℕ} (alpha : CoefficientVector k) (x y : ℤ) :
    (translate x (coefficientPolynomial alpha) -
      translate y (coefficientPolynomial alpha)).natDegree ≤ k - 1 := by
  let P := coefficientPolynomial alpha
  have hP : P.natDegree ≤ k := natDegree_coefficientPolynomial_le alpha
  have hle : (translate x P - translate y P).natDegree ≤ k := by
    exact (Polynomial.natDegree_sub_le _ _).trans (by simpa [P] using hP)
  apply Polynomial.natDegree_le_pred hle
  have hx : (translate x P).coeff k = P.coeff k := by
    rw [coeff_translate_eq_sum_Icc x P k k hP]
    simp
  have hy : (translate y P).coeff k = P.coeff k := by
    rw [coeff_translate_eq_sum_Icc y P k k hP]
    simp
  simp [hx, hy]

/-- Applying `T_{-y}` to a difference of translated coefficient vectors is
exactly the relative translation `T_{x-y} alpha-alpha`. -/
theorem conjugatedCentreDifference_eq_relative_coeff
    {k : ℕ} (alpha : CoefficientVector k) (x y : ℤ)
    (j : ℕ) :
    conjugatedCentreDifference alpha x y j =
      (translate (x - y) (coefficientPolynomial alpha) -
        coefficientPolynomial alpha).coeff j := by
  let P := coefficientPolynomial alpha
  let D := translate x P - translate y P
  have hD : D.natDegree ≤ k - 1 :=
    translated_difference_natDegree_le alpha x y
  have hcoeff :
      (translate (-y) D).coeff j = conjugatedCentreDifference alpha x y j := by
    rw [coeff_translate_eq_sum_Icc (-y) D j (k - 1) hD]
    simp only [D, P, conjugatedCentreDifference, Polynomial.coeff_sub,
      Int.cast_neg]
  rw [← hcoeff]
  have hpoly : translate (-y) D = translate (x - y) P - P := by
    dsimp [D]
    have hmap :
        translate (-y) (translate x P - translate y P) =
          translate (-y) (translate x P) - translate (-y) (translate y P) := by
      simpa only [translate] using
        (LinearMap.map_sub (Polynomial.taylor ((-y : ℤ) : ℝ))
          (translate x P) (translate y P))
    rw [hmap]
    rw [translate_add, translate_add]
    have hxy : -y + x = x - y := by omega
    rw [hxy, neg_add_cancel, translate_zero]
  rw [hpoly]

/-- The relative coefficient is the triangular row used in Lemma 5.3. -/
theorem relative_coeff_eq_translationCollisionRow
    {k : ℕ} (alpha : CoefficientVector k) (h : ℤ)
    (r : Fin (k - 1)) :
    (translate h (coefficientPolynomial alpha) -
      coefficientPolynomial alpha).coeff (r.1 + 1) =
        translationCollisionRow h (tailCoefficients alpha) r := by
  let P := coefficientPolynomial alpha
  have hP : P.natDegree ≤ k := natDegree_coefficientPolynomial_le alpha
  rw [Polynomial.coeff_sub]
  rw [coeff_translate_eq_sum_Icc h P (r.1 + 1) k hP]
  rw [show P.coeff (r.1 + 1) = alpha ⟨r.1, by omega⟩ by
    simpa [P] using coeff_coefficientPolynomial alpha ⟨r.1, by omega⟩]
  classical
  have hsplit : Finset.Icc (r.1 + 1) k =
      insert (r.1 + 1) (Finset.Icc (r.1 + 2) k) := by
    ext l
    simp only [Finset.mem_Icc, Finset.mem_insert, Nat.succ_le_iff]
    omega
  rw [hsplit, Finset.sum_insert (by simp)]
  simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self, pow_zero,
    mul_one]
  rw [show P.coeff (r.1 + 1) = alpha ⟨r.1, by omega⟩ by
    simpa [P] using coeff_coefficientPolynomial alpha ⟨r.1, by omega⟩]
  rw [add_sub_cancel_left]
  rw [translationCollisionRow]
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun l hl =>
    ⟨l - 2, by
      simp only [Finset.mem_Icc] at hl
      omega⟩)
  · intro l hl
    simp only [Finset.mem_Icc] at hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  · intro l₁ hl₁ l₂ hl₂ heq
    simp only [Finset.mem_Icc] at hl₁ hl₂
    have heq' : l₁ - 2 = l₂ - 2 := congrArg Fin.val heq
    omega
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    refine ⟨c.1 + 2, ?_, ?_⟩
    · simp only [Finset.mem_Icc]
      omega
    · apply Fin.ext
      simp
  · intro l hl
    simp only [Finset.mem_Icc] at hl
    simp only [tailCoefficients]
    have hle : r.1 ≤ l - 2 := by omega
    have hcoeff : P.coeff l = alpha ⟨l - 1, by omega⟩ := by
      have hc := coeff_coefficientPolynomial alpha ⟨l - 1, by omega⟩
      rw [Nat.sub_add_cancel (by omega)] at hc
      simpa [P] using hc
    rw [hcoeff]
    have hdeg : l - 2 + 2 = l := by omega
    have hidx : l - 2 + 1 = l - 1 := by omega
    have hexp : l - 2 - r.1 + 1 = l - (r.1 + 1) := by omega
    have hfin : (⟨l - 1, by omega⟩ : Fin k) =
        ⟨l - 2 + 1, by omega⟩ := Fin.ext hidx.symm
    simp only [hdeg, hfin, hexp]

/-! ## Quantitative conjugation of a collision -/

/-- A rowwise amplification factor for conjugating by a translation whose
size is at most `N+1`. -/
def translationConjugationRowConstant (k j : ℕ) : ℝ :=
  ∑ l ∈ Finset.Icc j (k - 1), (l.choose j : ℝ) * (2 : ℝ) ^ (l - j)

/-- A single explicit constant which dominates every relevant row. -/
def translationConjugationConstant (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ico 1 k, translationConjugationRowConstant k j

theorem translationConjugationRowConstant_nonneg (k j : ℕ) :
    0 ≤ translationConjugationRowConstant k j := by
  exact Finset.sum_nonneg fun _ _ =>
    mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) _)

theorem translationConjugationConstant_nonneg (k : ℕ) :
    0 ≤ translationConjugationConstant k := by
  exact Finset.sum_nonneg fun j _ => translationConjugationRowConstant_nonneg k j

private theorem rowConstant_le_conjugationConstant
    {k j : ℕ} (hj : j ∈ Finset.Ico 1 k) :
    translationConjugationRowConstant k j ≤ translationConjugationConstant k := by
  rw [translationConjugationConstant]
  exact Finset.single_le_sum
    (fun i _ => translationConjugationRowConstant_nonneg k i) hj

/-- Distance to the integers is subadditive for a finite integer-linear
combination.  This is the exact elementary estimate used when `T_{-y}` is
applied to coordinate errors. -/
theorem distToInt_sum_int_mul_le {ι : Type*}
    (s : Finset ι) (a : ι → ℤ) (b : ι → ℝ) :
    distToInt (∑ i ∈ s, (a i : ℝ) * b i) ≤
      ∑ i ∈ s, |(a i : ℝ)| * distToInt (b i) := by
  classical
  let z : ℤ := ∑ i ∈ s, a i * round (b i)
  calc
    distToInt (∑ i ∈ s, (a i : ℝ) * b i) ≤
        |(∑ i ∈ s, (a i : ℝ) * b i) - (z : ℝ)| :=
      distToInt_le_abs_sub_int _ z
    _ = |∑ i ∈ s, (a i : ℝ) * (b i - (round (b i) : ℝ))| := by
      congr 1
      simp only [z]
      push_cast
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ i ∈ s, |(a i : ℝ) * (b i - (round (b i) : ℝ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ s, |(a i : ℝ)| * distToInt (b i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [abs_mul, distToInt_eq_abs_sub_round]

private theorem normalized_translation_power_bound
    {N j l : ℕ} (hN : 1 ≤ N) (hjl : j ≤ l) {y : ℤ}
    (hy : |(y : ℝ)| ≤ (N : ℝ) + 1) :
    |(y : ℝ)| ^ (l - j) * ((N : ℝ)⁻¹) ^ l ≤
      (2 : ℝ) ^ (l - j) * ((N : ℝ)⁻¹) ^ j := by
  have hNR : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hinv : 0 ≤ (N : ℝ)⁻¹ := inv_nonneg.mpr hNR.le
  have htwoN : (N : ℝ) + 1 ≤ 2 * (N : ℝ) := by
    have hNR1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hnormalized : |(y : ℝ)| * (N : ℝ)⁻¹ ≤ 2 := by
    calc
      |(y : ℝ)| * (N : ℝ)⁻¹ ≤ ((N : ℝ) + 1) * (N : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_right hy hinv
      _ ≤ (2 * (N : ℝ)) * (N : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_right htwoN hinv
      _ = 2 := by field_simp
  have hpows : (|(y : ℝ)| * (N : ℝ)⁻¹) ^ (l - j) ≤
      (2 : ℝ) ^ (l - j) :=
    pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) hinv) hnormalized _
  let d := l - j
  have hl : j + d = l := Nat.add_sub_of_le hjl
  have hfactor :
      |(y : ℝ)| ^ (l - j) * ((N : ℝ)⁻¹) ^ l =
        ((N : ℝ)⁻¹) ^ j *
          (|(y : ℝ)| * (N : ℝ)⁻¹) ^ (l - j) := by
    change |(y : ℝ)| ^ d * ((N : ℝ)⁻¹) ^ l =
      ((N : ℝ)⁻¹) ^ j * (|(y : ℝ)| * (N : ℝ)⁻¹) ^ d
    rw [← hl]
    rw [pow_add, mul_pow]
    ring
  rw [hfactor]
  calc
    ((N : ℝ)⁻¹) ^ j * (|(y : ℝ)| * (N : ℝ)⁻¹) ^ (l - j) ≤
        ((N : ℝ)⁻¹) ^ j * (2 : ℝ) ^ (l - j) :=
      mul_le_mul_of_nonneg_left hpows (pow_nonneg hinv _)
    _ = (2 : ℝ) ^ (l - j) * ((N : ℝ)⁻¹) ^ j := by ring

/-- A collision between two raw orbit centres remains a collision after
conjugation by `T_{-y}`, with an explicit degree-dependent loss.  The location
bound on `y` is exactly the hypothesis omitted from the displayed manuscript
statement and used in its proof. -/
theorem dist_conjugatedCentreDifference_le
    {k N : ℕ} (hN : 1 ≤ N) (alpha : CoefficientVector k) (x y : ℤ)
    {delta : ℝ} (hdelta : 0 ≤ delta)
    (hy : |(y : ℝ)| ≤ (N : ℝ) + 1)
    (hcollision : ∀ r : Fin (k - 1),
      distToInt (centreDifference alpha x y r) ≤
        delta * ((N : ℝ)⁻¹) ^ (r.1 + 1))
    (r : Fin (k - 1)) :
    distToInt (conjugatedCentreDifference alpha x y (r.1 + 1)) ≤
      translationConjugationConstant k * delta *
        ((N : ℝ)⁻¹) ^ (r.1 + 1) := by
  let s := Finset.Icc (r.1 + 1) (k - 1)
  let a : ℕ → ℤ := fun l => (l.choose (r.1 + 1) : ℤ) * (-y) ^ (l - (r.1 + 1))
  let b : ℕ → ℝ := fun l =>
    (translate x (coefficientPolynomial alpha)).coeff l -
      (translate y (coefficientPolynomial alpha)).coeff l
  have hstart : distToInt (conjugatedCentreDifference alpha x y (r.1 + 1)) ≤
      ∑ l ∈ s, |(a l : ℝ)| * distToInt (b l) := by
    have hlin := distToInt_sum_int_mul_le s a b
    apply le_trans ?_ hlin
    apply le_of_eq
    congr 1
    apply Finset.sum_congr rfl
    intro l hl
    simp only [a, b]
    push_cast
    simp only [s] at *
    ring
  refine hstart.trans ?_
  calc
    (∑ l ∈ s, |(a l : ℝ)| * distToInt (b l)) ≤
        ∑ l ∈ s,
          ((l.choose (r.1 + 1) : ℝ) * (2 : ℝ) ^ (l - (r.1 + 1))) *
            (delta * ((N : ℝ)⁻¹) ^ (r.1 + 1)) := by
      apply Finset.sum_le_sum
      intro l hl
      have hlmem : r.1 + 1 ≤ l ∧ l ≤ k - 1 := by
        simpa [s] using hl
      have hlfin : l - 1 < k - 1 := by omega
      let q : Fin (k - 1) := ⟨l - 1, hlfin⟩
      have hb : b l = centreDifference alpha x y q := by
        simp only [b, centreDifference, translationCentre, q]
        have hidx : l - 1 + 1 = l := Nat.sub_add_cancel (by omega)
        rw [hidx]
      have hdist : distToInt (b l) ≤
          delta * ((N : ℝ)⁻¹) ^ l := by
        rw [hb]
        have hc := hcollision q
        have hidx : q.1 + 1 = l := by
          simp only [q]
          omega
        simpa only [hidx] using hc
      have ha : |(a l : ℝ)| =
          (l.choose (r.1 + 1) : ℝ) * |(y : ℝ)| ^ (l - (r.1 + 1)) := by
        simp only [a]
        push_cast
        rw [abs_mul, abs_pow, abs_neg, abs_of_nonneg (Nat.cast_nonneg _)]
      rw [ha]
      calc
        ((l.choose (r.1 + 1) : ℝ) * |(y : ℝ)| ^ (l - (r.1 + 1))) *
            distToInt (b l) ≤
          ((l.choose (r.1 + 1) : ℝ) * |(y : ℝ)| ^ (l - (r.1 + 1))) *
            (delta * ((N : ℝ)⁻¹) ^ l) :=
          mul_le_mul_of_nonneg_left hdist
            (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (abs_nonneg _) _))
        _ = ((l.choose (r.1 + 1) : ℝ) * delta) *
            (|(y : ℝ)| ^ (l - (r.1 + 1)) * ((N : ℝ)⁻¹) ^ l) := by ring
        _ ≤ ((l.choose (r.1 + 1) : ℝ) * delta) *
            ((2 : ℝ) ^ (l - (r.1 + 1)) *
              ((N : ℝ)⁻¹) ^ (r.1 + 1)) := by
          apply mul_le_mul_of_nonneg_left
          · exact normalized_translation_power_bound hN hlmem.1 hy
          · exact mul_nonneg (Nat.cast_nonneg _) hdelta
        _ = ((l.choose (r.1 + 1) : ℝ) *
              (2 : ℝ) ^ (l - (r.1 + 1))) *
            (delta * ((N : ℝ)⁻¹) ^ (r.1 + 1)) := by ring
    _ = translationConjugationRowConstant k (r.1 + 1) *
          (delta * ((N : ℝ)⁻¹) ^ (r.1 + 1)) := by
      rw [translationConjugationRowConstant]
      simp only [s, Finset.sum_mul]
    _ ≤ translationConjugationConstant k *
          (delta * ((N : ℝ)⁻¹) ^ (r.1 + 1)) := by
      apply mul_le_mul_of_nonneg_right
      · apply rowConstant_le_conjugationConstant
        simp only [Finset.mem_Ico]
        omega
      · exact mul_nonneg hdelta (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) _)
    _ = translationConjugationConstant k * delta *
          ((N : ℝ)⁻¹) ^ (r.1 + 1) := by ring

/-- The orbit collision, after conjugation, is exactly the row hypothesis of
the triangular extraction lemma. -/
theorem dist_translationCollisionRow_of_centre_collision
    {k N : ℕ} (hN : 1 ≤ N) (alpha : CoefficientVector k) (x y : ℤ)
    {delta : ℝ} (hdelta : 0 ≤ delta)
    (hy : |(y : ℝ)| ≤ (N : ℝ) + 1)
    (hcollision : ∀ r : Fin (k - 1),
      distToInt (centreDifference alpha x y r) ≤
        delta * ((N : ℝ)⁻¹) ^ (r.1 + 1))
    (r : Fin (k - 1)) :
    distToInt (translationCollisionRow (x - y) (tailCoefficients alpha) r) ≤
      translationConjugationConstant k * delta *
        ((N : ℝ)⁻¹) ^ (r.1 + 1) := by
  rw [← relative_coeff_eq_translationCollisionRow alpha (x - y) r]
  rw [← conjugatedCentreDifference_eq_relative_coeff alpha x y (r.1 + 1)]
  exact dist_conjugatedCentreDifference_le hN alpha x y hdelta hy hcollision r

/-! ## Dividing by the common gcd -/

/-- The gcd of all tail numerators. -/
def tailNumeratorGCD {k : ℕ} (w : Fin (k - 1) → ℤ) : ℕ :=
  (Finset.univ : Finset (Fin (k - 1))).gcd fun c => (w c).natAbs

/-- The common gcd of a preliminary denominator and all its tail numerators. -/
def preliminaryCommonGCD {k : ℕ} (r0 : ℕ) (w : Fin (k - 1) → ℤ) : ℕ :=
  Nat.gcd r0 (tailNumeratorGCD w)

private theorem preliminaryCommonGCD_dvd_denominator
    {k r0 : ℕ} (w : Fin (k - 1) → ℤ) :
    preliminaryCommonGCD r0 w ∣ r0 := by
  exact Nat.gcd_dvd_left _ _

private theorem preliminaryCommonGCD_dvd_numerator
    {k r0 : ℕ} (w : Fin (k - 1) → ℤ) (c : Fin (k - 1)) :
    preliminaryCommonGCD r0 w ∣ (w c).natAbs := by
  exact (Nat.gcd_dvd_right _ _).trans
    (Finset.gcd_dvd (s := (Finset.univ : Finset (Fin (k - 1))))
      (f := fun i => (w i).natAbs) (Finset.mem_univ c))

/-- Pure arithmetic form of the final paragraph of Lemma 5.4: divide the
denominator and all tail numerators by their common gcd.  The errors cannot
increase, and the result satisfies the exact divisor-based predicate
`External.TailPrimitive`. -/
noncomputable def reduce_to_preliminaryApproximation
    {k N r0 : ℕ} (alpha : CoefficientVector k)
    (hr0 : 0 < r0) (hr0N : r0 ≤ N) (w : Fin (k - 1) → ℤ)
    (happrox : ∀ c : Fin (k - 1),
      |(r0 : ℝ) * alpha ⟨c.1 + 1, by omega⟩ - (w c : ℝ)| ≤
        Real.rpow (N : ℝ) (1 - ((c.1 + 2 : ℕ) : ℝ)) /
          (4 * (k : ℝ) ^ 4)) :
    {pre : PreliminaryApproximation k N alpha // pre.r ≤ N} := by
  let d := preliminaryCommonGCD r0 w
  have hd_r0 : d ∣ r0 := preliminaryCommonGCD_dvd_denominator w
  have hd_w (c : Fin (k - 1)) : d ∣ (w c).natAbs :=
    preliminaryCommonGCD_dvd_numerator w c
  have hdpos : 0 < d := by
    exact Nat.gcd_pos_of_pos_left (tailNumeratorGCD w) hr0
  let r := r0 / d
  let v : Fin k → ℤ := fun j =>
    if hj : 1 ≤ j.1 then
      w ⟨j.1 - 1, by omega⟩ / (d : ℤ)
    else 0
  have hfactor_r : d * r = r0 := by
    exact Nat.mul_div_cancel' hd_r0
  have hfactor_w (c : Fin (k - 1)) :
      (d : ℤ) * (w c / (d : ℤ)) = w c := by
    have hdwi : (d : ℤ) ∣ w c := Int.natCast_dvd.mpr (hd_w c)
    simpa [mul_comm] using Int.ediv_mul_cancel hdwi
  have hrpos : 0 < r := by
    exact Nat.div_pos (Nat.le_of_dvd hr0 hd_r0) hdpos
  refine ⟨
    { r := r
      r_pos := hrpos
      numerator := v
      primitive := ?_
      accurate := ?_ }, ?_⟩
  · intro e her hev
    have hde_r0 : d * e ∣ r0 := by
      rw [← hfactor_r]
      exact Nat.mul_dvd_mul_left d her
    have hde_w (c : Fin (k - 1)) : d * e ∣ (w c).natAbs := by
      let j : Fin k := ⟨c.1 + 1, by omega⟩
      have hej : e ∣ (v j).natAbs := hev j (by simp [j])
      have hdwi : (d : ℤ) ∣ w c := Int.natCast_dvd.mpr (hd_w c)
      have hnat : (w c / (d : ℤ)).natAbs = (w c).natAbs / d := by
        simpa using Int.natAbs_ediv_of_dvd hdwi
      have hvj : v j = w c / (d : ℤ) := by
        have hj : 1 ≤ j.1 := by simp [j]
        simp only [v, dif_pos hj]
        congr 1
      rw [hvj, hnat] at hej
      have hmul := Nat.mul_dvd_mul_left d hej
      rwa [Nat.mul_div_cancel' (hd_w c)] at hmul
    have hde_tail : d * e ∣ tailNumeratorGCD w := by
      apply Finset.dvd_gcd
      intro c _
      exact hde_w c
    have hde_d : d * e ∣ d := by
      change d * e ∣ Nat.gcd r0 (tailNumeratorGCD w)
      exact Nat.dvd_gcd hde_r0 hde_tail
    have hde_one : e ∣ 1 := by
      apply (Nat.mul_dvd_mul_iff_left hdpos).mp
      simpa using hde_d
    exact Nat.dvd_one.mp hde_one
  · intro j hj
    let c : Fin (k - 1) := ⟨j.1 - 1, by omega⟩
    have hvj : v j = w c / (d : ℤ) := by
      simp only [v, dif_pos hj]
      congr 1
    have hdwi : (d : ℤ) ∣ w c := Int.natCast_dvd.mpr (hd_w c)
    have hr_cast : (r0 : ℝ) = (d : ℝ) * (r : ℝ) := by
      exact_mod_cast hfactor_r.symm
    have hw_cast : (w c : ℝ) = (d : ℝ) * ((w c / (d : ℤ) : ℤ) : ℝ) := by
      exact_mod_cast (hfactor_w c).symm
    have hfactor :
        (r0 : ℝ) * alpha j - (w c : ℝ) =
          (d : ℝ) * ((r : ℝ) * alpha j - ((w c / (d : ℤ) : ℤ) : ℝ)) := by
      rw [hr_cast, hw_cast]
      ring
    have hnot_increase :
        |(r : ℝ) * alpha j - ((w c / (d : ℤ) : ℤ) : ℝ)| ≤
          |(r0 : ℝ) * alpha j - (w c : ℝ)| := by
      have hdabs : |(d : ℝ)| = (d : ℝ) := abs_of_nonneg (Nat.cast_nonneg d)
      rw [hfactor, abs_mul, hdabs]
      have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdpos
      nlinarith [abs_nonneg
        ((r : ℝ) * alpha j - ((w c / (d : ℤ) : ℤ) : ℝ))]
    rw [hvj]
    refine hnot_increase.trans ?_
    have hc := happrox c
    have hcidx : (⟨c.1 + 1, by omega⟩ : Fin k) = j := by
      apply Fin.ext
      simp only [c]
      omega
    have hexp : c.1 + 2 = j.1 + 1 := by
      simp only [c]
      omega
    simpa only [hcidx, hexp] using hc
  · exact (Nat.div_le_self r0 d).trans hr0N

private theorem inv_pow_eq_rpow_neg
    {N j : ℕ} :
    ((N : ℝ)⁻¹) ^ j = Real.rpow (N : ℝ) (-((j : ℕ) : ℝ)) := by
  calc
    ((N : ℝ)⁻¹) ^ j = ((N : ℝ) ^ j)⁻¹ := inv_pow _ _
    _ = (Real.rpow (N : ℝ) (j : ℝ))⁻¹ := by
      exact congrArg Inv.inv (Real.rpow_natCast (N : ℝ) j).symm
    _ = Real.rpow (N : ℝ) (-((j : ℕ) : ℝ)) :=
      (Real.rpow_neg (Nat.cast_nonneg N) (j : ℝ)).symm

/-- Lemma 5.4, with all hypotheses needed by its proof made explicit.

The first pair says that the two cut parameters really lie in `[0,N+1]`;
this is true for the construction in the all-cuts lemma but absent from its
displayed statement.  The short-block hypothesis is written in precisely the
integer form used below, `k! |x-y| \le N`.  The smallness condition records
the two explicit losses: conjugation of the collision and triangular
extraction.  The result includes the manuscript's `r \le N` as a subtype
property in addition to the `PreliminaryApproximation` record.
-/
theorem collision_to_preliminaryApproximation
    {k N : ℕ} (hk : 3 ≤ k) (hN : 1 ≤ N)
    (alpha : CoefficientVector k) (x y : ℤ) (hxy : x ≠ y)
    {delta : ℝ} (hdelta : 0 ≤ delta)
    (hlocation :
      (0 ≤ x ∧ x ≤ (N : ℤ) + 1) ∧
      (0 ≤ y ∧ y ≤ (N : ℤ) + 1))
    (hshortBlock : k.factorial * (x - y).natAbs ≤ N)
    (hcollision : ∀ r : Fin (k - 1),
      distToInt (centreDifference alpha x y r) ≤
        delta * ((N : ℝ)⁻¹) ^ (r.1 + 1))
    (hsmall :
      triangularExtractionConstant k *
          (translationConjugationConstant k * delta) ≤
        1 / (4 * (k : ℝ) ^ 4)) :
    Nonempty {pre : PreliminaryApproximation k N alpha // pre.r ≤ N} := by
  let h : ℤ := x - y
  have hh : h ≠ 0 := by
    intro hz
    apply hxy
    dsimp [h] at hz
    omega
  have hy : |(y : ℝ)| ≤ (N : ℝ) + 1 := by
    rw [abs_of_nonneg (by exact_mod_cast hlocation.2.1)]
    exact_mod_cast hlocation.2.2
  let eta : ℝ := translationConjugationConstant k * delta
  have heta : 0 ≤ eta :=
    mul_nonneg (translationConjugationConstant_nonneg k) hdelta
  have hrow : ∀ r : Fin (k - 1),
      distToInt (translationCollisionRow h (tailCoefficients alpha) r) ≤
        eta * ((N : ℝ)⁻¹) ^ (r.1 + 1) := by
    intro r
    simpa only [h, eta] using
      dist_translationCollisionRow_of_centre_collision
        hN alpha x y hdelta hy hcollision r
  have habs : |(h : ℝ)| = (h.natAbs : ℝ) := by
    cases h with
    | ofNat n => simp
    | negSucc n =>
        simp only [Int.cast_negSucc, Int.natAbs]
        rw [abs_neg, abs_of_nonneg]
        positivity
  have hhnat : 0 < h.natAbs := Int.natAbs_pos.mpr hh
  have hhlower : (1 : ℝ) ≤ |(h : ℝ)| := by
    rw [habs]
    exact_mod_cast hhnat
  have hhNatUpper : h.natAbs ≤ N := by
    exact (Nat.le_mul_of_pos_left h.natAbs (Nat.factorial_pos k)).trans
      hshortBlock
  have hhupper : |(h : ℝ)| ≤ (N : ℝ) := by
    rw [habs]
    exact_mod_cast hhNatUpper
  obtain ⟨w, hw⟩ :=
    triangular_extraction hk h N (tailCoefficients alpha) heta hhlower hhupper hrow
  let r0 : ℕ := k.factorial * h.natAbs
  let w0 : Fin (k - 1) → ℤ := fun c => h.sign * w c
  have hr0pos : 0 < r0 := Nat.mul_pos (Nat.factorial_pos k) hhnat
  have hr0N : r0 ≤ N := by simpa only [r0] using hshortBlock
  have hsign_mul : (h.sign : ℝ) * (h : ℝ) = (h.natAbs : ℝ) := by
    calc
      (h.sign : ℝ) * (h : ℝ) = ((h.sign * h : ℤ) : ℝ) := by push_cast; rfl
      _ = (((h.natAbs : ℕ) : ℤ) : ℝ) := by
        rw [Int.sign_mul_self_eq_natAbs]
      _ = (h.natAbs : ℝ) := by norm_num
  have hsign_abs : |(h.sign : ℝ)| = 1 := by
    rcases lt_or_gt_of_ne hh with hneg | hpos
    · rw [Int.sign_eq_neg_one_iff_neg.mpr hneg]
      norm_num
    · rw [Int.sign_eq_one_iff_pos.mpr hpos]
      norm_num
  have happ : ∀ c : Fin (k - 1),
      |(r0 : ℝ) * alpha ⟨c.1 + 1, by omega⟩ - (w0 c : ℝ)| ≤
        Real.rpow (N : ℝ) (1 - ((c.1 + 2 : ℕ) : ℝ)) /
          (4 * (k : ℝ) ^ 4) := by
    intro c
    have hsigned :
        |(r0 : ℝ) * alpha ⟨c.1 + 1, by omega⟩ - (w0 c : ℝ)| =
          |(k.factorial : ℝ) * (h : ℝ) * tailCoefficients alpha c -
            (w c : ℝ)| := by
      have hr0cast : (r0 : ℝ) =
          (k.factorial : ℝ) * (h.natAbs : ℝ) := by
        simp only [r0, Nat.cast_mul, Nat.cast_factorial]
      have heq :
          (r0 : ℝ) * alpha ⟨c.1 + 1, by omega⟩ - (w0 c : ℝ) =
            (h.sign : ℝ) *
              ((k.factorial : ℝ) * (h : ℝ) * tailCoefficients alpha c -
                (w c : ℝ)) := by
        simp only [w0, Int.cast_mul, tailCoefficients]
        rw [hr0cast, ← hsign_mul]
        ring
      rw [heq, abs_mul, hsign_abs, one_mul]
    rw [hsigned]
    refine (hw c).trans ?_
    have hpowNonneg : 0 ≤ ((N : ℝ)⁻¹) ^ (c.1 + 1) :=
      pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N)) _
    have hscaled :
        triangularExtractionConstant k * eta *
            ((N : ℝ)⁻¹) ^ (c.1 + 1) ≤
          (1 / (4 * (k : ℝ) ^ 4)) *
            ((N : ℝ)⁻¹) ^ (c.1 + 1) := by
      apply mul_le_mul_of_nonneg_right
      · simpa only [eta] using hsmall
      · exact hpowNonneg
    refine hscaled.trans_eq ?_
    have hexp :
        1 - ((c.1 + 2 : ℕ) : ℝ) = -((c.1 + 1 : ℕ) : ℝ) := by
      push_cast
      ring
    rw [hexp, ← inv_pow_eq_rpow_neg]
    ring
  exact ⟨reduce_to_preliminaryApproximation alpha hr0pos hr0N w0 happ⟩

/-- Backward/reflected branch of Lemma 5.4.  It is a direct corollary because
reflection changes each lower coordinate only by a sign. -/
theorem reflected_collision_to_preliminaryApproximation
    {k N : ℕ} (hk : 3 ≤ k) (hN : 1 ≤ N)
    (alpha : CoefficientVector k) (x y : ℤ) (hxy : x ≠ y)
    {delta : ℝ} (hdelta : 0 ≤ delta)
    (hlocation :
      (0 ≤ x ∧ x ≤ (N : ℤ) + 1) ∧
      (0 ≤ y ∧ y ≤ (N : ℤ) + 1))
    (hshortBlock : k.factorial * (x - y).natAbs ≤ N)
    (hcollision : ∀ r : Fin (k - 1),
      distToInt (reflectedCentreDifference alpha x y r) ≤
        delta * ((N : ℝ)⁻¹) ^ (r.1 + 1))
    (hsmall :
      triangularExtractionConstant k *
          (translationConjugationConstant k * delta) ≤
        1 / (4 * (k : ℝ) ^ 4)) :
    Nonempty {pre : PreliminaryApproximation k N alpha // pre.r ≤ N} := by
  apply collision_to_preliminaryApproximation hk hN alpha x y hxy hdelta
    hlocation hshortBlock
  · exact centre_collision_of_reflected_collision alpha x y hcollision
  · exact hsmall

end

end ImprovedWeylBounds
