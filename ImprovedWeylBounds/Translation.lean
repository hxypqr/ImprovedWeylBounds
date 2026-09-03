import ImprovedWeylBounds.Basic

/-!
# Translation and reflection of real polynomials

The definitions here retain the constant coefficient.  Thus `translate m P`
is literally `P(X + m)`.  This makes composition an honest group action on
`ℝ[X]`; the paper's action on nonconstant coefficients is recovered by
discarding coefficient zero.
-/

open Polynomial

namespace ImprovedWeylBounds

/-- Translate a real polynomial by an integer: `translate m P = P(X + m)`. -/
noncomputable def translate (m : ℤ) (P : ℝ[X]) : ℝ[X] :=
  Polynomial.taylor (m : ℝ) P

/-- Reflect a real polynomial: `reflect P = P(-X)`. -/
noncomputable def reflect (P : ℝ[X]) : ℝ[X] :=
  P.comp (-X)

@[simp]
theorem translate_zero (P : ℝ[X]) : translate 0 P = P := by
  simp [translate]

/-- Integer translations form an additive action. -/
theorem translate_add (m n : ℤ) (P : ℝ[X]) :
    translate m (translate n P) = translate (m + n) P := by
  simpa [translate] using
    (Polynomial.taylor_taylor P (m : ℝ) (n : ℝ))

@[simp]
theorem translate_neg_left (m : ℤ) (P : ℝ[X]) :
    translate (-m) (translate m P) = P := by
  rw [translate_add, neg_add_cancel, translate_zero]

@[simp]
theorem translate_neg_right (m : ℤ) (P : ℝ[X]) :
    translate m (translate (-m) P) = P := by
  rw [translate_add, add_neg_cancel, translate_zero]

/-- Evaluation of a translated polynomial is evaluation at the translated point. -/
@[simp]
theorem eval_translate (m : ℤ) (P : ℝ[X]) (x : ℝ) :
    (translate m P).eval x = P.eval (x + m) := by
  exact Polynomial.taylor_eval (m : ℝ) P x

@[simp]
theorem eval_zero_translate (m : ℤ) (P : ℝ[X]) :
    (translate m P).eval 0 = P.eval (m : ℝ) := by
  simp

/-- The coefficient formula in its canonical Hasse-derivative form. -/
theorem coeff_translate (m : ℤ) (P : ℝ[X]) (j : ℕ) :
    (translate m P).coeff j = (Polynomial.hasseDeriv j P).eval (m : ℝ) := by
  exact Polynomial.taylor_coeff (m : ℝ) P j

/-- Explicit binomial coefficient formula for translation. -/
theorem coeff_translate_eq_sum (m : ℤ) (P : ℝ[X]) (j : ℕ) :
    (translate m P).coeff j =
      P.sum fun l a => (l.choose j : ℝ) * a * (m : ℝ) ^ (l - j) := by
  rw [coeff_translate, Polynomial.hasseDeriv_apply, Polynomial.eval_sum]
  simp only [Polynomial.eval_monomial]

/-- The finite-range form of the translation formula.  If `P` has degree at
most `k`, this is exactly
`[X^j] P(X+m) = ∑_{l=0}^k binom(l,j) [X^l]P · m^(l-j)`. -/
theorem coeff_translate_eq_sum_range (m : ℤ) (P : ℝ[X]) (j k : ℕ)
    (hP : P.natDegree ≤ k) :
    (translate m P).coeff j =
      ∑ l ∈ Finset.range (k + 1),
        (l.choose j : ℝ) * P.coeff l * (m : ℝ) ^ (l - j) := by
  rw [coeff_translate_eq_sum]
  rw [P.sum_over_range'
    (fun l => by simp)
    (k + 1)
    (Nat.lt_succ_of_le hP)]

/-- The translation formula with precisely the paper's index range `j ≤ l ≤ k`. -/
theorem coeff_translate_eq_sum_Icc (m : ℤ) (P : ℝ[X]) (j k : ℕ)
    (hP : P.natDegree ≤ k) :
    (translate m P).coeff j =
      ∑ l ∈ Finset.Icc j k,
        (l.choose j : ℝ) * P.coeff l * (m : ℝ) ^ (l - j) := by
  rw [coeff_translate_eq_sum_range m P j k hP]
  symm
  apply Finset.sum_subset
  · intro l hl
    rw [Finset.mem_Icc] at hl
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le hl.2
  · intro l hlrange hlIcc
    have hlt : l < j := by
      rw [Finset.mem_range] at hlrange
      have hnot : ¬(j ≤ l ∧ l ≤ k) := by
        simpa only [Finset.mem_Icc] using hlIcc
      exact Nat.lt_of_not_ge fun hjl => hnot ⟨hjl, Nat.le_of_lt_succ hlrange⟩
    simp [Nat.choose_eq_zero_of_lt hlt]

/-- Translation preserves the degree. -/
@[simp]
theorem natDegree_translate (m : ℤ) (P : ℝ[X]) :
    (translate m P).natDegree = P.natDegree := by
  exact Polynomial.natDegree_taylor P (m : ℝ)

/-- Translation preserves the leading coefficient. -/
@[simp]
theorem leadingCoeff_translate (m : ℤ) (P : ℝ[X]) :
    (translate m P).leadingCoeff = P.leadingCoeff := by
  exact Polynomial.leadingCoeff_taylor (m : ℝ) P

/-- Reflection evaluates the original polynomial at the negative point. -/
@[simp]
theorem eval_reflect (P : ℝ[X]) (x : ℝ) :
    (reflect P).eval x = P.eval (-x) := by
  simp [reflect, Polynomial.eval_comp]

/-- Reflection is an involution. -/
@[simp]
theorem reflect_reflect (P : ℝ[X]) : reflect (reflect P) = P := by
  exact Polynomial.comp_neg_X_comp_neg_X P

/-- Reflection multiplies the degree-`j` coefficient by `(-1)^j`. -/
theorem coeff_reflect (P : ℝ[X]) (j : ℕ) :
    (reflect P).coeff j = (-1 : ℝ) ^ j * P.coeff j := by
  simpa [reflect, mul_comm] using
    (Polynomial.comp_C_mul_X_coeff (p := P) (r := (-1 : ℝ)) (n := j))

/-- Reflecting after translation gives the phase `P(m-X)`. -/
@[simp]
theorem eval_reflect_translate (m : ℤ) (P : ℝ[X]) (x : ℝ) :
    (reflect (translate m P)).eval x = P.eval ((m : ℝ) - x) := by
  simp [sub_eq_add_neg, add_comm]

/-- The dihedral relation between reflection and translation. -/
theorem reflect_translate (m : ℤ) (P : ℝ[X]) :
    reflect (translate m P) = translate (-m) (reflect P) := by
  apply Polynomial.funext
  intro x
  simp [add_comm]

/-- Reflection preserves degree, although it changes an odd leading
coefficient's sign. -/
@[simp]
theorem natDegree_reflect (P : ℝ[X]) :
    (reflect P).natDegree = P.natDegree := by
  by_cases hP : P = 0
  · simp [hP, reflect]
  unfold reflect
  rw [Polynomial.natDegree_comp_eq_of_mul_ne_zero (p := P) (q := -X)]
  · simp
  · simp [hP]

@[simp]
theorem leadingCoeff_reflect (P : ℝ[X]) :
    (reflect P).leadingCoeff =
      (-1 : ℝ) ^ P.natDegree * P.leadingCoeff := by
  exact Polynomial.comp_neg_X_leadingCoeff_eq P

end ImprovedWeylBounds
