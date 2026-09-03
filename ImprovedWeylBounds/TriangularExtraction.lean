import ImprovedWeylBounds.Basic

/-!
# Extraction from a triangular translation system

This file formalizes the elementary linear algebra in Lemma 5.3 of the
paper.  The first result is deliberately stated for an arbitrary integral
square matrix: rounding its rows and multiplying by the adjugate produces
simultaneous integral approximants.  The remainder of the file specializes
this construction to the binomial upper-triangular matrix occurring in the
translation action.
-/

open scoped BigOperators

namespace ImprovedWeylBounds

noncomputable section

/-- The real matrix obtained by casting an integral matrix entrywise. -/
abbrev intMatrixToReal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (Int.castRingHom ℝ).mapMatrix A

/-- Adjugate extraction after choosing the nearest integer in every row.

No nonsingularity hypothesis is needed: the identity
`adj(A) A = det(A) I` is valid over `ℤ`, including when `det(A)=0`.
-/
theorem exists_adjugate_integer_approximation
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℝ)
    (err : Fin n → ℝ)
    (hrow : ∀ i, distToInt ((intMatrixToReal A).mulVec x i) ≤ err i) :
    ∃ v : Fin n → ℤ, ∀ c,
      |(A.det : ℝ) * x c - (v c : ℝ)| ≤
        ∑ i, |(A.adjugate c i : ℝ)| * err i := by
  let z : Fin n → ℤ := fun i => round ((intMatrixToReal A).mulVec x i)
  let v : Fin n → ℤ := A.adjugate.mulVec z
  refine ⟨v, fun c => ?_⟩
  have hcastAdj : intMatrixToReal A.adjugate = (intMatrixToReal A).adjugate :=
    (Int.castRingHom ℝ).map_adjugate A
  have hcastAdj_apply (r s : Fin n) :
      (intMatrixToReal A).adjugate r s = (A.adjugate r s : ℝ) := by
    rw [← hcastAdj]
    rfl
  have hcastDet : ((A.det : ℤ) : ℝ) = (intMatrixToReal A).det := by
    simpa [intMatrixToReal] using (Int.castRingHom ℝ).map_det A
  have hmain :
      (A.det : ℝ) * x c - (v c : ℝ) =
        ∑ i, (A.adjugate c i : ℝ) *
          ((intMatrixToReal A).mulVec x i - (z i : ℝ)) := by
    have hadj := congr_fun
      (Matrix.mulVec_mulVec x (intMatrixToReal A).adjugate (intMatrixToReal A)) c
    rw [Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec] at hadj
    change (intMatrixToReal A).adjugate.mulVec
      ((intMatrixToReal A).mulVec x) c = (intMatrixToReal A).det * x c at hadj
    have hvcast : (v c : ℝ) =
        (intMatrixToReal A).adjugate.mulVec (fun i => (z i : ℝ)) c := by
      simp only [v, Matrix.mulVec, dotProduct]
      push_cast
      apply Finset.sum_congr rfl
      intro i _
      rw [hcastAdj_apply]
    rw [hcastDet]
    rw [← hadj, hvcast]
    simp only [Matrix.mulVec, dotProduct]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hcastAdj_apply]
    ring
  rw [hmain]
  calc
    |∑ i, (A.adjugate c i : ℝ) *
          ((intMatrixToReal A).mulVec x i - (z i : ℝ))| ≤
        ∑ i, |(A.adjugate c i : ℝ) *
          ((intMatrixToReal A).mulVec x i - (z i : ℝ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |(A.adjugate c i : ℝ)| *
          |(intMatrixToReal A).mulVec x i - (z i : ℝ)| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [abs_mul]
    _ ≤ ∑ i, |(A.adjugate c i : ℝ)| * err i := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      simpa [z, distToInt_eq_abs_sub_round] using hrow i

/-! ## The translation matrix -/

/-- The matrix `A_h` from Lemma 5.3.  Index `r : Fin (k-1)` represents the
paper index `j=r+1`, while index `c` represents the coefficient
`x_c=h α_{c+2}`. -/
def triangularTranslationMatrix (k : ℕ) (h : ℤ) :
    Matrix (Fin (k - 1)) (Fin (k - 1)) ℤ :=
  fun r c =>
    if r.1 ≤ c.1 then
      ((c.1 + 2).choose (r.1 + 1) : ℤ) * h ^ (c.1 - r.1)
    else 0

/-- `A_h` is upper triangular (in the usual row/column ordering). -/
theorem triangularTranslationMatrix_blockTriangular (k : ℕ) (h : ℤ) :
    (triangularTranslationMatrix k h).BlockTriangular id := by
  intro r c hcr
  have hnot : ¬r.1 ≤ c.1 := by
    exact Nat.not_le.mpr (by simpa using hcr)
  simp [triangularTranslationMatrix, hnot]

/-- Its diagonal entries, in zero-based notation, are `2,3,...,k`. -/
@[simp]
theorem triangularTranslationMatrix_diag (k : ℕ) (h : ℤ)
    (i : Fin (k - 1)) :
    triangularTranslationMatrix k h i i = (i.1 + 2 : ℤ) := by
  simp [triangularTranslationMatrix, Nat.choose_succ_self_right]
  omega

private theorem prod_range_add_two (n : ℕ) :
    ∏ i ∈ Finset.range n, (i + 2) = (n + 1).factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        ∏ i ∈ Finset.range (n + 1), (i + 2) =
            (∏ i ∈ Finset.range n, (i + 2)) * (n + 2) := by
              rw [Finset.prod_range_succ]
        _ = (n + 1).factorial * (n + 2) := by rw [ih]
        _ = (n + 2).factorial := by
          rw [mul_comm]
          simpa [Nat.add_assoc] using (Nat.factorial_succ (n + 1)).symm

/-- The exact determinant identity used in Lemma 5.3. -/
theorem det_triangularTranslationMatrix {k : ℕ} (hk : 1 ≤ k) (h : ℤ) :
    (triangularTranslationMatrix k h).det = (k.factorial : ℤ) := by
  rw [Matrix.det_of_upperTriangular
    (triangularTranslationMatrix_blockTriangular k h)]
  simp_rw [triangularTranslationMatrix_diag]
  have hp : (∏ i : Fin (k - 1), (i.1 + 2)) = k.factorial := by
    calc
      (∏ i : Fin (k - 1), (i.1 + 2)) =
          ∏ i ∈ Finset.range (k - 1), (i + 2) :=
        Fin.prod_univ_eq_prod_range (fun i => i + 2) (k - 1)
      _ = (k - 1 + 1).factorial := prod_range_add_two (k - 1)
      _ = k.factorial := by congr 2; omega
  exact_mod_cast hp

/-- Over the integers the adjugate of a nonsingular upper-triangular matrix
is again upper triangular.  We prove this by passing faithfully to `ℚ`, where
the inverse exists, and then use `A⁻¹ = det(A)⁻¹ adj(A)`. -/
private theorem adjugate_blockTriangular_int
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : A.BlockTriangular id) (hdet : A.det ≠ 0) :
    A.adjugate.BlockTriangular id := by
  let AQ : Matrix (Fin n) (Fin n) ℚ :=
    (Int.castRingHom ℚ).mapMatrix A
  have hAQ : AQ.BlockTriangular id := by
    intro r c hcr
    simp [AQ, hA hcr]
  have hdetQ : AQ.det ≠ 0 := by
    rw [← (Int.castRingHom ℚ).map_det A]
    change (A.det : ℚ) ≠ 0
    exact_mod_cast hdet
  letI : Invertible AQ :=
    Matrix.invertibleOfIsUnitDet AQ (isUnit_iff_ne_zero.mpr hdetQ)
  have hinv : AQ⁻¹.BlockTriangular id :=
    Matrix.blockTriangular_inv_of_blockTriangular hAQ
  intro r c hcr
  have hz := hinv hcr
  rw [Matrix.inv_def] at hz
  simp only [Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv] at hz
  have hadjQ : AQ.adjugate r c = (A.adjugate r c : ℚ) := by
    rw [← (Int.castRingHom ℚ).map_adjugate A]
    rfl
  rw [hadjQ] at hz
  have hentryQ : (A.adjugate r c : ℚ) = 0 :=
    (mul_eq_zero.mp hz).resolve_left (inv_ne_zero hdetQ)
  exact_mod_cast hentryQ

/-- The adjugate of the paper matrix has no entries below the diagonal. -/
theorem adjugate_triangularTranslationMatrix_blockTriangular
    {k : ℕ} (hk : 1 ≤ k) (h : ℤ) :
    (triangularTranslationMatrix k h).adjugate.BlockTriangular id := by
  apply adjugate_blockTriangular_int _
    (triangularTranslationMatrix_blockTriangular k h)
  rw [det_triangularTranslationMatrix hk h]
  exact_mod_cast k.factorial_ne_zero

/-- The diagonal scaling matrix `D_h=diag(h,h²,...,h^(k-1))`. -/
def translationScaleMatrix (k : ℕ) (h : ℤ) :
    Matrix (Fin (k - 1)) (Fin (k - 1)) ℤ :=
  Matrix.diagonal fun i => h ^ (i.1 + 1)

/-- A division-free form of `A_h=D_h⁻¹ A_1 D_h`.  This identity remains
valid at `h=0`; for the paper we later use it with `h ≠ 0`. -/
theorem scale_mul_triangularTranslationMatrix (k : ℕ) (h : ℤ) :
    translationScaleMatrix k h * triangularTranslationMatrix k h =
      triangularTranslationMatrix k 1 * translationScaleMatrix k h := by
  ext r c
  simp only [translationScaleMatrix, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hrc : r.1 ≤ c.1
  · simp only [triangularTranslationMatrix, hrc, if_pos, one_pow]
    have hexp : r.1 + 1 + (c.1 - r.1) = c.1 + 1 := by omega
    calc
      h ^ (r.1 + 1) * (((c.1 + 2).choose (r.1 + 1) : ℤ) *
          h ^ (c.1 - r.1)) =
          ((c.1 + 2).choose (r.1 + 1) : ℤ) *
            (h ^ (r.1 + 1) * h ^ (c.1 - r.1)) := by ring
      _ = ((c.1 + 2).choose (r.1 + 1) : ℤ) * h ^ (c.1 + 1) := by
        rw [← pow_add, hexp]
      _ = ((c.1 + 2).choose (r.1 + 1) : ℤ) * 1 * h ^ (c.1 + 1) := by
        ring
  · simp [triangularTranslationMatrix, hrc]

/-- The exponent of `h` in the `i`th diagonal entry of `adj(D_h)`. -/
def scaleAdjugateExponent {k : ℕ} (i : Fin (k - 1)) : ℕ :=
  ∑ t ∈ Finset.univ.erase i, (t.1 + 1)

@[simp]
theorem adjugate_translationScaleMatrix_apply {k : ℕ} (h : ℤ)
    (i j : Fin (k - 1)) :
    (translationScaleMatrix k h).adjugate i j =
      if i = j then h ^ scaleAdjugateExponent i else 0 := by
  rw [translationScaleMatrix, Matrix.adjugate_diagonal]
  simp only [Matrix.diagonal_apply]
  split_ifs with hij
  · subst j
    rw [Finset.prod_pow_eq_pow_sum]
    rfl
  · rfl

private theorem scaleAdjugateExponent_add_sub
    {k : ℕ} {c j : Fin (k - 1)} (hcj : c.1 ≤ j.1) :
    scaleAdjugateExponent c =
      scaleAdjugateExponent j + (j.1 - c.1) := by
  let S : ℕ := ∑ t : Fin (k - 1), (t.1 + 1)
  have hc_mem : c ∈ (Finset.univ : Finset (Fin (k - 1))) := Finset.mem_univ c
  have hj_mem : j ∈ (Finset.univ : Finset (Fin (k - 1))) := Finset.mem_univ j
  have hc_sum : scaleAdjugateExponent c + (c.1 + 1) = S := by
    simpa [scaleAdjugateExponent, S, add_comm] using
      (Finset.sum_erase_add _ (fun t : Fin (k - 1) => t.1 + 1) hc_mem)
  have hj_sum : scaleAdjugateExponent j + (j.1 + 1) = S := by
    simpa [scaleAdjugateExponent, S, add_comm] using
      (Finset.sum_erase_add _ (fun t : Fin (k - 1) => t.1 + 1) hj_mem)
  omega

/-- Exact scaling of the nonzero adjugate entries.  This is the formal
counterpart of `adj(A_h)_{c,j}=O_k(|h|^(j-c))`; in fact the coefficient is
exactly the corresponding entry at `h=1`. -/
theorem adjugate_triangularTranslationMatrix_scaling
    {k : ℕ} {h : ℤ} (hh : h ≠ 0)
    {c j : Fin (k - 1)} (hcj : c.1 ≤ j.1) :
    (triangularTranslationMatrix k h).adjugate c j =
      h ^ (j.1 - c.1) *
        (triangularTranslationMatrix k 1).adjugate c j := by
  have hmat := congrArg Matrix.adjugate
    (scale_mul_triangularTranslationMatrix k h)
  rw [Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib] at hmat
  have hscale : (translationScaleMatrix k h).adjugate =
      Matrix.diagonal (fun i => h ^ scaleAdjugateExponent i) := by
    ext r s
    simp [adjugate_translationScaleMatrix_apply, Matrix.diagonal_apply]
  rw [hscale] at hmat
  have hentry := congr_fun (congr_fun hmat c) j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at hentry
  have hexp := scaleAdjugateExponent_add_sub hcj
  apply mul_right_cancel₀ (pow_ne_zero _ hh)
  calc
    (triangularTranslationMatrix k h).adjugate c j *
        h ^ scaleAdjugateExponent j =
      h ^ scaleAdjugateExponent c *
        (triangularTranslationMatrix k 1).adjugate c j := hentry
    _ = (h ^ (j.1 - c.1) *
          (triangularTranslationMatrix k 1).adjugate c j) *
        h ^ scaleAdjugateExponent j := by
      rw [hexp, pow_add]
      ring

/-- A completely explicit, computable constant depending only on the degree.
It is the sum of the absolute values of all entries of `adj(A_1)`. -/
def triangularExtractionConstant (k : ℕ) : ℝ :=
  ∑ c : Fin (k - 1), ∑ j : Fin (k - 1),
    |((triangularTranslationMatrix k 1).adjugate c j : ℝ)|

theorem triangularExtractionConstant_nonneg (k : ℕ) :
    0 ≤ triangularExtractionConstant k := by
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

private theorem adjugate_one_row_sum_le_constant
    {k : ℕ} (c : Fin (k - 1)) :
    (∑ j : Fin (k - 1),
        |((triangularTranslationMatrix k 1).adjugate c j : ℝ)|) ≤
      triangularExtractionConstant k := by
  rw [triangularExtractionConstant]
  exact Finset.single_le_sum
    (s := (Finset.univ : Finset (Fin (k - 1))))
    (f := fun i => ∑ j : Fin (k - 1),
      |((triangularTranslationMatrix k 1).adjugate i j : ℝ)|)
    (fun i _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
    (Finset.mem_univ c)

/-- Quantitative adjugate growth, including the exact triangular support. -/
theorem abs_adjugate_triangularTranslationMatrix_le
    {k : ℕ} (hk : 1 ≤ k) {h : ℤ} (hh : h ≠ 0)
    (c j : Fin (k - 1)) :
    |((triangularTranslationMatrix k h).adjugate c j : ℝ)| ≤
      triangularExtractionConstant k * |(h : ℝ)| ^ (j.1 - c.1) := by
  by_cases hcj : c.1 ≤ j.1
  · rw [adjugate_triangularTranslationMatrix_scaling hh hcj]
    push_cast
    rw [abs_mul, abs_pow]
    have hcoeff :
        |((triangularTranslationMatrix k 1).adjugate c j : ℝ)| ≤
          triangularExtractionConstant k :=
      (Finset.single_le_sum
      (fun i _ => abs_nonneg ((triangularTranslationMatrix k 1).adjugate c i : ℝ))
      (Finset.mem_univ j)).trans (adjugate_one_row_sum_le_constant c)
    calc
      |(h : ℝ)| ^ (j.1 - c.1) *
          |((triangularTranslationMatrix k 1).adjugate c j : ℝ)| =
        |((triangularTranslationMatrix k 1).adjugate c j : ℝ)| *
          |(h : ℝ)| ^ (j.1 - c.1) := mul_comm _ _
      _ ≤ triangularExtractionConstant k * |(h : ℝ)| ^ (j.1 - c.1) :=
        mul_le_mul_of_nonneg_right hcoeff (pow_nonneg (abs_nonneg _) _)
  · have hjc : j < c := by omega
    rw [adjugate_triangularTranslationMatrix_blockTriangular hk h hjc]
    simp only [Int.cast_zero, abs_zero]
    exact mul_nonneg (triangularExtractionConstant_nonneg k)
      (pow_nonneg (abs_nonneg _) _)

private theorem adjugate_scaled_error_term_le
    {k : ℕ} (hk : 1 ≤ k) {h : ℤ} (hh : h ≠ 0)
    {η scale : ℝ} (hη : 0 ≤ η) (hscale0 : 0 ≤ scale)
    (hunit : |(h : ℝ)| * scale ≤ 1)
    (c j : Fin (k - 1)) :
    |((triangularTranslationMatrix k h).adjugate c j : ℝ)| *
        (η * scale ^ (j.1 + 1)) ≤
      |((triangularTranslationMatrix k 1).adjugate c j : ℝ)| *
        (η * scale ^ (c.1 + 1)) := by
  by_cases hcj : c.1 ≤ j.1
  · rw [adjugate_triangularTranslationMatrix_scaling hh hcj]
    push_cast
    rw [abs_mul, abs_pow]
    let d := j.1 - c.1
    have hexp : j.1 + 1 = c.1 + 1 + d := by
      dsimp [d]
      omega
    have hfactor :
        |(h : ℝ)| ^ d * scale ^ (j.1 + 1) =
          scale ^ (c.1 + 1) * (|(h : ℝ)| * scale) ^ d := by
      rw [hexp, pow_add, mul_pow]
      ring
    have hpow : (|(h : ℝ)| * scale) ^ d ≤ 1 :=
      pow_le_one₀ (mul_nonneg (abs_nonneg _) hscale0) hunit
    have hbase :
        0 ≤ |((triangularTranslationMatrix k 1).adjugate c j : ℝ)| *
          η * scale ^ (c.1 + 1) := by positivity
    calc
      (|(h : ℝ)| ^ d *
          |((triangularTranslationMatrix k 1).adjugate c j : ℝ)|) *
          (η * scale ^ (j.1 + 1)) =
          (|((triangularTranslationMatrix k 1).adjugate c j : ℝ)| *
            η * scale ^ (c.1 + 1)) *
          (|(h : ℝ)| * scale) ^ d := by
            calc
              (|(h : ℝ)| ^ d *
                  |((triangularTranslationMatrix k 1).adjugate c j : ℝ)|) *
                  (η * scale ^ (j.1 + 1)) =
                |((triangularTranslationMatrix k 1).adjugate c j : ℝ)| * η *
                  (|(h : ℝ)| ^ d * scale ^ (j.1 + 1)) := by ring
              _ = |((triangularTranslationMatrix k 1).adjugate c j : ℝ)| * η *
                  (scale ^ (c.1 + 1) * (|(h : ℝ)| * scale) ^ d) := by
                    rw [hfactor]
              _ = (|((triangularTranslationMatrix k 1).adjugate c j : ℝ)| *
                    η * scale ^ (c.1 + 1)) *
                  (|(h : ℝ)| * scale) ^ d := by ring
      _ ≤ (|((triangularTranslationMatrix k 1).adjugate c j : ℝ)| *
            η * scale ^ (c.1 + 1)) * 1 :=
        mul_le_mul_of_nonneg_left hpow hbase
      _ = |((triangularTranslationMatrix k 1).adjugate c j : ℝ)| *
          (η * scale ^ (c.1 + 1)) := by ring
  · have hjc : j < c := by omega
    rw [adjugate_triangularTranslationMatrix_blockTriangular hk h hjc]
    rw [adjugate_triangularTranslationMatrix_blockTriangular hk 1 hjc]
    norm_num

/-- Matrix form of Lemma 5.3.  The parameter `scale` is `N⁻¹`; consequently
`scale^(c+1)` is the paper's `N^(1-ℓ)` for `ℓ=c+2`.

The lower bound `1 ≤ |h|` in the paper is used here only through `h ≠ 0`,
while `|h| ≤ N` is exactly the normalized condition `|h| * scale ≤ 1`.
-/
theorem triangular_extraction_matrix
    {k : ℕ} (hk : 3 ≤ k) {h : ℤ} (hh : h ≠ 0)
    (α : Fin (k - 1) → ℝ) {η scale : ℝ}
    (hη : 0 ≤ η) (hscale0 : 0 ≤ scale)
    (hunit : |(h : ℝ)| * scale ≤ 1)
    (hrow : ∀ r,
      distToInt ((intMatrixToReal (triangularTranslationMatrix k h)).mulVec
        (fun c => (h : ℝ) * α c) r) ≤ η * scale ^ (r.1 + 1)) :
    ∃ v : Fin (k - 1) → ℤ, ∀ c,
      |(k.factorial : ℝ) * (h : ℝ) * α c - (v c : ℝ)| ≤
        triangularExtractionConstant k * η * scale ^ (c.1 + 1) := by
  obtain ⟨v, hv⟩ := exists_adjugate_integer_approximation
    (triangularTranslationMatrix k h) (fun c => (h : ℝ) * α c)
    (fun r => η * scale ^ (r.1 + 1)) hrow
  refine ⟨v, fun c => ?_⟩
  have hdet :
      ((triangularTranslationMatrix k h).det : ℝ) = (k.factorial : ℝ) := by
    rw [det_triangularTranslationMatrix (by omega) h]
    norm_cast
  rw [hdet] at hv
  calc
    |(k.factorial : ℝ) * (h : ℝ) * α c - (v c : ℝ)| =
        |(k.factorial : ℝ) * ((h : ℝ) * α c) - (v c : ℝ)| := by ring_nf
    _ ≤ ∑ j, |((triangularTranslationMatrix k h).adjugate c j : ℝ)| *
          (η * scale ^ (j.1 + 1)) := hv c
    _ ≤ ∑ j, |((triangularTranslationMatrix k 1).adjugate c j : ℝ)| *
          (η * scale ^ (c.1 + 1)) := by
      exact Finset.sum_le_sum fun j _ =>
        adjugate_scaled_error_term_le (by omega) hh hη hscale0 hunit c j
    _ = (∑ j, |((triangularTranslationMatrix k 1).adjugate c j : ℝ)|) *
          (η * scale ^ (c.1 + 1)) := by
      rw [Finset.sum_mul]
    _ ≤ triangularExtractionConstant k *
          (η * scale ^ (c.1 + 1)) := by
      exact mul_le_mul_of_nonneg_right (adjugate_one_row_sum_le_constant c)
        (mul_nonneg hη (pow_nonneg hscale0 _))
    _ = triangularExtractionConstant k * η * scale ^ (c.1 + 1) := by ring

/-! ## The paper statement -/

/-- The `j=r+1` expression in the hypothesis of Lemma 5.3, with
`α c` denoting the paper coefficient `α_(c+2)`.

Thus the summand indexed by `c` is
`choose (c+2) (r+1) * α_(c+2) * h^((c+2)-(r+1))`, and indices with
`c<r` are omitted.
-/
def translationCollisionRow {k : ℕ} (h : ℤ)
    (α : Fin (k - 1) → ℝ) (r : Fin (k - 1)) : ℝ :=
  ∑ c : Fin (k - 1),
    if r.1 ≤ c.1 then
      ((c.1 + 2).choose (r.1 + 1) : ℝ) * α c *
        (h : ℝ) ^ (c.1 - r.1 + 1)
    else 0

/-- Multiplication by `A_h` after putting `x_c=h α_(c+1)` is exactly the
translated-coefficient expression in the paper. -/
theorem triangularTranslationMatrix_mulVec_coefficients
    {k : ℕ} (h : ℤ) (α : Fin (k - 1) → ℝ) (r : Fin (k - 1)) :
    (intMatrixToReal (triangularTranslationMatrix k h)).mulVec
        (fun c => (h : ℝ) * α c) r =
      translationCollisionRow h α r := by
  simp only [Matrix.mulVec, dotProduct, translationCollisionRow]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hrc : r.1 ≤ c.1
  · simp only [intMatrixToReal, triangularTranslationMatrix, hrc, if_pos,
      RingHom.mapMatrix_apply, Matrix.map_apply]
    change (((((c.1 + 2).choose (r.1 + 1) : ℤ) *
        h ^ (c.1 - r.1) : ℤ) : ℝ) * ((h : ℝ) * α c)) = _
    push_cast
    rw [pow_succ]
    ring
  · simp [intMatrixToReal, triangularTranslationMatrix, hrc]

/-- Lemma 5.3 with the scale written as powers of `N⁻¹`.  Coordinate `c`
stands for the paper's `ℓ=c+2`, so the exponent `c+1` is `ℓ-1` and the
right side is exactly `C(k) η N^(1-ℓ)`.
-/
theorem triangular_extraction
    {k : ℕ} (hk : 3 ≤ k) (h : ℤ) (N : ℕ)
    (α : Fin (k - 1) → ℝ) {η : ℝ}
    (hη : 0 ≤ η)
    (hh_lower : (1 : ℝ) ≤ |(h : ℝ)|)
    (hh_upper : |(h : ℝ)| ≤ (N : ℝ))
    (hrow : ∀ r,
      distToInt (translationCollisionRow h α r) ≤
        η * ((N : ℝ)⁻¹) ^ (r.1 + 1)) :
    ∃ v : Fin (k - 1) → ℤ, ∀ c,
      |(k.factorial : ℝ) * (h : ℝ) * α c - (v c : ℝ)| ≤
        triangularExtractionConstant k * η *
          ((N : ℝ)⁻¹) ^ (c.1 + 1) := by
  have hh : h ≠ 0 := by
    intro hh
    subst h
    norm_num at hh_lower
  have hN : 0 < (N : ℝ) :=
    lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hh_lower) hh_upper
  have hscale0 : 0 ≤ (N : ℝ)⁻¹ := inv_nonneg.mpr hN.le
  have hunit : |(h : ℝ)| * (N : ℝ)⁻¹ ≤ 1 := by
    calc
      |(h : ℝ)| * (N : ℝ)⁻¹ ≤ (N : ℝ) * (N : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_right hh_upper hscale0
      _ = 1 := by field_simp
  apply triangular_extraction_matrix hk hh α hη hscale0 hunit
  intro r
  rw [triangularTranslationMatrix_mulVec_coefficients]
  exact hrow r

private theorem inv_pow_succ_eq_zpow_one_sub (x : ℝ) (n : ℕ) :
    x⁻¹ ^ (n + 1) = x ^ (1 - ((n + 2 : ℕ) : ℤ)) := by
  calc
    x⁻¹ ^ (n + 1) = (x ^ (n + 1))⁻¹ := inv_pow x (n + 1)
    _ = x ^ (-((n + 1 : ℕ) : ℤ)) := by
      simpa only [zpow_natCast] using (zpow_neg x ((n + 1 : ℕ) : ℤ)).symm
    _ = x ^ (1 - ((n + 2 : ℕ) : ℤ)) := by
      congr 1

/-- Lemma 5.3 in literal `N^(1-ℓ)` notation.  Here `c` denotes
`ℓ=c+2`, and likewise row `r` denotes `j=r+1`. -/
theorem triangular_extraction_zpow
    {k : ℕ} (hk : 3 ≤ k) (h : ℤ) (N : ℕ)
    (α : Fin (k - 1) → ℝ) {η : ℝ}
    (hη : 0 ≤ η)
    (hh_lower : (1 : ℝ) ≤ |(h : ℝ)|)
    (hh_upper : |(h : ℝ)| ≤ (N : ℝ))
    (hrow : ∀ r,
      distToInt (translationCollisionRow h α r) ≤
        η * (N : ℝ) ^ (1 - ((r.1 + 2 : ℕ) : ℤ))) :
    ∃ v : Fin (k - 1) → ℤ, ∀ c,
      |(k.factorial : ℝ) * (h : ℝ) * α c - (v c : ℝ)| ≤
        triangularExtractionConstant k * η *
          (N : ℝ) ^ (1 - ((c.1 + 2 : ℕ) : ℤ)) := by
  have hrow' : ∀ r,
      distToInt (translationCollisionRow h α r) ≤
        η * ((N : ℝ)⁻¹) ^ (r.1 + 1) := by
    intro r
    rw [inv_pow_succ_eq_zpow_one_sub]
    exact hrow r
  obtain ⟨v, hv⟩ := triangular_extraction hk h N α hη hh_lower hh_upper hrow'
  refine ⟨v, fun c => ?_⟩
  rw [← inv_pow_succ_eq_zpow_one_sub]
  exact hv c

end

end ImprovedWeylBounds
