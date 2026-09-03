import ImprovedWeylBounds.Basic
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# A finite de la Vallée Poussin reproducing kernel

This file replaces the appeal to a smooth cutoff and Poisson summation in
`main.tex`, Lemma 4.1 (lines 739--759), by the elementary kernel
`V_L = 2 F_{2L} - F_L`, where `F_Q` is the Fejér kernel.  All sums below are
finite.  In particular, no form of Poisson summation is taken as an external
input.
-/

open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace ImprovedWeylBounds
namespace ReproducingKernel

/-- The geometric polynomial `1 + e(x) + ... + e((Q-1)x)` on `ℝ / ℤ`. -/
noncomputable def geometricPolynomial (Q : ℕ) (x : UnitAddCircle) : ℂ :=
  ∑ m ∈ Finset.range Q, fourier (m : ℤ) x

/-- The Fejér kernel, normalized to have integral one when `Q > 0`. -/
noncomputable def fejerKernel (Q : ℕ) (x : UnitAddCircle) : ℂ :=
  ((‖geometricPolynomial Q x‖ ^ 2 / (Q : ℝ) : ℝ) : ℂ)

/-- The de la Vallée Poussin kernel `2 F_{2L} - F_L`. -/
noncomputable def vallPoussinKernel (L : ℕ) (x : UnitAddCircle) : ℂ :=
  2 * fejerKernel (2 * L) x - fejerKernel L x

lemma continuous_geometricPolynomial (Q : ℕ) :
    Continuous (geometricPolynomial Q) := by
  unfold geometricPolynomial
  fun_prop

lemma continuous_fejerKernel (Q : ℕ) : Continuous (fejerKernel Q) := by
  unfold fejerKernel
  exact Complex.continuous_ofReal.comp
    (((continuous_norm.comp (continuous_geometricPolynomial Q)).pow 2).div_const _)

lemma continuous_vallPoussinKernel (L : ℕ) : Continuous (vallPoussinKernel L) := by
  unfold vallPoussinKernel
  exact (continuous_const.mul (continuous_fejerKernel (2 * L))).sub
    (continuous_fejerKernel L)

lemma norm_geometricPolynomial_le (Q : ℕ) (x : UnitAddCircle) :
    ‖geometricPolynomial Q x‖ ≤ Q := by
  rw [geometricPolynomial]
  calc
    ‖∑ m ∈ Finset.range Q, fourier (m : ℤ) x‖
        ≤ ∑ m ∈ Finset.range Q, ‖fourier (m : ℤ) x‖ := norm_sum_le _ _
    _ = Q := by simp [fourier_apply]

lemma fejerKernel_nonneg (Q : ℕ) (x : UnitAddCircle) :
    0 ≤ (fejerKernel Q x).re := by
  simp only [fejerKernel, Complex.ofReal_re]
  positivity

lemma norm_fejerKernel_le (Q : ℕ) (hQ : 0 < Q) (x : UnitAddCircle) :
    ‖fejerKernel Q x‖ ≤ Q := by
  rw [fejerKernel, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h := norm_geometricPolynomial_le Q x
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  rw [div_le_iff₀ hQr]
  nlinarith [mul_self_le_mul_self (norm_nonneg (geometricPolynomial Q x)) h]

lemma norm_vallPoussinKernel_le (L : ℕ) (hL : 0 < L) (x : UnitAddCircle) :
    ‖vallPoussinKernel L x‖ ≤ 5 * L := by
  rw [vallPoussinKernel]
  calc
    ‖2 * fejerKernel (2 * L) x - fejerKernel L x‖
        ≤ ‖2 * fejerKernel (2 * L) x‖ + ‖fejerKernel L x‖ := norm_sub_le _ _
    _ = 2 * ‖fejerKernel (2 * L) x‖ + ‖fejerKernel L x‖ := by norm_num
    _ ≤ 2 * (2 * L) + L := by
      gcongr
      · simpa only [Nat.cast_mul, Nat.cast_ofNat] using
          norm_fejerKernel_le (2 * L) (by omega) x
      · exact norm_fejerKernel_le L hL x
    _ = 5 * L := by ring

/-- Orthogonality of the circle characters evaluates the square integral of
the geometric polynomial. -/
lemma integral_norm_sq_geometricPolynomial (Q : ℕ) :
    ∫ x : UnitAddCircle, ‖geometricPolynomial Q x‖ ^ 2
        ∂AddCircle.haarAddCircle = (Q : ℝ) := by
  let P : C(UnitAddCircle, ℂ) :=
    ∑ m ∈ Finset.range Q, fourier (m : ℤ)
  have hP (x : UnitAddCircle) : P x = geometricPolynomial Q x := by
    classical
    change (∑ m ∈ Finset.range Q, fourier (m : ℤ)) x =
      ∑ m ∈ Finset.range Q, fourier (m : ℤ) x
    induction Finset.range Q using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih => simp [Finset.sum_insert, ha, ih]
  have htoLp :
      P.toLp 2 AddCircle.haarAddCircle ℂ =
        ∑ m ∈ Finset.range Q, fourierLp 2 (m : ℤ) := by
    simp only [P, map_sum, fourierLp]
  have hinner :
      inner ℂ (P.toLp 2 AddCircle.haarAddCircle ℂ)
          (P.toLp 2 AddCircle.haarAddCircle ℂ) = (Q : ℂ) := by
    rw [htoLp]
    have horth :
        Orthonormal ℂ
          (fun m : ℕ => fourierLp (T := (1 : ℝ)) 2 (m : ℤ)) := by
      simpa only [Function.comp_def] using
        (orthonormal_fourier (T := (1 : ℝ))).comp (fun m : ℕ => (m : ℤ))
          Int.ofNat_injective
    simpa using
      horth.inner_sum (fun _ : ℕ => (1 : ℂ)) (fun _ : ℕ => (1 : ℂ)) (Finset.range Q)
  have hint :
      (∫ x : UnitAddCircle, ((‖P x‖ ^ 2 : ℝ) : ℂ)
          ∂AddCircle.haarAddCircle) = (Q : ℂ) := by
    rw [← hinner, ContinuousMap.inner_toLp]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [Complex.mul_conj']
    simp only [hP]
    norm_cast
  have hcast :
      ((∫ x : UnitAddCircle, ‖geometricPolynomial Q x‖ ^ 2
          ∂AddCircle.haarAddCircle : ℝ) : ℂ) = ((Q : ℝ) : ℂ) := by
    calc
      ((∫ x : UnitAddCircle, ‖geometricPolynomial Q x‖ ^ 2
          ∂AddCircle.haarAddCircle : ℝ) : ℂ) =
          ∫ x : UnitAddCircle, ((‖geometricPolynomial Q x‖ ^ 2 : ℝ) : ℂ)
            ∂AddCircle.haarAddCircle := integral_ofReal.symm
      _ = (Q : ℂ) := by simpa only [hP] using hint
      _ = ((Q : ℝ) : ℂ) := by norm_cast
  exact Complex.ofReal_injective hcast

/-- The Fejér kernel has `L¹` norm one. -/
lemma integral_norm_fejerKernel (Q : ℕ) (hQ : 0 < Q) :
    ∫ x : UnitAddCircle, ‖fejerKernel Q x‖ ∂AddCircle.haarAddCircle = 1 := by
  have hQr : (Q : ℝ) ≠ 0 := by positivity
  simp_rw [fejerKernel, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ ‖geometricPolynomial Q _‖ ^ 2 / (Q : ℝ))]
  rw [integral_div, integral_norm_sq_geometricPolynomial, div_self hQr]

/-- Consequently the de la Vallée Poussin kernel has a uniform `L¹` bound. -/
lemma integral_norm_vallPoussinKernel_le_three (L : ℕ) (hL : 0 < L) :
    ∫ x : UnitAddCircle, ‖vallPoussinKernel L x‖
        ∂AddCircle.haarAddCircle ≤ 3 := by
  have hpoint (x : UnitAddCircle) :
      ‖vallPoussinKernel L x‖ ≤
        2 * ‖fejerKernel (2 * L) x‖ + ‖fejerKernel L x‖ := by
    rw [vallPoussinKernel]
    calc
      ‖2 * fejerKernel (2 * L) x - fejerKernel L x‖
          ≤ ‖2 * fejerKernel (2 * L) x‖ + ‖fejerKernel L x‖ := norm_sub_le _ _
      _ = 2 * ‖fejerKernel (2 * L) x‖ + ‖fejerKernel L x‖ := by norm_num
  have hFi (Q : ℕ) :
      Integrable (fun x : UnitAddCircle => ‖fejerKernel Q x‖)
        AddCircle.haarAddCircle :=
    (continuous_fejerKernel Q).norm.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    ∫ x : UnitAddCircle, ‖vallPoussinKernel L x‖ ∂AddCircle.haarAddCircle
        ≤ ∫ x : UnitAddCircle,
            (2 * ‖fejerKernel (2 * L) x‖ + ‖fejerKernel L x‖)
              ∂AddCircle.haarAddCircle := integral_mono_of_nonneg
                (ae_of_all _ fun x => norm_nonneg (vallPoussinKernel L x))
                ((hFi (2 * L)).const_mul 2 |>.add (hFi L)) (ae_of_all _ hpoint)
    _ = 2 * 1 + 1 := by
      rw [integral_add, integral_const_mul, integral_norm_fejerKernel (2 * L) (by omega),
        integral_norm_fejerKernel L hL]
      · exact (hFi (2 * L)).const_mul 2
      · exact hFi L
    _ = 3 := by norm_num

/-- The square definition of the Fejér kernel expands into a finite double
Fourier sum.  This is the only algebra behind its Fourier multiplier. -/
lemma fejerKernel_eq_double_sum (Q : ℕ) (x : UnitAddCircle) :
    fejerKernel Q x =
      (1 / (Q : ℂ)) *
        ∑ a ∈ Finset.range Q, ∑ b ∈ Finset.range Q,
          fourier ((a : ℤ) - (b : ℤ)) x := by
  rw [fejerKernel]
  have hsquare :
      (((‖geometricPolynomial Q x‖ ^ 2 : ℝ) : ℂ)) =
        geometricPolynomial Q x * conj (geometricPolynomial Q x) := by
    rw [Complex.mul_conj']
    norm_cast
  have hcast :
      (((‖geometricPolynomial Q x‖ ^ 2 / (Q : ℝ) : ℝ) : ℂ)) =
        (((‖geometricPolynomial Q x‖ ^ 2 : ℝ) : ℂ) / (Q : ℂ)) := by
    norm_cast
  rw [hcast, hsquare, geometricPolynomial, map_sum]
  rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro b hb
  rw [← fourier_neg, ← fourier_add]
  congr 1
  ring_nf

/-- Integral of one circle character against normalized Haar measure. -/
lemma integral_fourier (n : ℤ) :
    ∫ x : UnitAddCircle, fourier n x ∂AddCircle.haarAddCircle =
      if n = 0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := (1 : ℝ)) n) 0
  simpa [fourierCoeff, Pi.single_apply, eq_comm] using h

/-- Fourier coefficient of a Fejér kernel, expressed as the number of pairs
of indices with the prescribed difference. -/
lemma fourierCoeff_fejerKernel (Q : ℕ) (n : ℤ) :
    fourierCoeff (T := (1 : ℝ)) (fejerKernel Q) n =
      (1 / (Q : ℂ)) *
        ∑ a ∈ Finset.range Q, ∑ b ∈ Finset.range Q,
          if (a : ℤ) - (b : ℤ) = n then 1 else 0 := by
  unfold fourierCoeff
  simp_rw [fejerKernel_eq_double_sum, smul_eq_mul]
  simp_rw [show ∀ (t : UnitAddCircle),
      fourier (-n) t *
          ((1 / (Q : ℂ)) *
            ∑ a ∈ Finset.range Q, ∑ b ∈ Finset.range Q,
              fourier ((a : ℤ) - (b : ℤ)) t) =
        (1 / (Q : ℂ)) *
          (fourier (-n) t *
            ∑ a ∈ Finset.range Q, ∑ b ∈ Finset.range Q,
              fourier ((a : ℤ) - (b : ℤ)) t) by
    intro t
    ring]
  rw [integral_const_mul]
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [integral_finsetSum]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      have hcombine :
          (∫ x : UnitAddCircle,
              fourier (-n) x * fourier ((a : ℤ) - (b : ℤ)) x
                ∂AddCircle.haarAddCircle) =
            ∫ x : UnitAddCircle,
              fourier (-n + ((a : ℤ) - (b : ℤ))) x
                ∂AddCircle.haarAddCircle := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [fourier_add]
      rw [hcombine, integral_fourier]
      have heq :
          -n + ((a : ℤ) - (b : ℤ)) = 0 ↔ (a : ℤ) - (b : ℤ) = n := by
        omega
      simp only [heq]
    · intro b hb
      exact ((map_continuous (fourier (-n))).mul
        (map_continuous (fourier ((a : ℤ) - (b : ℤ))))).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
  · intro a ha
    apply Continuous.integrable_of_hasCompactSupport
    · fun_prop
    · exact HasCompactSupport.of_compactSpace _

/-- Pairs of indices contributing to the `n`-th Fejér multiplier. -/
abbrev DifferencePairs (Q : ℕ) (n : ℤ) :=
  {ab : Fin Q × Fin Q // (ab.1.val : ℤ) - (ab.2.val : ℤ) = n}

/-- For a nonnegative difference `n`, a pair is uniquely determined by its
second entry. -/
def differencePairsEquivFinOfNonneg (Q : ℕ) (n : ℤ) (hn : 0 ≤ n) :
    DifferencePairs Q n ≃ Fin (Q - n.toNat) where
  toFun ab := ⟨ab.1.2.val, by
    have hab := ab.2
    have ha := ab.1.1.isLt
    have hncast : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn
    omega⟩
  invFun b :=
    ⟨(⟨b.val + n.toNat, by omega⟩, ⟨b.val, by omega⟩), by
      have hncast : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn
      push_cast
      omega⟩
  left_inv ab := by
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      change ab.val.2.val + n.toNat = ab.val.1.val
      have hab := ab.2
      have hncast : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn
      omega
    · rfl
  right_inv b := by
    apply Fin.ext
    rfl

/-- For a negative difference `n`, a pair is uniquely determined by its
first entry. -/
def differencePairsEquivFinOfNeg (Q : ℕ) (n : ℤ) (hn : n < 0) :
    DifferencePairs Q n ≃ Fin (Q - (-n).toNat) where
  toFun ab := ⟨ab.1.1.val, by
    have hab := ab.2
    have hb := ab.1.2.isLt
    have hncast : ((-n).toNat : ℤ) = -n := Int.toNat_of_nonneg (by omega)
    omega⟩
  invFun a :=
    ⟨(⟨a.val, by omega⟩, ⟨a.val + (-n).toNat, by omega⟩), by
      have hncast : ((-n).toNat : ℤ) = -n := Int.toNat_of_nonneg (by omega)
      push_cast
      omega⟩
  left_inv ab := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Fin.ext
      change ab.val.1.val + (-n).toNat = ab.val.2.val
      have hab := ab.2
      have hncast : ((-n).toNat : ℤ) = -n := Int.toNat_of_nonneg (by omega)
      omega
  right_inv a := by
    apply Fin.ext
    rfl

lemma card_differencePairs (Q : ℕ) (n : ℤ) :
    Fintype.card (DifferencePairs Q n) = Q - n.natAbs := by
  rcases lt_or_ge n 0 with hn | hn
  · rw [Fintype.card_congr (differencePairsEquivFinOfNeg Q n hn)]
    simp only [Fintype.card_fin]
    congr 1
    omega
  · rw [Fintype.card_congr (differencePairsEquivFinOfNonneg Q n hn)]
    simp only [Fintype.card_fin]
    congr 1
    omega

lemma double_sum_indicator_eq_card (Q : ℕ) (n : ℤ) :
    (∑ a ∈ Finset.range Q, ∑ b ∈ Finset.range Q,
        if (a : ℤ) - (b : ℤ) = n then (1 : ℂ) else 0) =
      (Fintype.card (DifferencePairs Q n) : ℂ) := by
  classical
  rw [← Fin.sum_univ_eq_sum_range]
  simp_rw [← Fin.sum_univ_eq_sum_range]
  rw [← Finset.sum_product']
  rw [Finset.univ_product_univ]
  simpa [Fintype.card_subtype] using
    (Finset.sum_boole (R := ℂ)
      (fun ab : Fin Q × Fin Q => (ab.1.val : ℤ) - (ab.2.val : ℤ) = n)
      Finset.univ)

/-- Exact Fejér multiplier, in the form most convenient for arithmetic.  The
natural subtraction is deliberately truncated; hence this formula also says
that the multiplier vanishes outside `[-Q,Q]`. -/
lemma fourierCoeff_fejerKernel_eq_card (Q : ℕ) (n : ℤ) :
    fourierCoeff (T := (1 : ℝ)) (fejerKernel Q) n =
      (1 / (Q : ℂ)) * (Q - n.natAbs : ℕ) := by
  rw [fourierCoeff_fejerKernel, double_sum_indicator_eq_card,
    card_differencePairs]

/-- On the frequency box needed below, the de la Vallée Poussin multiplier is
identically one. -/
lemma fourierCoeff_vallPoussinKernel_eq_one (L : ℕ) (hL : 0 < L) (n : ℤ)
    (hn : n.natAbs ≤ L) :
    fourierCoeff (T := (1 : ℝ)) (vallPoussinKernel L) n = 1 := by
  have hFi (Q : ℕ) :
      Integrable (fejerKernel Q) AddCircle.haarAddCircle :=
    (continuous_fejerKernel Q).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hlinear :
      fourierCoeff (T := (1 : ℝ)) (vallPoussinKernel L) n =
        2 * fourierCoeff (T := (1 : ℝ)) (fejerKernel (2 * L)) n -
          fourierCoeff (T := (1 : ℝ)) (fejerKernel L) n := by
    have hadd := congrFun
      (fourierCoeff.add
        ((hFi (2 * L)).const_mul 2)
        ((hFi L).const_mul (-1))) n
    change fourierCoeff (T := (1 : ℝ))
        (fun x => 2 * fejerKernel (2 * L) x + (-1) * fejerKernel L x) n =
      fourierCoeff (T := (1 : ℝ)) (fun x => 2 * fejerKernel (2 * L) x) n +
        fourierCoeff (T := (1 : ℝ)) (fun x => (-1) * fejerKernel L x) n at hadd
    rw [fourierCoeff.const_mul, fourierCoeff.const_mul] at hadd
    change fourierCoeff (T := (1 : ℝ))
        (fun x => 2 * fejerKernel (2 * L) x - fejerKernel L x) n = _
    simpa only [sub_eq_add_neg, neg_one_mul] using hadd
  rw [hlinear, fourierCoeff_fejerKernel_eq_card,
    fourierCoeff_fejerKernel_eq_card]
  have h2L : n.natAbs ≤ 2 * L := by omega
  have hLr : (L : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hL)
  have h2Lr : ((2 * L : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.mul_ne_zero (by norm_num : 2 ≠ 0) (ne_of_gt hL)
  rw [Nat.cast_sub h2L, Nat.cast_sub hn]
  field_simp
  push_cast
  ring

/-- The exact one-dimensional frequency box `[-L,L]`. -/
noncomputable def spectrumBox (L : ℕ) : Finset ℤ :=
  Finset.Icc (-(L : ℤ)) (L : ℤ)

/-- A function has spectrum in `[-L,L]` when it is given by a finite Fourier
expansion over that box.  This constructive formulation avoids any uniqueness
or Fourier-inversion prerequisites. -/
def HasSpectrumAtMost (L : ℕ) (f : UnitAddCircle → ℂ) : Prop :=
  ∃ c : ℤ → ℂ, ∀ x,
    f x = ∑ n ∈ spectrumBox L, c n * fourier n x

/-- Our convolution convention is `(κ ∗ f)(x) = ∫ κ(y) f(x-y) dy`. -/
noncomputable def circleConvolution (κ f : UnitAddCircle → ℂ)
    (x : UnitAddCircle) : ℂ :=
  ∫ y : UnitAddCircle, κ y * f (x - y) ∂AddCircle.haarAddCircle

/-- A one-dimensional character is multiplicative under subtraction in its
argument. -/
lemma fourier_apply_sub (n : ℤ) (x y : UnitAddCircle) :
    fourier n (x - y) = fourier n x * fourier (-n) y := by
  induction x using QuotientAddGroup.induction_on with
  | H a =>
    induction y using QuotientAddGroup.induction_on with
    | H b =>
      simp only [← QuotientAddGroup.mk_sub, fourier_coe_apply]
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring

/-- Convolution by a kernel acts on a character by its corresponding Fourier
coefficient. -/
lemma circleConvolution_fourier (κ : UnitAddCircle → ℂ) (n : ℤ)
    (x : UnitAddCircle) :
    circleConvolution κ (fourier n) x =
      fourier n x * fourierCoeff (T := (1 : ℝ)) κ n := by
  unfold circleConvolution fourierCoeff
  calc
    (∫ y : UnitAddCircle, κ y * fourier n (x - y)
        ∂AddCircle.haarAddCircle) =
        ∫ y : UnitAddCircle,
          (fourier (-n) y * κ y) * fourier n x
            ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [fourier_apply_sub]
      ring
    _ = (∫ y : UnitAddCircle, fourier (-n) y * κ y
          ∂AddCircle.haarAddCircle) * fourier n x := by
      rw [integral_mul_const]
    _ = fourier n x *
        (∫ y : UnitAddCircle, fourier (-n) y * κ y
          ∂AddCircle.haarAddCircle) := by ring

/-- Lemma 4.1, reproduction part: the explicit de la Vallée Poussin kernel
reproduces every trigonometric polynomial with spectrum in `[-L,L]`. -/
theorem circleConvolution_vallPoussinKernel_eq
    (L : ℕ) (hL : 0 < L) (f : UnitAddCircle → ℂ)
    (hf : HasSpectrumAtMost L f) (x : UnitAddCircle) :
    circleConvolution (vallPoussinKernel L) f x = f x := by
  classical
  obtain ⟨c, hc⟩ := hf
  rw [hc x]
  unfold circleConvolution
  simp_rw [hc]
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro n hn
    have hnbox : n.natAbs ≤ L := by
      simp only [spectrumBox, Finset.mem_Icc] at hn
      have hs : n.natAbs ≤ (L : ℤ).natAbs := by
        rw [Int.natAbs_le_iff_sq_le]
        nlinarith [hn.1, hn.2]
      simpa using hs
    have hchar := circleConvolution_fourier
      (vallPoussinKernel L) n x
    unfold circleConvolution at hchar
    rw [fourierCoeff_vallPoussinKernel_eq_one L hL n hnbox] at hchar
    calc
      (∫ y : UnitAddCircle,
          vallPoussinKernel L y * (c n * fourier n (x - y))
            ∂AddCircle.haarAddCircle) =
          c n * (∫ y : UnitAddCircle,
            vallPoussinKernel L y * fourier n (x - y)
              ∂AddCircle.haarAddCircle) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with y
        ring
      _ = c n * fourier n x := by rw [hchar, mul_one]
  · intro n hn
    apply Continuous.integrable_of_hasCompactSupport
    · exact (continuous_vallPoussinKernel L).mul
        (continuous_const.mul
          ((map_continuous (fourier n)).comp (continuous_const.sub continuous_id)))
    · exact HasCompactSupport.of_compactSpace _

/-- The chord cut out by the first character has the familiar sine length. -/
lemma norm_one_sub_fourier_one_coe (u : ℝ) :
    ‖(1 : ℂ) - fourier 1 (u : UnitAddCircle)‖ =
      2 * |Real.sin (Real.pi * u)| := by
  have hexp : fourier 1 (u : UnitAddCircle) =
      Complex.exp (Complex.I * (2 * Real.pi * u : ℝ)) := by
    rw [fourier_coe_apply]
    norm_num
    congr 1
    push_cast
    ring
  rw [hexp]
  rw [norm_sub_rev]
  rw [Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

/-- On `ℝ / ℤ`, chordal distance under the first character dominates four
times the quotient norm. -/
lemma four_mul_norm_le_norm_one_sub_fourier_one (x : UnitAddCircle) :
    4 * ‖x‖ ≤ ‖(1 : ℂ) - fourier 1 x‖ := by
  let u : ℝ := (AddCircle.equivIoc (1 : ℝ) (-(1 / 2 : ℝ)) x : ℝ)
  have hu_mem : u ∈ Set.Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1) :=
    (AddCircle.equivIoc (1 : ℝ) (-(1 / 2 : ℝ)) x).property
  have hu_abs : |u| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith [hu_mem.1, hu_mem.2]
  have hux : (u : UnitAddCircle) = x := by
    exact AddCircle.coe_equivIoc
  rw [← hux]
  have hnorm : ‖(u : UnitAddCircle)‖ = |u| :=
    (AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ)) one_ne_zero).2 (by
      simpa using hu_abs)
  rw [hnorm, norm_one_sub_fourier_one_coe]
  have harg : |Real.pi * u| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos.le]
  have hsin := Real.mul_abs_le_abs_sin harg
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  rw [abs_mul, abs_of_pos Real.pi_pos] at hsin
  calc
    4 * |u| = 2 * ((2 / Real.pi) * (Real.pi * |u|)) := by
      field_simp
      ring
    _ ≤ 2 * |Real.sin (Real.pi * u)| := by nlinarith

/-- The finite geometric-series identity on the circle. -/
lemma one_sub_fourier_mul_geometricPolynomial (Q : ℕ) (x : UnitAddCircle) :
    ((1 : ℂ) - fourier 1 x) * geometricPolynomial Q x =
      1 - fourier (Q : ℤ) x := by
  induction Q with
  | zero => simp [geometricPolynomial, fourier_zero]
  | succ Q ih =>
      rw [geometricPolynomial, Finset.sum_range_succ]
      change ((1 : ℂ) - fourier 1 x) *
          (geometricPolynomial Q x + fourier (Q : ℤ) x) = _
      rw [mul_add, ih]
      have hadd : fourier ((Q + 1 : ℕ) : ℤ) x =
          fourier 1 x * fourier (Q : ℤ) x := by
        rw [show ((Q + 1 : ℕ) : ℤ) = 1 + (Q : ℤ) by omega, fourier_add]
      rw [hadd]
      ring

/-- The elementary geometric-series estimate in a division-free form. -/
lemma norm_fejerKernel_mul_chord_sq_le (Q : ℕ) (hQ : 0 < Q)
    (x : UnitAddCircle) :
    ‖fejerKernel Q x‖ * ‖(1 : ℂ) - fourier 1 x‖ ^ 2 ≤
      4 / (Q : ℝ) := by
  have hprod :
      ‖geometricPolynomial Q x‖ * ‖(1 : ℂ) - fourier 1 x‖ ≤ 2 := by
    calc
      ‖geometricPolynomial Q x‖ * ‖(1 : ℂ) - fourier 1 x‖ =
          ‖((1 : ℂ) - fourier 1 x) * geometricPolynomial Q x‖ := by
        rw [norm_mul]
        ring
      _ = ‖(1 : ℂ) - fourier (Q : ℤ) x‖ := by
        rw [one_sub_fourier_mul_geometricPolynomial]
      _ ≤
          ‖(1 : ℂ)‖ + ‖fourier (Q : ℤ) x‖ := norm_sub_le _ _
      _ = 2 := by
        simp only [norm_one, fourier_apply, Circle.norm_coe]
        norm_num
  have hprod_nonneg :
      0 ≤ ‖geometricPolynomial Q x‖ * ‖(1 : ℂ) - fourier 1 x‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hsq :
      (‖geometricPolynomial Q x‖ * ‖(1 : ℂ) - fourier 1 x‖) ^ 2 ≤ 4 := by
    nlinarith
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  rw [fejerKernel, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  calc
    (‖geometricPolynomial Q x‖ ^ 2 / (Q : ℝ)) *
          ‖(1 : ℂ) - fourier 1 x‖ ^ 2 =
        (‖geometricPolynomial Q x‖ *
            ‖(1 : ℂ) - fourier 1 x‖) ^ 2 / (Q : ℝ) := by ring
    _ ≤ 4 / (Q : ℝ) := div_le_div_of_nonneg_right hsq hQr.le

/-- Quadratic Fejér decay in the intrinsic distance on `ℝ / ℤ`. -/
lemma norm_fejerKernel_mul_norm_sq_le (Q : ℕ) (hQ : 0 < Q)
    (x : UnitAddCircle) :
    ‖fejerKernel Q x‖ * ‖x‖ ^ 2 ≤ 4 / (Q : ℝ) := by
  have hdist := four_mul_norm_le_norm_one_sub_fourier_one x
  have hnorm : ‖x‖ ≤ ‖(1 : ℂ) - fourier 1 x‖ := by
    have hx := norm_nonneg x
    linarith
  have hsq : ‖x‖ ^ 2 ≤ ‖(1 : ℂ) - fourier 1 x‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg x) (norm_nonneg _)).2 hnorm
  calc
    ‖fejerKernel Q x‖ * ‖x‖ ^ 2 ≤
        ‖fejerKernel Q x‖ * ‖(1 : ℂ) - fourier 1 x‖ ^ 2 := by
      gcongr
    _ ≤ 4 / (Q : ℝ) := norm_fejerKernel_mul_chord_sq_le Q hQ x

/-- Quadratic tail estimate for the de la Vallée Poussin kernel. -/
lemma norm_vallPoussinKernel_mul_norm_sq_le (L : ℕ) (hL : 0 < L)
    (x : UnitAddCircle) :
    ‖vallPoussinKernel L x‖ * ‖x‖ ^ 2 ≤ 8 / (L : ℝ) := by
  have htri : ‖vallPoussinKernel L x‖ ≤
      2 * ‖fejerKernel (2 * L) x‖ + ‖fejerKernel L x‖ := by
    rw [vallPoussinKernel]
    calc
      ‖2 * fejerKernel (2 * L) x - fejerKernel L x‖ ≤
          ‖2 * fejerKernel (2 * L) x‖ + ‖fejerKernel L x‖ := norm_sub_le _ _
      _ = 2 * ‖fejerKernel (2 * L) x‖ + ‖fejerKernel L x‖ := by norm_num
  have hmul := mul_le_mul_of_nonneg_right htri (sq_nonneg ‖x‖)
  have h2 := norm_fejerKernel_mul_norm_sq_le (2 * L) (by omega) x
  have h1 := norm_fejerKernel_mul_norm_sq_le L hL x
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  calc
    ‖vallPoussinKernel L x‖ * ‖x‖ ^ 2 ≤
        (2 * ‖fejerKernel (2 * L) x‖ + ‖fejerKernel L x‖) * ‖x‖ ^ 2 := hmul
    _ = 2 * (‖fejerKernel (2 * L) x‖ * ‖x‖ ^ 2) +
          ‖fejerKernel L x‖ * ‖x‖ ^ 2 := by ring
    _ ≤ 2 * (4 / ((2 * L : ℕ) : ℝ)) + 4 / (L : ℝ) := by gcongr
    _ = 8 / (L : ℝ) := by
      push_cast
      field_simp
      ring

/-- Lemma 4.1, pointwise part, with the explicit quadratic constant `13`.
Quadratic decay is already summable in every coordinate after tensorization. -/
theorem norm_vallPoussinKernel_le_decay (L : ℕ) (hL : 0 < L)
    (x : UnitAddCircle) :
    ‖vallPoussinKernel L x‖ ≤
      13 * (L : ℝ) / (1 + ((L : ℝ) * ‖x‖) ^ 2) := by
  have hzero : 0 < 1 + ((L : ℝ) * ‖x‖) ^ 2 := by positivity
  rw [le_div_iff₀ hzero]
  have hsup := norm_vallPoussinKernel_le L hL x
  have htail := norm_vallPoussinKernel_mul_norm_sq_le L hL x
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  calc
    ‖vallPoussinKernel L x‖ * (1 + ((L : ℝ) * ‖x‖) ^ 2) =
        ‖vallPoussinKernel L x‖ +
          (L : ℝ) ^ 2 * (‖vallPoussinKernel L x‖ * ‖x‖ ^ 2) := by ring
    _ ≤ 5 * (L : ℝ) + (L : ℝ) ^ 2 * (8 / (L : ℝ)) := by gcongr
    _ = 13 * (L : ℝ) := by field_simp; ring

end ReproducingKernel
end ImprovedWeylBounds
