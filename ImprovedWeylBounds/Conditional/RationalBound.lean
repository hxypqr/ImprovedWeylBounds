import ImprovedWeylBounds.Translation
import ImprovedWeylBounds.Arithmetic
import ImprovedWeylBounds.Asymptotics
import ImprovedWeylBounds.Conditional.Inverse
import ImprovedWeylBounds.ExponentArithmetic

open scoped BigOperators
open Polynomial

namespace ImprovedWeylBounds.Conditional

open ImprovedWeylBounds

noncomputable def polyCoefficients (d : ℕ) (P : ℝ[X]) : CoefficientVector d :=
  fun j => P.coeff (j.val + 1)

noncomputable def polynomialShortSum (P : ℝ[X]) (M : ℤ) (H : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 H, e (P.eval ((M : ℝ) + (n : ℝ)))

theorem eval_eq_coeff_zero_add_phase (d : ℕ) (P : ℝ[X])
    (hP : P.natDegree ≤ d) (n : ℕ) :
    P.eval (n : ℝ) = P.coeff 0 + nonconstantPhase (polyCoefficients d P) n := by
  rw [P.eval_eq_sum_range' (Nat.lt_succ_of_le hP)]
  rw [Finset.sum_range_succ']
  simp only [pow_zero, mul_one]
  simp only [nonconstantPhase, polyCoefficients]
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ => P.coeff (k + 1) * (n : ℝ) ^ (k + 1)) d]
  ac_rfl

theorem polynomialShortSum_eq (d : ℕ) (P : ℝ[X]) (M : ℤ) (H : ℕ)
    (hP : P.natDegree ≤ d) :
    polynomialShortSum P M H =
      e ((translate M P).coeff 0) * g (polyCoefficients d (translate M P)) H := by
  have hQ : (translate M P).natDegree ≤ d := by simpa using hP
  rw [polynomialShortSum, g]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [add_comm (M : ℝ) (n : ℝ)]
  rw [← eval_translate M P (n : ℝ)]
  rw [eval_eq_coeff_zero_add_phase d (translate M P) hQ n]
  rw [e_add]

theorem polyCoefficients_top (d : ℕ) (hd : 1 ≤ d) (P : ℝ[X]) (M : ℤ)
    (hdeg : P.natDegree = d) :
    polyCoefficients d (translate M P) ⟨d - 1, by omega⟩ = P.coeff d := by
  change (translate M P).coeff ((d - 1) + 1) = P.coeff d
  rw [Nat.sub_add_cancel hd]
  have hlead := leadingCoeff_translate M P
  rw [Polynomial.leadingCoeff, Polynomial.leadingCoeff, natDegree_translate, hdeg] at hlead
  exact hlead

theorem norm_polynomialShortSum_eq (d : ℕ) (P : ℝ[X]) (M : ℤ) (H : ℕ)
    (hP : P.natDegree ≤ d) :
    ‖polynomialShortSum P M H‖ = ‖g (polyCoefficients d (translate M P)) H‖ := by
  rw [polynomialShortSum_eq d P M H hP, norm_mul, norm_e, one_mul]

private theorem ratio_pow_mul_rpow_lt
    {x A b η : ℝ} {d : ℕ} (hx : 0 < x)
    (hd : 0 < d)
    (hA : Real.rpow x b < A) :
    (x / A) ^ d * Real.rpow x η <
      Real.rpow x ((d : ℝ) * (1 - b) + η) := by
  have hAbase : 0 < Real.rpow x b := Real.rpow_pos_of_pos hx _
  have hApos : 0 < A := hAbase.trans hA
  have hratio : x / A < x / Real.rpow x b := by
    exact (div_lt_div_iff_of_pos_left hx hApos hAbase).2 hA
  have hratioNonneg : 0 ≤ x / A := (div_pos hx hApos).le
  have hpow := pow_lt_pow_left₀ hratio hratioNonneg (Nat.ne_of_gt hd)
  have heta : 0 < Real.rpow x η := Real.rpow_pos_of_pos hx _
  have hdiv : x / Real.rpow x b = Real.rpow x (1 - b) := by
    symm
    calc
      Real.rpow x (1 - b) = Real.rpow x 1 / Real.rpow x b :=
        Real.rpow_sub hx 1 b
      _ = x / Real.rpow x b := by simp
  calc
    (x / A) ^ d * Real.rpow x η <
        (x / Real.rpow x b) ^ d * Real.rpow x η :=
      mul_lt_mul_of_pos_right hpow heta
    _ = Real.rpow x ((d : ℝ) * (1 - b) + η) := by
      rw [hdiv]
      calc
        Real.rpow x (1 - b) ^ d * Real.rpow x η =
            Real.rpow x ((1 - b) * (d : ℝ)) * Real.rpow x η := by
          congr 1
          exact (Real.rpow_mul_natCast hx.le (1 - b) d).symm
        _ = Real.rpow x (((1 - b) * (d : ℝ)) + η) :=
          (Real.rpow_add hx _ _).symm
        _ = Real.rpow x ((d : ℝ) * (1 - b) + η) := by ring_nf

private theorem approximation_scale_identity
    {x A C η : ℝ} {d : ℕ} (hx : 0 < x) (hA : 0 < A) :
    C * (x / A) ^ d * Real.rpow x (-(d : ℝ) + η) =
      C * Real.rpow x η / A ^ d := by
  have hx0 : x ≠ 0 := hx.ne'
  have hA0 : A ≠ 0 := hA.ne'
  rw [show -(d : ℝ) + η = η - d by ring]
  have hrpow : Real.rpow x (η - (d : ℝ)) = Real.rpow x η / x ^ d := by
    exact Real.rpow_sub_natCast hx0 η d
  rw [hrpow]
  rw [div_pow]
  field_simp

private theorem amplitude_pow_le
    {q d : ℕ} {x A C η : ℝ}
    (hq : 0 < q) (hx : 0 < x) (hA : 0 < A)
    (hsep : 1 / (q : ℝ) ≤
      C * (x / A) ^ d * Real.rpow x (-(d : ℝ) + η)) :
    A ^ d ≤ C * (q : ℝ) * Real.rpow x η := by
  rw [approximation_scale_identity hx hA] at hsep
  have hqreal : 0 < (q : ℝ) := by exact_mod_cast hq
  have hAd : 0 < A ^ d := pow_pos hA _
  calc
    A ^ d = (1 / (q : ℝ)) * ((q : ℝ) * A ^ d) := by field_simp
    _ ≤ (C * Real.rpow x η / A ^ d) * ((q : ℝ) * A ^ d) := by
      exact mul_le_mul_of_nonneg_right hsep (by positivity)
    _ = C * (q : ℝ) * Real.rpow x η := by field_simp

private theorem amplitude_le_root_bound
    {q d : ℕ} {x A C η ε : ℝ}
    (hq : 0 < q) (hd : 0 < d) (hx : 1 ≤ x)
    (hη : η ≤ (d : ℝ) * ε)
    (hpow : A ^ d ≤ C * (q : ℝ) * Real.rpow x η) :
    A ≤ max 1 C * Real.rpow (q : ℝ) (1 / (d : ℝ)) * Real.rpow x ε := by
  let B : ℝ := max 1 C
  have hB1 : 1 ≤ B := le_max_left _ _
  have hBC : C ≤ B := le_max_right _ _
  have hBd : C ≤ B ^ d :=
    hBC.trans (le_self_pow₀ hB1 (Nat.ne_of_gt hd))
  have hqreal : 0 < (q : ℝ) := by exact_mod_cast hq
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hxrpow : Real.rpow x η ≤ Real.rpow x ((d : ℝ) * ε) :=
    Real.rpow_le_rpow_of_exponent_le hx hη
  have hηnonneg : 0 ≤ Real.rpow x η := Real.rpow_nonneg hxpos.le _
  have hmain :
      C * (q : ℝ) * Real.rpow x η ≤
        B ^ d * (q : ℝ) * Real.rpow x ((d : ℝ) * ε) := by
    gcongr
  have hqroot : (Real.rpow (q : ℝ) (1 / (d : ℝ))) ^ d = (q : ℝ) := by
    calc
      (Real.rpow (q : ℝ) (1 / (d : ℝ))) ^ d =
          Real.rpow (q : ℝ) ((1 / (d : ℝ)) * (d : ℝ)) :=
        (Real.rpow_mul_natCast hqreal.le (1 / (d : ℝ)) d).symm
      _ = Real.rpow (q : ℝ) 1 := by
        congr 1
        field_simp
      _ = (q : ℝ) := by simp
  have hxroot : (Real.rpow x ε) ^ d = Real.rpow x ((d : ℝ) * ε) := by
    calc
      (Real.rpow x ε) ^ d = Real.rpow x (ε * (d : ℝ)) :=
        (Real.rpow_mul_natCast hxpos.le ε d).symm
      _ = Real.rpow x ((d : ℝ) * ε) := by ring_nf
  apply le_of_pow_le_pow_left₀ (Nat.ne_of_gt hd)
    (mul_nonneg
      (mul_nonneg (zero_le_one.trans hB1) (Real.rpow_nonneg hqreal.le _))
      (Real.rpow_nonneg hxpos.le _))
  calc
    A ^ d ≤ C * (q : ℝ) * Real.rpow x η := hpow
    _ ≤ B ^ d * (q : ℝ) * Real.rpow x ((d : ℝ) * ε) := hmain
    _ = (B * Real.rpow (q : ℝ) (1 / (d : ℝ)) * Real.rpow x ε) ^ d := by
      rw [mul_pow, mul_pow, hqroot, hxroot]

/-- The fully quantified meaning of the paper's rational short-interval
Vinogradov bound.  The threshold is uniform in the modulus, interval
location, polynomial, and reduced leading fraction. -/
def RationalShortIntervalBound (d : ℕ) (ε : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ H₀ : ℕ, 1 ≤ H₀ ∧
    ∀ (q H : ℕ) (M : ℤ) (P : ℝ[X]) (a : ℤ),
      H₀ ≤ H → 1 ≤ H → H ≤ q → a.natAbs.Coprime q →
      P.natDegree = d → P.coeff d = (a : ℝ) / (q : ℝ) →
      ‖polynomialShortSum P M H‖ ≤
        C *
          (Real.rpow (q : ℝ) (1 / (d : ℝ)) * Real.rpow (H : ℝ) ε +
            Real.rpow (H : ℝ) (1 - 1 / (Delta d : ℝ) + ε))

/-- The internal deduction at `main.tex:1072-1102`: the inverse principle,
rational separation, and elementary real-power algebra imply the rational
short-interval estimate. -/
theorem rationalShortIntervalBound_of_inverse
    (d : ℕ) (hd : 3 ≤ d) (ε : ℝ) (hε : 0 < ε)
    (hInverse : InversePrinciple d (Delta d)) :
    RationalShortIntervalBound d ε := by
  let δ : ℝ := ε / 2
  let η : ℝ := ε / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨C₀, hC₀, N₀, hN₀, hinv⟩ := hInverse δ η hδ hη
  let b : ℝ := 1 - 1 / (Delta d : ℝ) + δ
  let ar : ℝ := (d : ℝ) * (1 - b) + η
  have hdReal : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have har_lt : ar < 1 := by
    have hbase := degree_div_Delta_lt_one d hd
    dsimp [ar, b, δ, η]
    have hneg : -(d : ℝ) * ε / 2 + ε / 4 < 0 := by nlinarith
    have heq :
        (d : ℝ) * (1 - (1 - 1 / (Delta d : ℝ) + ε / 2)) + ε / 4 =
          (d : ℝ) / (Delta d : ℝ) + (-(d : ℝ) * ε / 2 + ε / 4) := by
      ring
    rw [heq]
    linarith
  have hevent := eventually_const_mul_rpow_lt_rpow C₀ ar 1 har_lt
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp hevent
  let H₀ : ℕ := max 1 (max N₀ N₁)
  let C : ℝ := max 1 C₀
  have hC1 : 1 ≤ C := le_max_left _ _
  have hC : 0 < C := zero_lt_one.trans_le hC1
  refine ⟨C, hC, H₀, by simp [H₀], ?_⟩
  intro q H M P a hH₀ hHpos hHq hcop hdeg hlead
  have hHN₀ : N₀ ≤ H := le_trans (le_max_left N₀ N₁)
    (le_trans (le_max_right 1 (max N₀ N₁)) hH₀)
  have hHN₁ : N₁ ≤ H := le_trans (le_trans (le_max_right N₀ N₁)
    (le_max_right 1 (max N₀ N₁))) hH₀
  have hHreal : 1 ≤ (H : ℝ) := by exact_mod_cast hHpos
  have hHrealPos : 0 < (H : ℝ) := zero_lt_one.trans_le hHreal
  have hqpos : 0 < q := lt_of_lt_of_le (by omega : 0 < H) hHq
  let α : CoefficientVector d := polyCoefficients d (translate M P)
  let A : ℝ := ‖g α H‖
  have hPdeg : P.natDegree ≤ d := hdeg.le
  have hsum : ‖polynomialShortSum P M H‖ = A := by
    dsimp [A, α]
    exact norm_polynomialShortSum_eq d P M H hPdeg
  rw [hsum]
  have htermOne :
      0 ≤ Real.rpow (q : ℝ) (1 / (d : ℝ)) * Real.rpow (H : ℝ) ε :=
    mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (Real.rpow_nonneg hHrealPos.le _)
  have htermTwo :
      0 ≤ Real.rpow (H : ℝ) (1 - 1 / (Delta d : ℝ) + ε) :=
    Real.rpow_nonneg hHrealPos.le _
  by_cases hsmall : A ≤ Real.rpow (H : ℝ) b
  · have hb_le : b ≤ 1 - 1 / (Delta d : ℝ) + ε := by
      dsimp [b, δ]
      linarith
    have hrpow_le := Real.rpow_le_rpow_of_exponent_le hHreal hb_le
    calc
      A ≤ Real.rpow (H : ℝ) b := hsmall
      _ ≤ Real.rpow (H : ℝ) (1 - 1 / (Delta d : ℝ) + ε) := hrpow_le
      _ ≤ Real.rpow (q : ℝ) (1 / (d : ℝ)) * Real.rpow (H : ℝ) ε +
          Real.rpow (H : ℝ) (1 - 1 / (Delta d : ℝ) + ε) :=
        le_add_of_nonneg_left htermOne
      _ = 1 * (Real.rpow (q : ℝ) (1 / (d : ℝ)) * Real.rpow (H : ℝ) ε +
          Real.rpow (H : ℝ) (1 - 1 / (Delta d : ℝ) + ε)) := by rw [one_mul]
      _ ≤ C * (Real.rpow (q : ℝ) (1 / (d : ℝ)) * Real.rpow (H : ℝ) ε +
          Real.rpow (H : ℝ) (1 - 1 / (Delta d : ℝ) + ε)) :=
        mul_le_mul_of_nonneg_right hC1 (add_nonneg htermOne htermTwo)
  · have hlarge : Real.rpow (H : ℝ) b < A := lt_of_not_ge hsmall
    have hApos : 0 < A := (Real.rpow_pos_of_pos hHrealPos _).trans hlarge
    have hthreshold :
        Real.rpow (H : ℝ)
          (1 - 1 / (Delta d : ℝ) + δ) < A := by
      simpa [b] using hlarge
    obtain ⟨approx⟩ := hinv H hHN₀ α A hApos le_rfl hthreshold
    let r : ℕ := approx.q
    have hrpos : 0 < r := approx.q_pos
    have hratio :
        ((H : ℝ) / A) ^ d * Real.rpow (H : ℝ) η <
          Real.rpow (H : ℝ) ar := by
      simpa [ar] using
        (ratio_pow_mul_rpow_lt hHrealPos (by omega : 0 < d) hlarge)
    have hrHreal : (r : ℝ) < (H : ℝ) := by
      calc
        (r : ℝ) ≤ C₀ * (((H : ℝ) / A) ^ d) * Real.rpow (H : ℝ) η :=
          approx.denominator_bound
        _ = C₀ * ((((H : ℝ) / A) ^ d) * Real.rpow (H : ℝ) η) := by ring
        _ < C₀ * Real.rpow (H : ℝ) ar :=
          mul_lt_mul_of_pos_left hratio hC₀
        _ < Real.rpow (H : ℝ) 1 := hN₁ H hHN₁
        _ = (H : ℝ) := by simp
    have hrH : r < H := by exact_mod_cast hrHreal
    have hrq : r < q := lt_of_lt_of_le hrH hHq
    let jtop : Fin d := ⟨d - 1, by omega⟩
    have hjtop : jtop.val + 1 = d := by dsimp [jtop]; omega
    have hαtop : α jtop = (a : ℝ) / (q : ℝ) := by
      dsimp [α]
      rw [polyCoefficients_top d (by omega) P M hdeg, hlead]
    have hdistUpper :
        distToInt (((r : ℝ) * (a : ℝ)) / (q : ℝ)) ≤
          C₀ * (((H : ℝ) / A) ^ d) *
            Real.rpow (H : ℝ) (-(d : ℝ) + η) := by
      calc
        distToInt (((r : ℝ) * (a : ℝ)) / (q : ℝ)) =
            distToInt ((r : ℝ) * α jtop) := by rw [hαtop]; ring_nf
        _ ≤ |(r : ℝ) * α jtop - (approx.numerator jtop : ℝ)| :=
          distToInt_le_abs_sub_int _ _
        _ ≤ C₀ * (((H : ℝ) / A) ^ d) *
            Real.rpow (H : ℝ) (-(d : ℝ) + η) := by
          simpa [hjtop] using approx.coefficient_bound jtop
    have hsep := reduced_fraction_separation_int hcop hrpos hrq
    have hApow :
        A ^ d ≤ C₀ * (q : ℝ) * Real.rpow (H : ℝ) η :=
      amplitude_pow_le hqpos hHrealPos hApos (hsep.trans hdistUpper)
    have hηε : η ≤ (d : ℝ) * ε := by
      dsimp [η]
      nlinarith
    have hroot :
        A ≤ C * Real.rpow (q : ℝ) (1 / (d : ℝ)) * Real.rpow (H : ℝ) ε := by
      simpa [C] using amplitude_le_root_bound hqpos (by omega : 0 < d)
        hHreal hηε hApow
    calc
      A ≤ C * Real.rpow (q : ℝ) (1 / (d : ℝ)) * Real.rpow (H : ℝ) ε := hroot
      _ ≤ C *
          (Real.rpow (q : ℝ) (1 / (d : ℝ)) * Real.rpow (H : ℝ) ε +
            Real.rpow (H : ℝ) (1 - 1 / (Delta d : ℝ) + ε)) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right htermTwo) hC.le
end ImprovedWeylBounds.Conditional
