import ImprovedWeylBounds.Basic

/-!
# Arithmetic of the Weyl exponents

This file checks the elementary degree and exponent calculations used in the
paper.  In particular, it identifies the two branches of `Delta`, verifies the
strict gain encoded by `tau`, derives the branch point after the change of
variables from `delta` to `u`, and checks the two numerical inequalities used
in the prime-argument application.
-/

namespace ImprovedWeylBounds

noncomputable section

set_option autoImplicit false

/-! ## The parameters `K` and `Delta` -/

/-- Unfolding the critical moment exponent. -/
@[simp]
theorem K_eq_mul_sub_one (k : ℕ) : K k = k * (k - 1) := rfl

/-- Starting in degree three, the classical power `2^(k-1)` is strictly
larger than the degree itself. -/
private theorem degree_lt_two_pow_pred {k : ℕ} (hk : 3 ≤ k) :
    k < 2 ^ (k - 1) := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      simp only [Nat.add_sub_cancel]
      have hkEq : k = (k - 1) + 1 := by omega
      have hkpow : 2 ^ k = 2 * 2 ^ (k - 1) := by
        calc
          2 ^ k = 2 ^ ((k - 1) + 1) := congrArg (2 ^ ·) hkEq
          _ = 2 ^ (k - 1) * 2 := by rw [pow_succ]
          _ = 2 * 2 ^ (k - 1) := Nat.mul_comm _ _
      rw [hkpow]
      have hpowpos : 0 < 2 ^ (k - 1) := pow_pos (by norm_num) _
      omega

/-- For `k ≥ 6`, the VMVT denominator `k(k-1)` is no larger than the
classical denominator `2^(k-1)`. -/
private theorem quadratic_le_two_pow_pred {k : ℕ} (hk : 6 ≤ k) :
    k * (k - 1) ≤ 2 ^ (k - 1) := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      simp only [Nat.add_sub_cancel]
      have hkEq : k = (k - 1) + 1 := by omega
      have hkpow : 2 ^ k = 2 * 2 ^ (k - 1) := by
        calc
          2 ^ k = 2 ^ ((k - 1) + 1) := congrArg (2 ^ ·) hkEq
          _ = 2 ^ (k - 1) * 2 := by rw [pow_succ]
          _ = 2 * 2 ^ (k - 1) := Nat.mul_comm _ _
      rw [hkpow]
      have hfac : k + 1 ≤ 2 * (k - 1) := by omega
      calc
        (k + 1) * k ≤ (2 * (k - 1)) * k := Nat.mul_le_mul_right k hfac
        _ = 2 * (k * (k - 1)) := by ring
        _ ≤ 2 * 2 ^ (k - 1) := Nat.mul_le_mul_left 2 ih

/-- The combined denominator is strictly larger than the degree for every
degree occurring in the paper. -/
theorem degree_lt_Delta (k : ℕ) (hk : 3 ≤ k) : k < Delta k := by
  rw [Delta, lt_min_iff]
  exact ⟨degree_lt_two_pow_pred hk, by
    rw [K]
    have htwo : 2 ≤ k - 1 := by omega
    calc
      k = k * 1 := by omega
      _ < k * (k - 1) := Nat.mul_lt_mul_of_pos_left htwo (by omega)⟩

/-- Integral form of `degree_lt_Delta`. -/
theorem degree_add_one_le_Delta (k : ℕ) (hk : 3 ≤ k) :
    k + 1 ≤ Delta k :=
  Nat.succ_le_iff.mpr (degree_lt_Delta k hk)

/-- Real-valued form of the inequality `k < Delta k`. -/
theorem degree_div_Delta_lt_one (k : ℕ) (hk : 3 ≤ k) :
    (k : ℝ) / (Delta k : ℝ) < 1 := by
  have hDeltaPos : 0 < (Delta k : ℝ) := by
    exact_mod_cast (lt_trans (by omega : 0 < k) (degree_lt_Delta k hk))
  rw [div_lt_one hDeltaPos]
  exact_mod_cast degree_lt_Delta k hk

/-- From degree six onward, the VMVT branch is the minimum. -/
theorem Delta_eq_K_of_six_le (k : ℕ) (hk : 6 ≤ k) : Delta k = K k := by
  rw [Delta, min_eq_right]
  exact quadratic_le_two_pow_pred hk

/-- Expanded form of `Delta_eq_K_of_six_le`. -/
theorem Delta_eq_mul_sub_one_of_six_le (k : ℕ) (hk : 6 ≤ k) :
    Delta k = k * (k - 1) := by
  rw [Delta_eq_K_of_six_le k hk, K]

/-- The denominator in degree six is `30`. -/
@[simp]
theorem Delta_six : Delta 6 = 30 := by
  norm_num [Delta, K]

/-! ## Strict improvement over the generic saving -/

/-- The saving appearing in the new prime-field estimate. -/
def tau (d : ℕ) (u : ℝ) : ℝ :=
  min (u / (d : ℝ)) (1 / (Delta d : ℝ))

/-- In the natural window `0 < u < 1`, the new saving `tau d u` is strictly
larger than the generic saving `u / Delta d`. -/
theorem benchmarkSaving_lt_tau (d : ℕ) (hd : 3 ≤ d) {u : ℝ}
    (hu : 0 < u) (hu1 : u < 1) :
    u / (Delta d : ℝ) < tau d u := by
  rw [tau, lt_min_iff]
  have hdPos : 0 < (d : ℝ) := by positivity
  have hDeltaPos : 0 < (Delta d : ℝ) := by
    exact_mod_cast (lt_trans (by omega : 0 < d) (degree_lt_Delta d hd))
  have hdDelta : (d : ℝ) < (Delta d : ℝ) := by
    exact_mod_cast degree_lt_Delta d hd
  exact ⟨(div_lt_div_iff_of_pos_left hu hDeltaPos hdPos).2 hdDelta,
    (div_lt_div_iff_of_pos_right hDeltaPos).2 hu1⟩

/-! ## The `delta`-to-`u` change of variables and branch point -/

/-- If `H = p^(1/d + delta)`, exponent arithmetic gives this value of `u`. -/
def uFromDelta (d : ℕ) (δ : ℝ) : ℝ :=
  (d : ℝ) ^ 2 * δ / (1 + (d : ℝ) * δ)

/-- The value of `delta` at which the two branches of `tau` meet. -/
def branchPoint (d : ℕ) : ℝ :=
  1 / ((d : ℝ) * ((Delta d : ℝ) - 1))

/-- The displayed formula for `u` is definitionally exact. -/
@[simp]
theorem uFromDelta_formula (d : ℕ) (δ : ℝ) :
    uFromDelta d δ = (d : ℝ) ^ 2 * δ / (1 + (d : ℝ) * δ) := rfl

private theorem uFromDelta_div_degree (d : ℕ) (hd : 0 < d) (δ : ℝ) :
    uFromDelta d δ / (d : ℝ) =
      (d : ℝ) * δ / (1 + (d : ℝ) * δ) := by
  unfold uFromDelta
  have hdn : (d : ℝ) ≠ 0 := by positivity
  field_simp

/-- The first branch is active precisely up to the displayed branch point. -/
theorem uFromDelta_branch_le_iff (d : ℕ) (hd : 3 ≤ d) (δ : ℝ)
    (hδ : 0 ≤ δ) :
    uFromDelta d δ / (d : ℝ) ≤ 1 / (Delta d : ℝ) ↔
      δ ≤ branchPoint d := by
  let x : ℝ := d
  let D : ℝ := Delta d
  have hx : 0 < x := by dsimp [x]; positivity
  have hxThree : 3 ≤ x := by dsimp [x]; exact_mod_cast hd
  have hD : 0 < D := by
    dsimp [D]
    exact_mod_cast (lt_trans (by omega : 0 < d) (degree_lt_Delta d hd))
  have hxD : x < D := by
    dsimp [x, D]
    exact_mod_cast degree_lt_Delta d hd
  have hden : 0 < 1 + x * δ := by positivity
  have hDm1 : 0 < D - 1 := by linarith
  have hprod : 0 < x * (D - 1) := mul_pos hx hDm1
  rw [uFromDelta_div_degree d (by omega) δ]
  change x * δ / (1 + x * δ) ≤ 1 / D ↔
    δ ≤ 1 / (x * (D - 1))
  rw [div_le_div_iff₀ hden hD, le_div_iff₀ hprod]
  constructor <;> intro h <;> nlinarith

/-- Equality of the two branches is equivalent to the displayed branch-point
formula. -/
theorem uFromDelta_branch_eq_iff (d : ℕ) (hd : 3 ≤ d) (δ : ℝ)
    (hδ : 0 ≤ δ) :
    uFromDelta d δ / (d : ℝ) = 1 / (Delta d : ℝ) ↔
      δ = branchPoint d := by
  let x : ℝ := d
  let D : ℝ := Delta d
  have hx : 0 < x := by dsimp [x]; positivity
  have hxThree : 3 ≤ x := by dsimp [x]; exact_mod_cast hd
  have hD : 0 < D := by
    dsimp [D]
    exact_mod_cast (lt_trans (by omega : 0 < d) (degree_lt_Delta d hd))
  have hxD : x < D := by
    dsimp [x, D]
    exact_mod_cast degree_lt_Delta d hd
  have hden : 0 < 1 + x * δ := by positivity
  have hDm1 : 0 < D - 1 := by linarith
  have hprod : 0 < x * (D - 1) := mul_pos hx hDm1
  rw [uFromDelta_div_degree d (by omega) δ]
  change x * δ / (1 + x * δ) = 1 / D ↔
    δ = 1 / (x * (D - 1))
  rw [div_eq_div_iff hden.ne' hD.ne', eq_div_iff hprod.ne']
  constructor <;> intro h <;> nlinarith

/-- The branch point is positive in every degree considered in the paper. -/
theorem branchPoint_pos (d : ℕ) (hd : 3 ≤ d) : 0 < branchPoint d := by
  have hdPos : 0 < (d : ℝ) := by positivity
  have hDelta : (1 : ℝ) < Delta d := by
    exact_mod_cast (lt_trans (by omega : 1 < d) (degree_lt_Delta d hd))
  exact one_div_pos.mpr (mul_pos hdPos (sub_pos.mpr hDelta))

/-- Substitution of the branch point makes the two branches equal. -/
theorem uFromDelta_at_branchPoint (d : ℕ) (hd : 3 ≤ d) :
    uFromDelta d (branchPoint d) / (d : ℝ) = 1 / (Delta d : ℝ) := by
  apply (uFromDelta_branch_eq_iff d hd (branchPoint d)
    (branchPoint_pos d hd).le).2
  rfl

/-! ## Baker's numerical checks -/

/-- Baker's constant `rho = 0.4079 / (k(k-1))`, written exactly. -/
def bakerRho (k : ℕ) : ℝ :=
  ((4079 : ℝ) / 10000) / ((k : ℝ) * ((k : ℝ) - 1))

/-- The first Type I/II numerical condition used after replacing Baker's
denominator by `k(k-1)`. -/
theorem bakerRho_mul_factor_lt (k : ℕ) (hk : 6 ≤ k) :
    bakerRho k * ((5 : ℝ) / 2 - 3 / (2 * (k : ℝ))) <
      1 / (2 * (k : ℝ)) := by
  let x : ℝ := k
  have hx6 : 6 ≤ x := by dsimp [x]; exact_mod_cast hk
  have hx : 0 < x := by linarith
  have hx1 : 0 < x - 1 := by linarith
  have hden : 0 < x * (x - 1) := mul_pos hx hx1
  have hnonneg : 0 ≤ x * (x - 6) :=
    mul_nonneg hx.le (sub_nonneg.mpr hx6)
  have hfive : 5 * x ≤ x * (x - 1) := by nlinarith
  have hsmall : ((4079 : ℝ) / 10000) * (5 * x - 3) < 5 * x := by
    norm_num
    linarith
  have hmain : ((4079 : ℝ) / 10000) * (5 * x - 3) < x * (x - 1) :=
    hsmall.trans_le hfive
  have hrhoA :
      (((4079 : ℝ) / 10000) / (x * (x - 1))) * (5 * x - 3) < 1 := by
    rw [div_mul_eq_mul_div, div_lt_one hden]
    exact hmain
  have hfactor :
      (5 : ℝ) / 2 - 3 / (2 * x) = (5 * x - 3) / (2 * x) := by
    field_simp
  change (((4079 : ℝ) / 10000) / (x * (x - 1))) *
      ((5 : ℝ) / 2 - 3 / (2 * x)) < 1 / (2 * x)
  rw [hfactor, ← mul_div_assoc]
  exact (div_lt_div_iff_of_pos_right (by positivity : 0 < 2 * x)).2 hrhoA

/-- The second Type I/II numerical condition used after replacing Baker's
denominator by `k(k-1)`. -/
theorem bakerRho_lt_three_mul_div (k : ℕ) (hk : 6 ≤ k) :
    bakerRho k < 3 * (k : ℝ) / (20 * (k : ℝ) + 5) := by
  let x : ℝ := k
  have hx6 : 6 ≤ x := by dsimp [x]; exact_mod_cast hk
  have hx : 0 < x := by linarith
  have hx1 : 0 < x - 1 := by linarith
  have hden : 0 < x * (x - 1) := mul_pos hx hx1
  have hright : 0 < 20 * x + 5 := by positivity
  have hnonneg : 0 ≤ x * (x - 6) :=
    mul_nonneg hx.le (sub_nonneg.mpr hx6)
  have hfive : 5 * x ≤ x * (x - 1) := by nlinarith
  have hcoef :
      ((4079 : ℝ) / 10000) * (20 * x + 5) < 20 * x + 5 := by
    norm_num
    linarith
  have hquad : 20 * x + 5 < 15 * x ^ 2 := by nlinarith
  have hcross :
      ((4079 : ℝ) / 10000) * (20 * x + 5) <
        (3 * x) * (x * (x - 1)) := by
    calc
      ((4079 : ℝ) / 10000) * (20 * x + 5) < 20 * x + 5 := hcoef
      _ < 15 * x ^ 2 := hquad
      _ = (3 * x) * (5 * x) := by ring
      _ ≤ (3 * x) * (x * (x - 1)) :=
        mul_le_mul_of_nonneg_left hfive (by positivity)
  change ((4079 : ℝ) / 10000) / (x * (x - 1)) <
    3 * x / (20 * x + 5)
  exact (div_lt_div_iff₀ hden hright).2 hcross

end

end ImprovedWeylBounds
