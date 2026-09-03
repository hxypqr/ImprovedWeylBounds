import ImprovedWeylBounds.Asymptotics
import ImprovedWeylBounds.Conditional.SmallFractionalParts
import ImprovedWeylBounds.ExponentArithmetic

/-!
# Small fractional parts: the complete parameter assembly

This file expands the asymptotic bookkeeping in the proof of Theorem 1.4 of
the manuscript.  The only two analytic inputs are the explicitly stated
external large-multiple lemma and an `InversePrinciple` at denominator
`Delta k`.  In particular, the floor in

`M = floor (N ^ (1 / Delta k - epsilon / 2))`

and all three constant absorptions are kept in the theorem proof.
-/

open Filter
open scoped BigOperators

namespace ImprovedWeylBounds
namespace Conditional

open External Applications

noncomputable section

/-- The integer cutoff used in the contradiction argument for small
fractional parts. -/
def smallFractionalPartsCutoff (k N : ℕ) (ε : ℝ) : ℕ :=
  ⌊Real.rpow (N : ℝ) (1 / (Delta k : ℝ) - ε / 2)⌋₊

/-- Once a nonnegative real number is at least two, its natural floor is at
least half of it.  This is the only loss caused by the floor in `M`. -/
private theorem half_le_natFloor {x : ℝ} (hx : 2 ≤ x) :
    x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have hlt : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  have hhalf : x / 2 ≤ x - 1 := by linarith
  linarith

/-- The real-power identity used after bounding `n = qm` by `N`. -/
private theorem polynomial_error_power_identity
    {N k j : ℕ} {β η : ℝ} (hN : 0 < N) :
    (N : ℝ) ^ j *
        (((6 : ℝ) * Real.rpow (N : ℝ) β) ^ k *
          Real.rpow (N : ℝ) (-((j + 1 : ℕ) : ℝ) + η)) =
      (6 : ℝ) ^ k *
        Real.rpow (N : ℝ) (β * (k : ℝ) - 1 + η) := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  simp only [Real.rpow_eq_pow]
  rw [mul_pow, ← Real.rpow_mul_natCast hNr.le β k]
  rw [← Real.rpow_natCast (N : ℝ) j]
  calc
    (N : ℝ) ^ (j : ℝ) *
        ((6 : ℝ) ^ k * (N : ℝ) ^ (β * (k : ℝ)) *
          (N : ℝ) ^ (-((j + 1 : ℕ) : ℝ) + η)) =
      (6 : ℝ) ^ k *
        ((N : ℝ) ^ (j : ℝ) *
          ((N : ℝ) ^ (β * (k : ℝ)) *
            (N : ℝ) ^ (-((j + 1 : ℕ) : ℝ) + η))) := by
      ring
    _ = (6 : ℝ) ^ k *
        (N : ℝ) ^
          ((j : ℝ) + (β * (k : ℝ) + (-((j + 1 : ℕ) : ℝ) + η))) := by
      rw [← Real.rpow_add hNr, ← Real.rpow_add hNr]
    _ = (6 : ℝ) ^ k *
        (N : ℝ) ^ (β * (k : ℝ) - 1 + η) := by
      congr 2
      push_cast
      ring

/-- Fully quantified asymptotic form of the manuscript's small-fractional-
parts theorem.  The conclusion has constant `1` after enlarging the
large-`N` threshold; this is equivalent to the stated Vinogradov bound.

All internal steps are proved here.  The hypotheses record exactly the two
analytic inputs that remain outside this proof. -/
theorem smallFractionalParts_eventually
    (hLargeMultiple : LargeMultiple) {k : ℕ} (hk : 3 ≤ k)
    (hInverse : InversePrinciple k (Delta k))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ α : CoefficientVector k,
      ∃ n ∈ Finset.Icc 1 N,
        distToInt (nonconstantPhase α n) ≤
          Real.rpow (N : ℝ) (-1 / (Delta k : ℝ) + ε) := by
  have hDnat : 0 < Delta k :=
    lt_trans (by omega : 0 < k) (degree_lt_Delta k hk)
  have hD : 0 < (Delta k : ℝ) := by exact_mod_cast hDnat
  have hkDnat : k + 1 ≤ Delta k := degree_add_one_le_Delta k hk
  have hkD : ((k + 1 : ℕ) : ℝ) / (Delta k : ℝ) ≤ 1 := by
    rw [div_le_one hD]
    exact_mod_cast hkDnat
  by_cases hεlarge : 1 / (Delta k : ℝ) ≤ ε
  · have htarget_nonneg : 0 ≤ -1 / (Delta k : ℝ) + ε := by
      have hneg := neg_le_neg hεlarge
      calc
        0 = -ε + ε := by ring
        _ ≤ -(1 / (Delta k : ℝ)) + ε := by
          simpa [add_comm] using add_le_add_right hneg ε
        _ = -1 / (Delta k : ℝ) + ε := by ring
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    intro α
    refine ⟨1, by simp [hN], ?_⟩
    calc
      distToInt (nonconstantPhase α 1) ≤ 1 / 2 := distToInt_le_half _
      _ ≤ 1 := by norm_num
      _ ≤ Real.rpow (N : ℝ) (-1 / (Delta k : ℝ) + ε) :=
        Real.one_le_rpow (by exact_mod_cast hN) htarget_nonneg
  · have hεsmall : ε < 1 / (Delta k : ℝ) := lt_of_not_ge hεlarge
    let β : ℝ := 1 / (Delta k : ℝ) - ε / 2
    let γ : ℝ := 1 / (Delta k : ℝ) - ε / 4
    let η : ℝ := ε / 8
    let ν : ℝ := β * ((k + 1 : ℕ) : ℝ) + η
    let ω : ℝ := β * (k : ℝ) - 1 + η
    let θ : ℝ := -1 / (Delta k : ℝ) + ε
    have hβ : 0 < β := by
      dsimp [β]
      nlinarith
    have hγ : 0 < γ := by
      dsimp [γ]
      nlinarith
    have hη : 0 < η := by
      dsimp [η]
      linarith
    have hβγ : β < γ := by
      dsimp [β, γ]
      linarith
    have hnegβθ : -β < θ := by
      apply sub_pos.mp
      rw [show θ - (-β) = ε / 2 by
        dsimp [β, θ]
        ring]
      positivity
    have hν : ν < 1 := by
      have hk1pos : 0 < (((k + 1 : ℕ) : ℝ)) := by positivity
      have hstrict :
          ν < ((k + 1 : ℕ) : ℝ) / (Delta k : ℝ) := by
        have hone : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
          exact_mod_cast (show 1 ≤ k + 1 by omega)
        have hsmall : ε / 8 < ε / 2 := by linarith
        have hmul : ε / 2 ≤ ε / 2 * ((k + 1 : ℕ) : ℝ) := by
          exact (le_mul_iff_one_le_right (by positivity : 0 < ε / 2)).2 hone
        dsimp [ν, β, η]
        rw [sub_mul, one_div_mul_eq_div]
        linarith
      exact hstrict.trans_le hkD
    have hωθ : ω < θ := by
      have hkpos : 0 < (k : ℝ) := by positivity
      have hratio :
          (k : ℝ) / (Delta k : ℝ) - 1 ≤
            -1 / (Delta k : ℝ) := by
        have hsum :
            (k : ℝ) / (Delta k : ℝ) + 1 / (Delta k : ℝ) ≤ 1 := by
          calc
            (k : ℝ) / (Delta k : ℝ) + 1 / (Delta k : ℝ) =
                ((k + 1 : ℕ) : ℝ) / (Delta k : ℝ) := by
              push_cast
              ring
            _ ≤ 1 := hkD
        have htmp :
            (k : ℝ) / (Delta k : ℝ) ≤
              1 - 1 / (Delta k : ℝ) :=
          (le_sub_iff_add_le).2 hsum
        have htmp' := sub_le_sub_right htmp 1
        convert htmp' using 1 <;> ring
      have hnonneg : 0 ≤ ε / 2 * (k : ℝ) := by positivity
      dsimp [ω, β, η, θ]
      rw [sub_mul, one_div_mul_eq_div]
      linarith
    obtain ⟨C, hC, N₀, hN₀, hmain⟩ :=
      largeMultiple_to_simultaneousApproximation
        hLargeMultiple hInverse (ε / 4) η (by positivity) hη
    let Cn : ℝ := C * (6 : ℝ) ^ k
    have hCn : 0 < Cn := by
      dsimp [Cn]
      positivity
    have hCutoffLarge :
        ∀ᶠ N : ℕ in atTop, (2 : ℝ) < Real.rpow (N : ℝ) β := by
      filter_upwards [eventually_const_mul_rpow_lt_rpow 2 0 β hβ]
        with N hN
      simpa using hN
    have hThresholdPower :
        ∀ᶠ N : ℕ in atTop,
          6 * Real.rpow (N : ℝ) β < Real.rpow (N : ℝ) γ :=
      eventually_const_mul_rpow_lt_rpow 6 β γ hβγ
    have hFloorReciprocal :
        ∀ᶠ N : ℕ in atTop,
          2 * Real.rpow (N : ℝ) (-β) < Real.rpow (N : ℝ) θ :=
      eventually_const_mul_rpow_lt_rpow 2 (-β) θ hnegβθ
    have hNAbsorb :
        ∀ᶠ N : ℕ in atTop,
          Cn * Real.rpow (N : ℝ) ν ≤ Real.rpow (N : ℝ) 1 :=
      eventually_const_mul_rpow_le_rpow Cn ν 1 hν
    have hErrorAbsorb :
        ∀ᶠ N : ℕ in atTop,
          ((k : ℝ) * Cn) * Real.rpow (N : ℝ) ω ≤
            Real.rpow (N : ℝ) θ :=
      eventually_const_mul_rpow_le_rpow ((k : ℝ) * Cn) ω θ hωθ
    filter_upwards [eventually_ge_atTop N₀, eventually_ge_atTop (1 : ℕ),
        hCutoffLarge, hThresholdPower, hFloorReciprocal, hNAbsorb,
        hErrorAbsorb] with N hNN₀ hNone hCutoffLargeN hThresholdPowerN
          hFloorReciprocalN hNAbsorbN hErrorAbsorbN
    intro α
    let M : ℕ := smallFractionalPartsCutoff k N ε
    have hNr : 0 < (N : ℝ) := by exact_mod_cast hNone
    have hpowerPos : 0 < Real.rpow (N : ℝ) β :=
      Real.rpow_pos_of_pos hNr β
    have hMtwo : 2 ≤ M := by
      change 2 ≤ ⌊Real.rpow (N : ℝ) β⌋₊
      exact Nat.le_floor hCutoffLargeN.le
    have hMpos : 0 < (M : ℝ) := by positivity
    have hMupper : (M : ℝ) ≤ Real.rpow (N : ℝ) β := by
      change (⌊Real.rpow (N : ℝ) β⌋₊ : ℝ) ≤ Real.rpow (N : ℝ) β
      exact Nat.floor_le hpowerPos.le
    have hMlower : Real.rpow (N : ℝ) β / 2 ≤ (M : ℝ) := by
      change Real.rpow (N : ℝ) β / 2 ≤
        (⌊Real.rpow (N : ℝ) β⌋₊ : ℝ)
      exact half_le_natFloor hCutoffLargeN.le
    have hSixM : 6 * (M : ℝ) < Real.rpow (N : ℝ) γ :=
      (mul_le_mul_of_nonneg_left hMupper (by norm_num)).trans_lt
        hThresholdPowerN
    have hthreshold :
        Real.rpow (N : ℝ)
            (1 - 1 / (Delta k : ℝ) + ε / 4) <
          (N : ℝ) / (6 * M) := by
      have hexp :
          1 - 1 / (Delta k : ℝ) + ε / 4 = 1 - γ := by
        dsimp [γ]
        ring
      rw [hexp]
      have hsub :
          Real.rpow (N : ℝ) (1 - γ) =
            (N : ℝ) / Real.rpow (N : ℝ) γ := by
        simpa only [Real.rpow_eq_pow, Real.rpow_one] using
          Real.rpow_sub hNr 1 γ
      rw [hsub]
      exact (div_lt_div_iff_of_pos_left hNr
        (Real.rpow_pos_of_pos hNr γ)
        (by positivity : 0 < (6 : ℝ) * M)).2 hSixM
    have hInvM :
        1 / (M : ℝ) ≤ 2 * Real.rpow (N : ℝ) (-β) := by
      have hxTwoM : Real.rpow (N : ℝ) β ≤ 2 * (M : ℝ) := by
        linarith
      calc
        1 / (M : ℝ) ≤ 2 / Real.rpow (N : ℝ) β := by
          exact (div_le_div_iff₀ hMpos hpowerPos).2 (by simpa using hxTwoM)
        _ = 2 * Real.rpow (N : ℝ) (-β) := by
          have hnegpow :
              Real.rpow (N : ℝ) (-β) =
                (Real.rpow (N : ℝ) β)⁻¹ :=
            Real.rpow_neg hNr.le β
          rw [hnegpow]
          simp only [div_eq_mul_inv]
    by_contra hno
    push Not at hno
    have haway : ∀ i : Fin N,
        1 / (M : ℝ) <
          distToInt (nonconstantPhase α (i.val + 1)) := by
      intro i
      have hi : i.val + 1 ∈ Finset.Icc 1 N := by simp
      exact (hInvM.trans_lt hFloorReciprocalN).trans (hno _ hi)
    obtain ⟨m, hm, ⟨approx⟩⟩ :=
      hmain N M hNN₀ hMtwo hthreshold α haway
    have hmBounds := Finset.mem_Icc.mp hm
    have hmPos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one hmBounds.1
    have hmM : m ≤ M := hmBounds.2
    have hmCast : (m : ℝ) ≤ (M : ℝ) := by exact_mod_cast hmM
    have hratio :
        (N : ℝ) / ((N : ℝ) / (6 * (M : ℝ))) = 6 * (M : ℝ) := by
      field_simp
    have hq := approx.denominator_bound
    rw [hratio] at hq
    have hqmRaw :
        ((approx.q * m : ℕ) : ℝ) ≤
          Cn * (M : ℝ) ^ (k + 1) * Real.rpow (N : ℝ) η := by
      calc
        ((approx.q * m : ℕ) : ℝ) = (approx.q : ℝ) * (m : ℝ) := by
          norm_num
        _ ≤ (C * ((6 : ℝ) * M) ^ k * Real.rpow (N : ℝ) η) *
              (m : ℝ) :=
          mul_le_mul_of_nonneg_right hq (by positivity)
        _ ≤ (C * ((6 : ℝ) * M) ^ k * Real.rpow (N : ℝ) η) *
              (M : ℝ) := by
          apply mul_le_mul_of_nonneg_left hmCast
          exact mul_nonneg
            (mul_nonneg hC.le (pow_nonneg (by positivity) k))
            (Real.rpow_nonneg hNr.le η)
        _ = Cn * (M : ℝ) ^ (k + 1) * Real.rpow (N : ℝ) η := by
          dsimp [Cn]
          rw [mul_pow, pow_succ]
          ring
    have hMpowSucc :
        (M : ℝ) ^ (k + 1) ≤
          (Real.rpow (N : ℝ) β) ^ (k + 1) := by
      gcongr
    have hqmPower :
        ((approx.q * m : ℕ) : ℝ) ≤
          Cn * Real.rpow (N : ℝ) ν := by
      calc
        ((approx.q * m : ℕ) : ℝ) ≤
            Cn * (M : ℝ) ^ (k + 1) * Real.rpow (N : ℝ) η := hqmRaw
        _ ≤ Cn * (Real.rpow (N : ℝ) β) ^ (k + 1) *
              Real.rpow (N : ℝ) η := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hMpowSucc hCn.le)
            (Real.rpow_nonneg hNr.le η)
        _ = Cn * Real.rpow (N : ℝ) ν := by
          have hpow :
              (Real.rpow (N : ℝ) β) ^ (k + 1) =
                Real.rpow (N : ℝ) (β * (((k + 1 : ℕ) : ℝ))) := by
            rw [← Real.rpow_natCast]
            exact (Real.rpow_mul hNr.le β (((k + 1 : ℕ) : ℝ))).symm
          rw [hpow]
          simp only [Real.rpow_eq_pow]
          calc
            Cn * (N : ℝ) ^ (β * ((k + 1 : ℕ) : ℝ)) *
                (N : ℝ) ^ η =
              Cn * ((N : ℝ) ^ (β * ((k + 1 : ℕ) : ℝ)) *
                (N : ℝ) ^ η) := by ring
            _ = Cn * (N : ℝ) ^
                (β * ((k + 1 : ℕ) : ℝ) + η) := by
              rw [← Real.rpow_add hNr]
            _ = Cn * (N : ℝ) ^ ν := rfl
    have hqmCast : ((approx.q * m : ℕ) : ℝ) ≤ (N : ℝ) := by
      calc
        ((approx.q * m : ℕ) : ℝ) ≤ Cn * Real.rpow (N : ℝ) ν := hqmPower
        _ ≤ Real.rpow (N : ℝ) 1 := hNAbsorbN
        _ = (N : ℝ) := Real.rpow_one _
    have hqmNat : approx.q * m ≤ N := by exact_mod_cast hqmCast
    have hqmPos : 0 < approx.q * m := Nat.mul_pos approx.q_pos hmPos
    have hpoly :=
      distToInt_polynomial_at_denominator_multiple_le α m approx
    have hterm : ∀ j : Fin k,
        (((approx.q * m : ℕ) : ℝ) ^ j.val *
            (C * (((N : ℝ) / ((N : ℝ) / (6 * (M : ℝ)))) ^ k) *
              Real.rpow (N : ℝ)
                (-((j.val + 1 : ℕ) : ℝ) + η))) ≤
          Cn * Real.rpow (N : ℝ) ω := by
      intro j
      rw [hratio]
      have hqmpow :
          (((approx.q * m : ℕ) : ℝ) ^ j.val) ≤ (N : ℝ) ^ j.val := by
        gcongr
      calc
        (((approx.q * m : ℕ) : ℝ) ^ j.val *
            (C * ((6 : ℝ) * M) ^ k *
              Real.rpow (N : ℝ) (-((j.val + 1 : ℕ) : ℝ) + η)))
            ≤ (N : ℝ) ^ j.val *
              (C * ((6 : ℝ) * M) ^ k *
                Real.rpow (N : ℝ) (-((j.val + 1 : ℕ) : ℝ) + η)) := by
          apply mul_le_mul_of_nonneg_right hqmpow
          exact mul_nonneg
            (mul_nonneg hC.le (pow_nonneg (by positivity) k))
            (Real.rpow_nonneg hNr.le _)
        _ ≤ (N : ℝ) ^ j.val *
              (C * ((6 : ℝ) * Real.rpow (N : ℝ) β) ^ k *
                Real.rpow (N : ℝ) (-((j.val + 1 : ℕ) : ℝ) + η)) := by
          apply mul_le_mul_of_nonneg_left
          · apply mul_le_mul_of_nonneg_right
            · exact mul_le_mul_of_nonneg_left
                (pow_le_pow_left₀ (by positivity : 0 ≤ (6 : ℝ) * M)
                  (mul_le_mul_of_nonneg_left hMupper (by norm_num)) k)
                hC.le
            · exact Real.rpow_nonneg hNr.le _
          · exact pow_nonneg (Nat.cast_nonneg N) j.val
        _ = Cn * Real.rpow (N : ℝ) ω := by
          have hid := polynomial_error_power_identity (N := N) (k := k)
            (j := j.val) (β := β) (η := η) (by omega)
          simp only [Real.rpow_eq_pow] at hid ⊢
          rw [show
            (N : ℝ) ^ j.val *
                (C * ((6 : ℝ) * (N : ℝ) ^ β) ^ k *
                  (N : ℝ) ^ (-((j.val + 1 : ℕ) : ℝ) + η)) =
              C * ((N : ℝ) ^ j.val *
                (((6 : ℝ) * (N : ℝ) ^ β) ^ k *
                  (N : ℝ) ^ (-((j.val + 1 : ℕ) : ℝ) + η))) by ring]
          rw [hid]
          dsimp [Cn, ω]
          ring
    have hfinal :
        distToInt (nonconstantPhase α (approx.q * m)) ≤
          Real.rpow (N : ℝ) θ := by
      calc
        distToInt (nonconstantPhase α (approx.q * m)) ≤
            ∑ j : Fin k,
              ((approx.q * m : ℕ) : ℝ) ^ j.val *
                (C * (((N : ℝ) / ((N : ℝ) / (6 * (M : ℝ)))) ^ k) *
                  Real.rpow (N : ℝ)
                    (-((j.val + 1 : ℕ) : ℝ) + η)) := hpoly
        _ ≤ ∑ _j : Fin k, Cn * Real.rpow (N : ℝ) ω := by
          exact Finset.sum_le_sum fun j _ ↦ hterm j
        _ = ((k : ℝ) * Cn) * Real.rpow (N : ℝ) ω := by
          simp
          ring
        _ ≤ Real.rpow (N : ℝ) θ := hErrorAbsorbN
    have hmem : approx.q * m ∈ Finset.Icc 1 N :=
      Finset.mem_Icc.mpr ⟨hqmPos, hqmNat⟩
    have hfinal' :
        distToInt (nonconstantPhase α (approx.q * m)) ≤
          Real.rpow (N : ℝ) (-1 / (Delta k : ℝ) + ε) := by
      simpa only [θ] using hfinal
    exact (not_lt_of_ge hfinal') (hno _ hmem)

/-- Explicit large-`N` version of `smallFractionalParts_eventually`. -/
theorem smallFractionalParts
    (hLargeMultiple : LargeMultiple) {k : ℕ} (hk : 3 ≤ k)
    (hInverse : InversePrinciple k (Delta k))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ α : CoefficientVector k,
      ∃ n ∈ Finset.Icc 1 N,
        distToInt (nonconstantPhase α n) ≤
          Real.rpow (N : ℝ) (-1 / (Delta k : ℝ) + ε) := by
  simpa only [eventually_atTop] using
    smallFractionalParts_eventually hLargeMultiple hk hInverse hε

/-- Literal all-`N` Vinogradov-notation form of Theorem 1.4.  The finitely
many values below the analytic threshold are covered by the universal bound
`distToInt x ≤ 1/2`; no additional number-theoretic input is used. -/
theorem smallFractionalParts_all
    (hLargeMultiple : LargeMultiple) {k : ℕ} (hk : 3 ≤ k)
    (hInverse : InversePrinciple k (Delta k))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 1 ≤ N → ∀ α : CoefficientVector k,
      ∃ n ∈ Finset.Icc 1 N,
        distToInt (nonconstantPhase α n) ≤
          C * Real.rpow (N : ℝ) (-1 / (Delta k : ℝ) + ε) := by
  obtain ⟨N₀, hlarge⟩ :=
    smallFractionalParts hLargeMultiple hk hInverse hε
  let C : ℝ := max 1 (N₀ : ℝ)
  have hC : 0 < C := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hCone : 1 ≤ C := le_max_left _ _
  refine ⟨C, hC, ?_⟩
  intro N hN α
  by_cases hNlarge : N₀ ≤ N
  · obtain ⟨n, hn, hbound⟩ := hlarge N hNlarge α
    refine ⟨n, hn, hbound.trans ?_⟩
    calc
      Real.rpow (N : ℝ) (-1 / (Delta k : ℝ) + ε) =
          1 * Real.rpow (N : ℝ) (-1 / (Delta k : ℝ) + ε) := by ring
      _ ≤ C * Real.rpow (N : ℝ) (-1 / (Delta k : ℝ) + ε) := by
        exact mul_le_mul_of_nonneg_right hCone (Real.rpow_nonneg (by positivity) _)
  · have hNlt : N < N₀ := lt_of_not_ge hNlarge
    have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (by norm_num) hNreal
    have hNC : (N : ℝ) ≤ C := by
      exact (by exact_mod_cast (Nat.le_of_lt hNlt) : (N : ℝ) ≤ N₀).trans
        (le_max_right _ _)
    have hDnat : 1 ≤ Delta k := by
      exact (Nat.succ_le_iff.mpr (lt_trans (by omega : 0 < k)
        (degree_lt_Delta k hk)))
    have hDreal : (1 : ℝ) ≤ Delta k := by exact_mod_cast hDnat
    have hDpos : (0 : ℝ) < Delta k := lt_of_lt_of_le (by norm_num) hDreal
    have htheta : (-1 : ℝ) ≤ -1 / (Delta k : ℝ) + ε := by
      have honeDiv : 1 / (Delta k : ℝ) ≤ 1 := (div_le_one hDpos).2 hDreal
      have hneg : (-1 : ℝ) ≤ -1 / (Delta k : ℝ) := by
        calc
          (-1 : ℝ) ≤ -(1 / (Delta k : ℝ)) := neg_le_neg honeDiv
          _ = -1 / (Delta k : ℝ) := by ring
      exact hneg.trans (le_add_of_nonneg_right hε.le)
    have hpow : Real.rpow (N : ℝ) (-1 : ℝ) ≤
        Real.rpow (N : ℝ) (-1 / (Delta k : ℝ) + ε) :=
      Real.rpow_le_rpow_of_exponent_le hNreal htheta
    have hone : 1 ≤ C * Real.rpow (N : ℝ) (-1 : ℝ) := by
      rw [show Real.rpow (N : ℝ) (-1 : ℝ) = (N : ℝ)⁻¹ by
        change (N : ℝ) ^ (-1 : ℝ) = (N : ℝ)⁻¹
        exact Real.rpow_neg_one _]
      calc
        1 = (N : ℝ) * (N : ℝ)⁻¹ := by
          exact (mul_inv_cancel₀ hNpos.ne').symm
        _ ≤ C * (N : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right hNC (inv_nonneg.mpr hNpos.le)
    refine ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hN⟩, ?_⟩
    calc
      distToInt (nonconstantPhase α 1) ≤ 1 / 2 := distToInt_le_half _
      _ ≤ 1 := by norm_num
      _ ≤ C * Real.rpow (N : ℝ) (-1 : ℝ) := hone
      _ ≤ C * Real.rpow (N : ℝ) (-1 / (Delta k : ℝ) + ε) :=
        mul_le_mul_of_nonneg_left hpow hC.le

end

end Conditional
end ImprovedWeylBounds
