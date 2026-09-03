import ImprovedWeylBounds.Basic

/-!
# Small asymptotic bookkeeping lemmas

The manuscript repeatedly absorbs a fixed constant into a positive gap
between two powers.  Here that convention is expanded into an actual
eventual statement on natural numbers.
-/

open Filter

namespace ImprovedWeylBounds

/-- A fixed multiple of a smaller real power is eventually strictly below a
larger real power. -/
theorem eventually_const_mul_rpow_lt_rpow (C a b : ℝ) (hab : a < b) :
    ∀ᶠ N : ℕ in atTop,
      C * Real.rpow (N : ℝ) a < Real.rpow (N : ℝ) b := by
  have hlim : Tendsto (fun N : ℕ ↦ Real.rpow (N : ℝ) (b - a)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hab)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually (eventually_gt_atTop C),
    eventually_ge_atTop (1 : ℕ)] with N hCN hN
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  calc
    C * Real.rpow (N : ℝ) a <
        Real.rpow (N : ℝ) (b - a) * Real.rpow (N : ℝ) a :=
      mul_lt_mul_of_pos_right hCN (Real.rpow_pos_of_pos hNpos _)
    _ = Real.rpow (N : ℝ) b := by
      calc
        Real.rpow (N : ℝ) (b - a) * Real.rpow (N : ℝ) a =
            Real.rpow (N : ℝ) ((b - a) + a) :=
          (Real.rpow_add hNpos (b - a) a).symm
        _ = Real.rpow (N : ℝ) b := by ring_nf

/-- Non-strict variant used when a later argument only asks for `≤`. -/
theorem eventually_const_mul_rpow_le_rpow (C a b : ℝ) (hab : a < b) :
    ∀ᶠ N : ℕ in atTop,
      C * Real.rpow (N : ℝ) a ≤ Real.rpow (N : ℝ) b :=
  (eventually_const_mul_rpow_lt_rpow C a b hab).mono fun _ h ↦ h.le

end ImprovedWeylBounds
