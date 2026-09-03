import ImprovedWeylBounds.External.Statements

/-!
# Translation invariance of Vinogradov systems

The fixed-leading-coefficient moment argument translates an arbitrary
integer interval to one beginning at `1`.  The manuscript explains that the
equal-power-sum equations survive this operation.  Here that binomial
argument is proved over the integers, in both directions.
-/

open scoped BigOperators

namespace ImprovedWeylBounds

/-- Two tuples have equal power sums in every positive degree at most `r`. -/
def EqualPowerSumsUpTo {s : ℕ} (r : ℕ) (x y : Fin s → ℤ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → n ≤ r → ∑ i, x i ^ n = ∑ i, y i ^ n

private theorem equalPowerSumsUpTo_add_const_forward
    {s r : ℕ} {x y : Fin s → ℤ}
    (h : EqualPowerSumsUpTo r x y) (c : ℤ) :
    EqualPowerSumsUpTo r (fun i => x i + c) (fun i => y i + c) := by
  intro n hn hnr
  simp_rw [add_pow]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hm0 : m = 0
  · subst m
    simp
  · have hmle : m ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hm)
    have hmp : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
    simp_rw [mul_assoc]
    rw [← Finset.sum_mul, h m hmp (hmle.trans hnr), Finset.sum_mul]

/-- Adding the same integer to every variable on both sides preserves, and
reflects, all Vinogradov equations up to degree `r`. -/
theorem equalPowerSumsUpTo_add_const_iff
    {s r : ℕ} (x y : Fin s → ℤ) (c : ℤ) :
    EqualPowerSumsUpTo r (fun i => x i + c) (fun i => y i + c) ↔
      EqualPowerSumsUpTo r x y := by
  constructor
  · intro h
    have hback := equalPowerSumsUpTo_add_const_forward h (-c)
    simpa only [add_assoc, add_neg_cancel, add_zero] using hback
  · intro h
    exact equalPowerSumsUpTo_add_const_forward h c

/-- Fin-indexed form matching `External.VinogradovSystem`: the equations for
the standard interval `{1, …, N}` are exactly the equations after translating
every variable by an arbitrary integer `c`. -/
theorem vinogradovSystem_iff_int_translate
    (s r N : ℕ) (x y : Fin s → Fin N) (c : ℤ) :
    External.VinogradovSystem s r N x y ↔
      EqualPowerSumsUpTo r
        (fun i => (x i).val.succ + c)
        (fun i => (y i).val.succ + c) := by
  rw [equalPowerSumsUpTo_add_const_iff]
  constructor
  · intro h n hn hnr
    have hnfin : n - 1 < r := by omega
    have heq := h ⟨n - 1, hnfin⟩
    have hnsucc : (n - 1).succ = n := by omega
    rw [hnsucc] at heq
    change ∑ i, ((x i).val.succ : ℤ) ^ n =
      ∑ i, ((y i).val.succ : ℤ) ^ n
    exact_mod_cast heq
  · intro h j
    have heq := h j.val.succ (by omega) (by omega)
    change ∑ i, ((x i).val.succ : ℤ) ^ j.val.succ =
      ∑ i, ((y i).val.succ : ℤ) ^ j.val.succ at heq
    exact_mod_cast heq

/-- Number of Vinogradov solutions in an integer translate of the standard
interval of length `N`. -/
noncomputable def translatedVinogradovMeanValue
    (s r N : ℕ) (c : ℤ) : ℕ := by
  classical
  exact Fintype.card
    {xy : (Fin s → Fin N) × (Fin s → Fin N) //
      EqualPowerSumsUpTo r
        (fun i => (xy.1 i).val.succ + c)
        (fun i => (xy.2 i).val.succ + c)}

/-- Translating the interval does not change the number of solutions of the
Vinogradov system. -/
theorem translatedVinogradovMeanValue_eq
    (s r N : ℕ) (c : ℤ) :
    translatedVinogradovMeanValue s r N c =
      External.vinogradovMeanValue s r N := by
  classical
  apply Fintype.card_congr
  exact
    { toFun := fun z =>
        ⟨z.1, (vinogradovSystem_iff_int_translate s r N z.1.1 z.1.2 c).2 z.2⟩
      invFun := fun z =>
        ⟨z.1, (vinogradovSystem_iff_int_translate s r N z.1.1 z.1.2 c).1 z.2⟩
      left_inv := fun z => by cases z; rfl
      right_inv := fun z => by cases z; rfl }

end ImprovedWeylBounds
