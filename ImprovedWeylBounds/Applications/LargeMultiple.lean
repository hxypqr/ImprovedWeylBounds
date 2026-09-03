import ImprovedWeylBounds.External.Statements

/-!
# The averaging step after Baker's large-multiple lemma

The cited large-multiple lemma supplies a lower bound for a sum over
`1 ≤ m ≤ M`.  The paper then selects one large summand.  That selection is
an internal finite argument and is checked here.
-/

open scoped BigOperators

namespace ImprovedWeylBounds
namespace Applications

noncomputable section

/-- The canonical equivalence between zero-based indices and the interval
of natural numbers `{1, …, N}` used by `g`. -/
def finEquivIccOne (N : ℕ) : Fin N ≃ {n : ℕ // n ∈ Finset.Icc 1 N} where
  toFun i := ⟨i.val + 1, by simp⟩
  invFun n := ⟨n.val - 1, by
    have hn := Finset.mem_Icc.mp n.property
    omega⟩
  left_inv i := by
    apply Fin.ext
    simp
  right_inv n := by
    apply Subtype.ext
    dsimp
    have hn := (Finset.mem_Icc.mp n.property).1
    omega

/-- Reindex a sum over `{1, …, N}` by `Fin N`. -/
theorem sum_Icc_one_eq_sum_fin {R : Type*} [AddCommMonoid R]
    (N : ℕ) (f : ℕ → R) :
    ∑ n ∈ Finset.Icc 1 N, f n = ∑ i : Fin N, f (i.val + 1) := by
  rw [← Finset.sum_attach]
  exact (Fintype.sum_equiv (finEquivIccOne N) _ _ fun _ => rfl).symm

/-- Multiplying every coefficient by `m` multiplies the polynomial phase by
`m`. -/
theorem nonconstantPhase_scale
    {k : ℕ} (α : CoefficientVector k) (m : ℕ) (n : ℕ) :
    nonconstantPhase (fun j => (m : ℝ) * α j) n =
      (m : ℝ) * nonconstantPhase α n := by
  simp only [nonconstantPhase, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The finite sequence used by the external large-multiple lemma produces
exactly the coefficient-scaled Weyl sum. -/
theorem phase_large_multiple_sum_eq_g
    {k : ℕ} (α : CoefficientVector k) (N m : ℕ) :
    (∑ n : Fin N,
        e ((m : ℝ) * nonconstantPhase α (n.val + 1))) =
      g (fun j => (m : ℝ) * α j) N := by
  rw [g, sum_Icc_one_eq_sum_fin]
  apply Finset.sum_congr rfl
  intro n _
  rw [nonconstantPhase_scale]

/-- A sum of `M` nonnegative terms exceeding `N/6` has one term exceeding
`N/(6M)`. -/
theorem exists_term_gt_average_six
    (N M : ℕ) (hM : 1 ≤ M) (F : ℕ → ℝ)
    (hlarge : (N : ℝ) / 6 < ∑ m ∈ Finset.Icc 1 M, F m) :
    ∃ m ∈ Finset.Icc 1 M, (N : ℝ) / (6 * M) < F m := by
  by_contra hnot
  push Not at hnot
  have hsum :
      ∑ m ∈ Finset.Icc 1 M, F m ≤
        ∑ _m ∈ Finset.Icc 1 M, (N : ℝ) / (6 * M) := by
    exact Finset.sum_le_sum fun m hm => hnot m hm
  have hcard : (Finset.Icc 1 M).card = M := by
    simp
  have hconst :
      ∑ _m ∈ Finset.Icc 1 M, (N : ℝ) / (6 * M) = (N : ℝ) / 6 := by
    rw [Finset.sum_const, nsmul_eq_mul, hcard]
    have hM0 : (M : ℝ) ≠ 0 := by positivity
    field_simp
  rw [hconst] at hsum
  exact (not_le_of_gt hlarge) hsum

/-- Exact consequence of the external large-multiple lemma used at the
start of the small-fractional-parts proof. -/
theorem exists_large_multiple
    (hLargeMultiple : External.LargeMultiple)
    (N M : ℕ) (hN : 1 ≤ N) (hM : 2 ≤ M) (x : Fin N → ℝ)
    (haway : ∀ n : Fin N, 1 / (M : ℝ) < distToInt (x n)) :
    ∃ m ∈ Finset.Icc 1 M,
      (N : ℝ) / (6 * M) < ‖∑ n : Fin N, e ((m : ℝ) * x n)‖ := by
  have hsum := hLargeMultiple N M hN hM x haway
  exact exists_term_gt_average_six N M (by omega)
    (fun m => ‖∑ n : Fin N, e ((m : ℝ) * x n)‖) hsum

/-- Polynomial-phase form of the averaging step, now expressed with the
paper's Weyl sum `g`. -/
theorem exists_large_scaled_weyl_sum
    (hLargeMultiple : External.LargeMultiple)
    {k : ℕ} (α : CoefficientVector k)
    (N M : ℕ) (hN : 1 ≤ N) (hM : 2 ≤ M)
    (haway : ∀ n : Fin N,
      1 / (M : ℝ) < distToInt (nonconstantPhase α (n.val + 1))) :
    ∃ m ∈ Finset.Icc 1 M,
      (N : ℝ) / (6 * M) < ‖g (fun j => (m : ℝ) * α j) N‖ := by
  obtain ⟨m, hm, hlarge⟩ := exists_large_multiple hLargeMultiple N M hN hM
    (fun n => nonconstantPhase α (n.val + 1)) haway
  refine ⟨m, hm, ?_⟩
  simpa only [phase_large_multiple_sum_eq_g] using hlarge

end

end Applications
end ImprovedWeylBounds
