import ImprovedWeylBounds.Basic

/-!
# All cuts of a finite sum

The elementary core of Lemma 5.1 is independent of Weyl sums: at every cut,
the prefix or the complementary tail has at least half the size of the full
sum, and one of those two alternatives occurs for linearly many cuts.  This
file proves that statement exactly for an arbitrary complex sequence.
-/

open scoped BigOperators

namespace ImprovedWeylBounds

/-- Sum of the entries strictly before the cut `m`. -/
noncomputable def prefixAt {N : ℕ} (u : Fin N → ℂ) (m : Fin (N + 1)) : ℂ :=
  ∑ i : Fin N, if i.val < m.val then u i else 0

/-- Sum of the entries at or after the cut `m`. -/
noncomputable def tailAt {N : ℕ} (u : Fin N → ℂ) (m : Fin (N + 1)) : ℂ :=
  ∑ i : Fin N, if m.val ≤ i.val then u i else 0

/-- The uncut full sum. -/
noncomputable def totalSum {N : ℕ} (u : Fin N → ℂ) : ℂ :=
  ∑ i : Fin N, u i

theorem prefixAt_add_tailAt {N : ℕ} (u : Fin N → ℂ) (m : Fin (N + 1)) :
    prefixAt u m + tailAt u m = totalSum u := by
  classical
  simp only [prefixAt, tailAt, totalSum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : i.val < m.val
  · simp [h, not_le.mpr h]
  · have hm : m.val ≤ i.val := le_of_not_gt h
    simp [h, hm]

/-- At any cut, one of the two pieces has norm at least half the prescribed
lower bound for the norm of the full sum. -/
theorem large_prefix_or_tail {N : ℕ} (u : Fin N → ℂ) (m : Fin (N + 1))
    {A : ℝ} (hA : A ≤ ‖totalSum u‖) :
    A / 2 ≤ ‖prefixAt u m‖ ∨ A / 2 ≤ ‖tailAt u m‖ := by
  by_cases hp : A / 2 ≤ ‖prefixAt u m‖
  · exact Or.inl hp
  · right
    have hp' : ‖prefixAt u m‖ < A / 2 := lt_of_not_ge hp
    by_contra ht
    have ht' : ‖tailAt u m‖ < A / 2 := lt_of_not_ge ht
    have htriangle :
        ‖totalSum u‖ ≤ ‖prefixAt u m‖ + ‖tailAt u m‖ := by
      rw [← prefixAt_add_tailAt u m]
      exact norm_add_le _ _
    linarith

/-- Cuts at which the prefix is large. -/
noncomputable def largePrefixCuts {N : ℕ} (u : Fin N → ℂ) (A : ℝ) :
    Finset (Fin (N + 1)) := by
  classical
  exact Finset.univ.filter fun m => A / 2 ≤ ‖prefixAt u m‖

/-- Cuts at which the tail is large. -/
noncomputable def largeTailCuts {N : ℕ} (u : Fin N → ℂ) (A : ℝ) :
    Finset (Fin (N + 1)) := by
  classical
  exact Finset.univ.filter fun m => A / 2 ≤ ‖tailAt u m‖

/-- One orientation supplies at least half of all `N+1` cuts.

This is the exact finite pigeonhole step in `main.tex:849-865`, before the
optional subdivision into shorter blocks. -/
theorem exists_many_large_cuts {N : ℕ} (u : Fin N → ℂ) {A : ℝ}
    (hA : A ≤ ‖totalSum u‖) :
    (N + 1 ≤ 2 * (largePrefixCuts u A).card ∧
        ∀ m ∈ largePrefixCuts u A, A / 2 ≤ ‖prefixAt u m‖) ∨
      (N + 1 ≤ 2 * (largeTailCuts u A).card ∧
        ∀ m ∈ largeTailCuts u A, A / 2 ≤ ‖tailAt u m‖) := by
  classical
  let P := largePrefixCuts u A
  let T := largeTailCuts u A
  have hcover : P ∪ T = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro m
    have hm := large_prefix_or_tail u m hA
    rcases hm with hm | hm
    · exact Finset.mem_union_left _ (by simp [P, largePrefixCuts, hm])
    · exact Finset.mem_union_right _ (by simp [T, largeTailCuts, hm])
  have hcard : N + 1 ≤ P.card + T.card := by
    calc
      N + 1 = (Finset.univ : Finset (Fin (N + 1))).card := by simp
      _ = (P ∪ T).card := by rw [hcover]
      _ ≤ P.card + T.card := Finset.card_union_le P T
  have hor : N + 1 ≤ 2 * P.card ∨ N + 1 ≤ 2 * T.card := by omega
  rcases hor with hP | hT
  · left
    refine ⟨?_, ?_⟩
    · simpa [P] using hP
    · intro m hm
      simpa [P, largePrefixCuts] using hm
  · right
    refine ⟨?_, ?_⟩
    · simpa [T] using hT
    · intro m hm
      simpa [T, largeTailCuts] using hm

end ImprovedWeylBounds
