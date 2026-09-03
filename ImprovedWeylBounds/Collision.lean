import ImprovedWeylBounds.Basic

/-!
# The algebraic collision criterion

This is the contradiction engine in Proposition 5.2.  Once sampling and the
maximal moment estimate give an upper bound for a separated family, linearly
many values of size at least `A/2` force two distinct centres to collide.
-/

open scoped BigOperators

namespace ImprovedWeylBounds

/-- A finite family cannot be pairwise separated if its pointwise lower
bound already makes the moment sum exceed every separated-family upper
bound. -/
theorem exists_collision_of_moment_bound
    {ι : Type*}
    (X : Finset ι) (separated : ι → ι → Prop) (value : ι → ℝ)
    (K : ℕ) {A upper : ℝ}
    (hA : 0 ≤ A)
    (hlarge : ∀ x ∈ X, A / 2 ≤ value x)
    (hupper : (X : Set ι).Pairwise separated →
      ∑ x ∈ X, (value x) ^ K ≤ upper)
    (hstrict : upper < (X.card : ℝ) * (A / 2) ^ K) :
    ∃ x ∈ X, ∃ y ∈ X, x ≠ y ∧ ¬ separated x y := by
  classical
  by_contra hcollision
  push Not at hcollision
  have hpairwise : (X : Set ι).Pairwise separated := by
    intro x hx y hy hxy
    exact hcollision x hx y hy hxy
  have hlower :
      (X.card : ℝ) * (A / 2) ^ K ≤ ∑ x ∈ X, (value x) ^ K := by
    calc
      (X.card : ℝ) * (A / 2) ^ K = ∑ _x ∈ X, (A / 2) ^ K := by simp
      _ ≤ ∑ x ∈ X, (value x) ^ K := by
        gcongr with x hx
        exact hlarge x hx
  exact (not_lt_of_ge (hlower.trans (hupper hpairwise))) hstrict

end ImprovedWeylBounds
