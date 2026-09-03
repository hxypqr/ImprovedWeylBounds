import ImprovedWeylBounds.Basic

/-!
# External analytic-number-theory interfaces

This module records, as propositions, the exact external results used by the
paper.  It deliberately contains no axioms and no proofs of those results.
An eventual formalization can prove these propositions or accept named
hypotheses of these types at the boundary of the development.
-/

open scoped BigOperators

namespace ImprovedWeylBounds.External

/-- The critical number of variables for the Vinogradov system of degree `r`. -/
def criticalMoment (r : ℕ) : ℕ := r * (r + 1) / 2

/-- The degree-`r` Vinogradov system for two `s`-tuples in `{1, ..., N}`.

Elements of `Fin N` encode the integers `1, ..., N` by adding one to their
zero-based value.
-/
def VinogradovSystem (s r N : ℕ) (x y : Fin s → Fin N) : Prop :=
  ∀ j : Fin r,
    (∑ i : Fin s, (x i).val.succ ^ (j.val.succ)) =
      ∑ i : Fin s, (y i).val.succ ^ (j.val.succ)

/-- The number `J_{s,r}(N)` of solutions of the Vinogradov system. -/
noncomputable def vinogradovMeanValue (s r N : ℕ) : ℕ := by
  classical
  exact Fintype.card
    {xy : (Fin s → Fin N) × (Fin s → Fin N) //
      VinogradovSystem s r N xy.1 xy.2}

/-- The critical Vinogradov mean value theorem used at `main.tex`, lines
584--613.

The constant is uniform in `N`; at the critical moment `s = r(r+1)/2`, its
dependence on `s` is already absorbed into its dependence on `r`.

Source: T. D. Wooley, *Nested efficient congruencing and relatives of
Vinogradov's mean value theorem*, Corollary 1.3:
https://arxiv.org/abs/1708.01220
-/
def CriticalVMVT : Prop :=
  ∀ (r : ℕ), 1 ≤ r → ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 1 ≤ N →
      (vinogradovMeanValue (criticalMoment r) r N : ℝ) ≤
        C * Real.rpow (N : ℝ) ((criticalMoment r : ℝ) + ε)

/-- The integer tuple `(r, v₂, ..., vₖ)` is primitive.

This divisor formulation avoids making a choice of a many-argument gcd and
also handles signed approximating integers without ambiguity.  Entry zero of
`v` is unused; entry `j` represents the integer for degree `j + 1`.
-/
def TailPrimitive {k : ℕ} (r : ℕ) (v : Fin k → ℤ) : Prop :=
  ∀ d : ℕ, d ∣ r →
    (∀ j : Fin k, 1 ≤ j.val → d ∣ (v j).natAbs) → d = 1

/-- Baker's denominator-compression lemma, used at `main.tex`, lines 615--645.

The interface makes explicit the positivity of `r`, the small-parameter
range, and the sufficiently-large-`N` threshold that are implicit in the
source's standing conventions.  No additional assumption `r ≤ N` belongs to
the quoted lemma.

Source: R. C. Baker, *Small fractional parts of polynomials*, Lemma 1
(restating Baker 1986, Lemma 4.6):
https://arxiv.org/html/1602.04245v2
-/
def BakerCompression : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k),
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ →
      ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ (N : ℕ), N₀ ≤ N →
        ∀ (α : CoefficientVector k) (A : ℝ) (r : ℕ)
          (v : Fin k → ℤ),
          0 < A → 0 < r → TailPrimitive r v →
          (∀ j : Fin k, 1 ≤ j.val →
            |(r : ℝ) * α j - (v j : ℝ)| ≤
              Real.rpow (N : ℝ) (1 - ((j.val + 1 : ℕ) : ℝ)) /
                (4 * (k : ℝ) ^ 4)) →
          A ≤ ‖g α N‖ →
          Real.rpow (r : ℝ) (1 - 1 / (k : ℝ)) *
              Real.rpow (N : ℝ) η < A →
          ∃ t : ℕ, 1 ≤ t ∧ t ≤ 2 * k ^ 2 ∧
            (t * r : ℝ) ≤
              (((N : ℝ) / A) ^ k) * Real.rpow (N : ℝ) η ∧
            (∀ j : Fin k, 1 ≤ j.val →
              (t : ℝ) * |(r : ℝ) * α j - (v j : ℝ)| ≤
                (((N : ℝ) / A) ^ k) *
                  Real.rpow (N : ℝ) (-((j.val + 1 : ℕ) : ℝ) + η)) ∧
            distToInt ((t * r : ℕ) * α ⟨0, by omega⟩) ≤
              ((N : ℝ) / A) * Real.rpow (N : ℝ) (-1 + η)

/-- The tuple `(q, a₁, ..., aₖ)` is primitive.  Entry `j` represents the
coefficient numerator for degree `j + 1`. -/
def CoefficientsPrimitive {k : ℕ} (q : ℕ) (a : Fin k → ℤ) : Prop :=
  ∀ d : ℕ, d ∣ q → (∀ j : Fin k, d ∣ (a j).natAbs) → d = 1

/-- The classical large-value inverse theorem for Weyl sums, used at
`main.tex`, lines 1063--1065.

The threshold margin `δ` and the harmless power loss `η` are deliberately
separate.  This is the quantified form of the source's `N^{o(1)}` notation.
The manuscript invokes this branch at `main.tex`, lines 449--457 and
1063--1065.

Source: Baker--Chen--Shparlinski, *Bounds on the norms of maximal operators
on Weyl sums*, Lemma 2.6 (whose stated range includes the classical one):
https://arxiv.org/html/2107.13674v1
-/
def ClassicalInverse : Prop :=
  ∀ (k : ℕ), 3 ≤ k → ∀ δ η : ℝ, 0 < δ → 0 < η →
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
      ∀ (N : ℕ), N₀ ≤ N → ∀ (α : CoefficientVector k) (A : ℝ),
        0 < A → A ≤ ‖g α N‖ →
        Real.rpow (N : ℝ)
            (1 - 1 / ((2 ^ (k - 1) : ℕ) : ℝ) + δ) < A →
        ∃ (q : ℕ) (a : Fin k → ℤ),
          0 < q ∧ CoefficientsPrimitive q a ∧
          (q : ℝ) ≤ C * (((N : ℝ) / A) ^ k) * Real.rpow (N : ℝ) η ∧
          ∀ j : Fin k,
            |(q : ℝ) * α j - (a j : ℝ)| ≤
              C * (((N : ℝ) / A) ^ k) *
                Real.rpow (N : ℝ) (-((j.val + 1 : ℕ) : ℝ) + η)

/-- Membership of the fractional part of `x` in the half-open interval
`[a,b) ⊆ [0,1)`, expressed without choosing a floor convention. -/
def InHalfOpenModOne (a b x : ℝ) : Prop :=
  ∃ z : ℤ, a ≤ x - (z : ℝ) ∧ x - (z : ℝ) < b

/-- Number of a finite family of points lying in `[a,b)` modulo one. -/
noncomputable def countInHalfOpenModOne {H : ℕ} (x : Fin H → ℝ)
    (a b : ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter fun n => InHalfOpenModOne a b (x n)).card

/-- A count-discrepancy bound, with intervals fixed to be half-open. -/
def HalfOpenDiscrepancyAtMost {H : ℕ} (x : Fin H → ℝ) (B : ℝ) : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
    |(countInHalfOpenModOne x a b : ℝ) - (H : ℝ) * (b - a)| ≤ B

/-- The explicit-constant Erdős--Turán inequality used at `main.tex`, lines
1171--1210.  It is stated for count discrepancy, rather than normalized
discrepancy.

Source: H. L. Montgomery, *Ten Lectures on the Interface between Analytic
Number Theory and Harmonic Analysis*, Chapter 1.
https://doi.org/10.1090/cbms/084
-/
def ErdosTuran : Prop :=
  ∀ (H M : ℕ), 1 ≤ M → ∀ x : Fin H → ℝ,
    HalfOpenDiscrepancyAtMost x
      (3 * (H : ℝ) / (M + 1 : ℕ) +
        3 * ∑ h ∈ Finset.Icc 1 M,
          (1 / (h : ℝ)) *
            ‖∑ n : Fin H, e ((h : ℝ) * x n)‖)

/-- Baker's large-multiple lemma used at `main.tex`, lines 1323--1335.

The source application gives the explicit lower bound `N / 6`; the lemma is
stated for an arbitrary finite sequence because polynomial structure is not
part of this external input.

Source: R. C. Baker, *Diophantine Inequalities*, Theorem 2.2; see also the
application in the proof of Theorem 1 of:
https://arxiv.org/html/1602.04245v2
-/
def LargeMultiple : Prop :=
  ∀ (N M : ℕ), 1 ≤ N → 2 ≤ M → ∀ x : Fin N → ℝ,
    (∀ n : Fin N, 1 / (M : ℝ) < distToInt (x n)) →
    (N : ℝ) / 6 <
      ∑ m ∈ Finset.Icc 1 M,
        ‖∑ n : Fin N, e ((m : ℝ) * x n)‖

end ImprovedWeylBounds.External
