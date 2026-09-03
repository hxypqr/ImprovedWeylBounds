import Mathlib

/-!
# Basic notation for Weyl sums

This file gives exact, finite definitions for the additive character, integer
intervals, Weyl sums, distance to the nearest integer, and the two degree
parameters used in the paper.
-/

open scoped BigOperators

namespace ImprovedWeylBounds

/-- Mathlib's standard additive character on `ℝ`, valued in the unit circle. -/
noncomputable abbrev additiveCharacter : AddChar ℝ Circle := Real.fourierChar

/-- The paper's notation `e(x) = exp(2 π i x)`, regarded as a complex number. -/
noncomputable def e (x : ℝ) : ℂ := (additiveCharacter x : ℂ)

@[simp]
theorem e_zero : e 0 = 1 := by
  simp [e]

/-- The defining homomorphism identity `e(x + y) = e(x)e(y)`. -/
theorem e_add (x y : ℝ) : e (x + y) = e x * e y := by
  change ((additiveCharacter (x + y) : Circle) : ℂ) =
    ((additiveCharacter x : Circle) : ℂ) * ((additiveCharacter y : Circle) : ℂ)
  rw [AddChar.map_add_eq_mul]
  rfl

/-- The character is trivial on the integers. -/
@[simp]
theorem e_int (z : ℤ) : e (z : ℝ) = 1 := by
  rw [e, Real.fourierChar_apply]
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    Complex.exp_int_mul_two_pi_mul_I z

/-- Every value of the additive character has complex norm one. -/
@[simp]
theorem norm_e (x : ℝ) : ‖e x‖ = 1 := by
  exact Circle.norm_coe _

/-- The integer interval `(M, M + H]`, containing exactly `H` integers. -/
noncomputable def integerInterval (M : ℤ) (H : ℕ) : Finset ℤ :=
  Finset.Ioc M (M + H)

@[simp]
theorem mem_integerInterval {M n : ℤ} {H : ℕ} :
    n ∈ integerInterval M H ↔ M < n ∧ n ≤ M + (H : ℤ) := by
  simp [integerInterval]

/-- The interval `(M, M + H]` has exactly `H` integer points. -/
@[simp]
theorem card_integerInterval (M : ℤ) (H : ℕ) :
    (integerInterval M H).card = H := by
  simp [integerInterval, Int.card_Ioc]

/-- A finite exponential sum over an integer interval. -/
noncomputable def intervalExpSum (phase : ℤ → ℝ) (M : ℤ) (H : ℕ) : ℂ :=
  ∑ n ∈ integerInterval M H, e (phase n)

/-- The polynomial phase `α₁n + ⋯ + αₖnᵏ`, with coefficients indexed from zero.
The coefficient at index `0` is harmless and permits direct use of vectors and
polynomial coefficient functions. -/
noncomputable def polynomialPhase {k : ℕ} (α : Fin (k + 1) → ℝ) (n : ℤ) : ℝ :=
  ∑ j : Fin (k + 1), α j * (n : ℝ) ^ (j : ℕ)

/-- The translated-interval Weyl sum attached to a coefficient vector. -/
noncomputable def weylSum {k : ℕ} (α : Fin (k + 1) → ℝ) (M : ℤ) (H : ℕ) : ℂ :=
  intervalExpSum (polynomialPhase α) M H

/-- Distance from a real number to the nearest integer, realized as the norm
of its class in `ℝ / ℤ`. -/
noncomputable def distToInt (x : ℝ) : ℝ :=
  ‖(x : UnitAddCircle)‖

@[simp]
theorem distToInt_eq_abs_sub_round (x : ℝ) :
    distToInt x = |x - (round x : ℝ)| := by
  exact UnitAddCircle.norm_eq

/-- The chosen nearest integer really minimizes the distance. -/
theorem distToInt_le_abs_sub_int (x : ℝ) (z : ℤ) :
    distToInt x ≤ |x - (z : ℝ)| := by
  rw [distToInt_eq_abs_sub_round]
  exact round_le x z

/-- Distance to the integers is invariant under an integral translation. -/
@[simp]
theorem distToInt_add_int (x : ℝ) (z : ℤ) :
    distToInt (x + z) = distToInt x := by
  simp only [distToInt_eq_abs_sub_round, round_add_intCast]
  congr 1
  push_cast
  ring

@[simp]
theorem distToInt_sub_int (x : ℝ) (z : ℤ) :
    distToInt (x - z) = distToInt x := by
  simpa [sub_eq_add_neg] using distToInt_add_int x (-z)

/-- Every real number lies within `1/2` of an integer. -/
theorem distToInt_le_half (x : ℝ) : distToInt x ≤ 1 / 2 := by
  simpa [distToInt] using
    (AddCircle.norm_le_half_period (p := (1 : ℝ)) (x := (x : UnitAddCircle)) one_ne_zero)

/-- Distance to the integers vanishes exactly at the integers. -/
theorem distToInt_eq_zero_iff (x : ℝ) :
    distToInt x = 0 ↔ ∃ z : ℤ, x = z := by
  rw [distToInt_eq_abs_sub_round, abs_eq_zero, sub_eq_zero]
  constructor
  · intro hx
    exact ⟨round x, hx⟩
  · rintro ⟨z, rfl⟩
    simp

/-- A coefficient vector `(α₁, …, αₖ)` indexed so that entry `i`
is the coefficient of degree `i + 1`. -/
abbrev CoefficientVector (k : ℕ) := Fin k → ℝ

/-- The no-constant-term phase `α₁ n + ⋯ + αₖ nᵏ`. -/
noncomputable def nonconstantPhase {k : ℕ} (α : CoefficientVector k) (n : ℕ) : ℝ :=
  ∑ j : Fin k, α j * (n : ℝ) ^ (j.1 + 1)

/-- The paper's full-length Weyl sum
`gₖ(α; N) = ∑_{1 ≤ n ≤ N} e(α₁n + ⋯ + αₖnᵏ)`. -/
noncomputable def g {k : ℕ} (α : CoefficientVector k) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, e (nonconstantPhase α n)

/-- The critical moment exponent `Kₖ = k(k-1)`. -/
def K (k : ℕ) : ℕ := k * (k - 1)

/-- The combined Weyl exponent denominator
`Δₖ = min(2^(k-1), k(k-1))`. -/
def Delta (k : ℕ) : ℕ := min (2 ^ (k - 1)) (K k)

end ImprovedWeylBounds
