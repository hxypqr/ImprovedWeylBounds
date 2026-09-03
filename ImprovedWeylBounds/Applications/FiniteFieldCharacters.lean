import ImprovedWeylBounds.Conditional.FiniteField
import ImprovedWeylBounds.Applications.LargeMultiple
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# Identifying canonical real lifts with finite-field characters

The finite-field short sum was defined through canonical integer coefficient
lifts.  These lemmas verify that this realization agrees term by term with
the standard additive character on `ZMod p`; later distribution and additive
applications can therefore use either representation without an implicit
change of phase.
-/

open scoped BigOperators
open Polynomial

namespace ImprovedWeylBounds
namespace Applications

open Conditional

noncomputable section

/-- Integer obtained by evaluating the canonical coefficient representatives
of `P` at an integer. -/
def canonicalIntegerEvaluation (d p : ℕ) (P : (ZMod p)[X]) (x : ℤ) : ℤ :=
  ∑ n ∈ Finset.range (d + 1), ((P.coeff n).val : ℤ) * x ^ n

theorem eval_zmodRealLift_eq_canonicalIntegerEvaluation
    (d p : ℕ) (P : (ZMod p)[X]) (x : ℤ) :
    (zmodRealLift d p P).eval (x : ℝ) =
      (canonicalIntegerEvaluation d p P x : ℤ) := by
  classical
  rw [zmodRealLift, Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_monomial, canonicalIntegerEvaluation]
  push_cast
  rfl

theorem canonicalIntegerEvaluation_cast
    (d p : ℕ) [NeZero p] (P : (ZMod p)[X]) (x : ℤ)
    (hdeg : P.natDegree ≤ d) :
    (canonicalIntegerEvaluation d p P x : ZMod p) = P.eval (x : ZMod p) := by
  classical
  rw [P.eval_eq_sum_range' (Nat.lt_succ_of_le hdeg)]
  simp only [canonicalIntegerEvaluation, Int.cast_sum, Int.cast_mul,
    Int.cast_pow, Int.cast_natCast]
  apply Finset.sum_congr rfl
  intro n _
  rw [ZMod.natCast_zmod_val]

/-- The real additive character at an integral numerator over `p` is exactly
the standard additive character of its residue class. -/
theorem e_int_div_eq_stdAddChar (p : ℕ) [NeZero p] (z : ℤ) :
    e ((z : ℝ) / (p : ℝ)) = ZMod.stdAddChar (z : ZMod p) := by
  rw [ZMod.stdAddChar_coe]
  rw [e, Real.fourierChar_apply]
  change (Circle.exp (2 * Real.pi * ((z : ℝ) / (p : ℝ))) : ℂ) = _
  rw [Circle.coe_exp]
  push_cast
  congr 1
  ring

theorem eval_normalizedZModLift
    (d p : ℕ) [NeZero p] (P : (ZMod p)[X]) (x : ℤ) :
    (normalizedZModLift d p P).eval (x : ℝ) =
      (canonicalIntegerEvaluation d p P x : ℝ) / (p : ℝ) := by
  rw [normalizedZModLift, Polynomial.eval_mul, Polynomial.eval_C,
    eval_zmodRealLift_eq_canonicalIntegerEvaluation]
  ring

/-- Termwise agreement between the canonical lifted phase and the finite
field additive character. -/
theorem e_eval_normalizedZModLift_eq_stdAddChar
    (d p : ℕ) [NeZero p] (P : (ZMod p)[X]) (x : ℤ)
    (hdeg : P.natDegree ≤ d) :
    e ((normalizedZModLift d p P).eval (x : ℝ)) =
      ZMod.stdAddChar (P.eval (x : ZMod p)) := by
  rw [eval_normalizedZModLift, e_int_div_eq_stdAddChar]
  rw [canonicalIntegerEvaluation_cast d p P x hdeg]

/-- Exact character-sum form of `finiteFieldShortSum`. -/
theorem finiteFieldShortSum_eq_stdAddChar
    (d p : ℕ) [NeZero p] (P : (ZMod p)[X]) (M : ℤ) (H : ℕ)
    (hdeg : P.natDegree ≤ d) :
    finiteFieldShortSum d p P M H =
      ∑ n ∈ Finset.Icc 1 H,
        ZMod.stdAddChar (P.eval ((M + (n : ℤ) : ℤ) : ZMod p)) := by
  rw [finiteFieldShortSum, polynomialShortSum]
  apply Finset.sum_congr rfl
  intro n _
  simpa only [Int.cast_add, Int.cast_natCast] using
    (e_eval_normalizedZModLift_eq_stdAddChar
      d p P (M + (n : ℤ)) hdeg)

/-- Polynomial values on the integer interval `(M,M+H]`, indexed by
`Fin H`. -/
def intervalPolynomialValue (p : ℕ) (P : (ZMod p)[X])
    (M : ℤ) (H : ℕ) (n : Fin H) : ZMod p :=
  P.eval ((M + (n.1 + 1 : ℕ) : ℤ) : ZMod p)

/-- Standard representative of an interval value, normalized into `[0,1)`.
-/
def normalizedIntervalPolynomialValue (p : ℕ) [NeZero p]
    (P : (ZMod p)[X]) (M : ℤ) (H : ℕ) (n : Fin H) : ℝ :=
  ((intervalPolynomialValue p P M H n).val : ℝ) / (p : ℝ)

/-- A frequency of the normalized standard representative is exactly the
standard finite-field character. -/
theorem e_mul_normalizedIntervalPolynomialValue
    (p : ℕ) [NeZero p] (P : (ZMod p)[X]) (M : ℤ) (H h : ℕ)
    (n : Fin H) :
    e ((h : ℝ) * normalizedIntervalPolynomialValue p P M H n) =
      ZMod.stdAddChar ((h : ZMod p) * intervalPolynomialValue p P M H n) := by
  let v := intervalPolynomialValue p P M H n
  calc
    e ((h : ℝ) * normalizedIntervalPolynomialValue p P M H n) =
        e ((((h * v.val : ℕ) : ℤ) : ℝ) / (p : ℝ)) := by
      congr 1
      simp only [normalizedIntervalPolynomialValue, v]
      push_cast
      ring
    _ = ZMod.stdAddChar (((h * v.val : ℕ) : ℤ) : ZMod p) :=
      e_int_div_eq_stdAddChar p ((h * v.val : ℕ) : ℤ)
    _ = ZMod.stdAddChar ((h : ZMod p) * v) := by
      congr 1
      push_cast
      rw [ZMod.natCast_zmod_val]

/-- Exact identification of every Erdős--Turán frequency sum with the
finite-field short sum of the nonzero scalar multiple `hP`. -/
theorem intervalFrequencySum_eq_finiteFieldShortSum
    (d p : ℕ) [NeZero p] (P : (ZMod p)[X]) (M : ℤ) (H h : ℕ)
    (hdeg : P.natDegree ≤ d) :
    (∑ n : Fin H,
        e ((h : ℝ) * normalizedIntervalPolynomialValue p P M H n)) =
      finiteFieldShortSum d p (Polynomial.C (h : ZMod p) * P) M H := by
  rw [finiteFieldShortSum_eq_stdAddChar]
  · rw [sum_Icc_one_eq_sum_fin]
    apply Finset.sum_congr rfl
    intro n _
    rw [e_mul_normalizedIntervalPolynomialValue]
    congr 1
    simp only [intervalPolynomialValue, Polynomial.eval_mul,
      Polynomial.eval_C]
  · exact (Polynomial.natDegree_C_mul_le (h : ZMod p) P).trans hdeg

end

end Applications
end ImprovedWeylBounds
