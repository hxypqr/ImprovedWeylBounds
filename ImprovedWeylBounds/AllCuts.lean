import ImprovedWeylBounds.FiniteSums
import ImprovedWeylBounds.Translation

/-!
# All cuts, translated partial sums, and short blocks

This file formalizes the internal content of Lemma 5.1 of the manuscript.
The proof has three independent finite parts:

* every cut has a large prefix or a large complementary tail (imported from
  `FiniteSums`), and one orientation occurs for at least half of the cuts;
* a tail is a translated forward partial sum, while a prefix becomes a
  reflected translated partial sum after reversing its order;
* the selected integer parameters in `[0, N+1]` can be divided into exactly
  `4 * k!` consecutive blocks, one of which retains the expected proportion
  of the points and has the diameter needed later in Lemma 5.4.

The location assertion `X \subseteq [0,N+1]` is made explicit below.  It is
used later when a collision is conjugated by a translation, although it was
omitted from the displayed statement of Lemma 5.1 in the manuscript.
-/

open scoped BigOperators
open Polynomial

namespace ImprovedWeylBounds
namespace AllCuts

noncomputable section

/-! ## The manuscript sum as a finite sequence -/

/-- The summand indexed by `i : Fin N` is the manuscript summand at `i+1`. -/
def phaseSequence (phase : ℕ → ℝ) (N : ℕ) : Fin N → ℂ :=
  fun i ↦ e (phase (i.1 + 1))

/-- Specialization of `phaseSequence` to the polynomial phase of `g`. -/
def weylSequence {k : ℕ} (α : CoefficientVector k) (N : ℕ) : Fin N → ℂ :=
  phaseSequence (nonconstantPhase α) N

/-- Prefix `S_m = ∑_{1 ≤ n ≤ m} e(phase n)`. -/
def manuscriptPrefix (phase : ℕ → ℝ) (m : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 m, e (phase n)

/-- Tail `S_N-S_m = ∑_{m < n ≤ N} e(phase n)`. -/
def manuscriptTail (phase : ℕ → ℝ) (m N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ioc m N, e (phase n)

/-- The normalized forward sum of length `L` based at `m`. -/
def forwardPartial (phase : ℕ → ℝ) (m L : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 L, e (phase (m + h) - phase m)

/-- The normalized backwards sum of length `L` based at `x`. -/
def backwardPartial (phase : ℕ → ℝ) (x L : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 L, e (phase (x - h) - phase x)

theorem totalSum_weylSequence {k N : ℕ} (α : CoefficientVector k) :
    totalSum (weylSequence α N) = g α N := by
  classical
  rw [totalSum, g]
  change (∑ i : Fin N, e (nonconstantPhase α (i.1 + 1))) = _
  rw [Fin.sum_univ_eq_sum_range
    (fun i ↦ e (nonconstantPhase α (i + 1)))]
  apply Finset.sum_bij (fun i _ ↦ i + 1)
  · intro i hi
    simp only [Finset.mem_range] at hi
    simp only [Finset.mem_Icc]
    omega
  · intro i₁ hi₁ i₂ hi₂ heq
    omega
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    refine ⟨n - 1, ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · omega
  · intro i hi
    rfl

theorem prefixAt_phaseSequence {N : ℕ} (phase : ℕ → ℝ)
    (m : Fin (N + 1)) :
    prefixAt (phaseSequence phase N) m = manuscriptPrefix phase m.1 := by
  classical
  rw [prefixAt, manuscriptPrefix]
  change (∑ i : Fin N, if i.1 < m.1 then e (phase (i.1 + 1)) else 0) = _
  rw [Fin.sum_univ_eq_sum_range
    (fun i ↦ if i < m.1 then e (phase (i + 1)) else 0)]
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun i _ ↦ i + 1)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    simp only [Finset.mem_Icc]
    omega
  · intro i₁ hi₁ i₂ hi₂ heq
    omega
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    refine ⟨n - 1, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_range]
      omega
    · omega
  · intro i hi
    rfl

theorem tailAt_phaseSequence {N : ℕ} (phase : ℕ → ℝ)
    (m : Fin (N + 1)) :
    tailAt (phaseSequence phase N) m = manuscriptTail phase m.1 N := by
  classical
  rw [tailAt, manuscriptTail]
  change (∑ i : Fin N, if m.1 ≤ i.1 then e (phase (i.1 + 1)) else 0) = _
  rw [Fin.sum_univ_eq_sum_range
    (fun i ↦ if m.1 ≤ i then e (phase (i + 1)) else 0)]
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun i _ ↦ i + 1)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    simp only [Finset.mem_Ioc]
    omega
  · intro i₁ hi₁ i₂ hi₂ heq
    omega
  · intro n hn
    simp only [Finset.mem_Ioc] at hn
    refine ⟨n - 1, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_range]
      omega
    · omega
  · intro i hi
    rfl

/-! ## Forward and reversed-prefix identities -/

/-- Equation (5.3) in the manuscript, before specializing `phase` to a
polynomial: a tail is a unit scalar times a translated forward sum. -/
theorem manuscriptTail_eq_forwardPartial (phase : ℕ → ℝ) {m N : ℕ}
    (hmN : m ≤ N) :
    manuscriptTail phase m N = e (phase m) * forwardPartial phase m (N - m) := by
  classical
  rw [manuscriptTail, forwardPartial, Finset.mul_sum]
  apply Finset.sum_bij (fun n _ ↦ n - m)
  · intro n hn
    simp only [Finset.mem_Ioc] at hn
    simp only [Finset.mem_Icc]
    omega
  · intro n₁ hn₁ n₂ hn₂ heq
    simp only [Finset.mem_Ioc] at hn₁ hn₂
    omega
  · intro h hh
    simp only [Finset.mem_Icc] at hh
    refine ⟨m + h, ?_, ?_⟩
    · simp only [Finset.mem_Ioc]
      omega
    · omega
  · intro n hn
    simp only [Finset.mem_Ioc] at hn
    rw [← e_add]
    congr 1
    have hnm : m + (n - m) = n := Nat.add_sub_of_le hn.1.le
    rw [hnm]
    ring

/-- Equation (5.4) in the manuscript: reversing a prefix based at `x=m+1`
turns it into a normalized backwards sum. -/
theorem manuscriptPrefix_eq_backwardPartial (phase : ℕ → ℝ) (m : ℕ) :
    manuscriptPrefix phase m =
      e (phase (m + 1)) * backwardPartial phase (m + 1) m := by
  classical
  rw [manuscriptPrefix, backwardPartial, Finset.mul_sum]
  apply Finset.sum_bij (fun n _ ↦ m + 1 - n)
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    simp only [Finset.mem_Icc]
    omega
  · intro n₁ hn₁ n₂ hn₂ heq
    simp only [Finset.mem_Icc] at hn₁ hn₂
    omega
  · intro h hh
    simp only [Finset.mem_Icc] at hh
    refine ⟨m + 1 - h, ?_, ?_⟩
    · simp only [Finset.mem_Icc]
      omega
    · omega
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    rw [← e_add]
    congr 1
    have hreverse : m + 1 - (m + 1 - n) = n := by omega
    rw [hreverse]
    ring

/-- The exact tail identity written using `tailAt`. -/
theorem tailAt_eq_forwardPartial {N : ℕ} (phase : ℕ → ℝ)
    (m : Fin (N + 1)) :
    tailAt (phaseSequence phase N) m =
      e (phase m.1) * forwardPartial phase m.1 (N - m.1) := by
  rw [tailAt_phaseSequence]
  exact manuscriptTail_eq_forwardPartial phase (Nat.le_of_lt_succ m.2)

/-- The exact reversed-prefix identity written using `prefixAt`. -/
theorem prefixAt_eq_backwardPartial {N : ℕ} (phase : ℕ → ℝ)
    (m : Fin (N + 1)) :
    prefixAt (phaseSequence phase N) m =
      e (phase (m.1 + 1)) * backwardPartial phase (m.1 + 1) m.1 := by
  rw [prefixAt_phaseSequence]
  exact manuscriptPrefix_eq_backwardPartial phase m.1

/-! ## Identification of the two polynomial centres -/

/-- A polynomial with zero constant term and coefficient vector `α`. -/
def phasePolynomial {k : ℕ} (α : CoefficientVector k) : ℝ[X] :=
  ∑ j : Fin k, Polynomial.monomial (j.1 + 1) (α j)

@[simp]
theorem eval_phasePolynomial {k : ℕ} (α : CoefficientVector k) (n : ℕ) :
    (phasePolynomial α).eval (n : ℝ) = nonconstantPhase α n := by
  classical
  simp only [phasePolynomial, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial, nonconstantPhase]

/-- A forward normalized phase is the nonconstant part of `P(X+m)`.
Thus its lower coefficients are the projection of `T_m α`. -/
theorem forwardPartial_eq_translate {k : ℕ} (α : CoefficientVector k)
    (m L : ℕ) :
    forwardPartial (nonconstantPhase α) m L =
      ∑ h ∈ Finset.Icc 1 L,
        e ((translate (m : ℤ) (phasePolynomial α)).eval (h : ℝ) -
          (translate (m : ℤ) (phasePolynomial α)).eval 0) := by
  classical
  apply Finset.sum_congr rfl
  intro h hh
  rw [eval_translate, eval_zero_translate]
  have hcast : ((h : ℝ) + ((m : ℤ) : ℝ)) = ((m + h : ℕ) : ℝ) := by
    push_cast
    ring
  have hmcast : (((m : ℤ) : ℝ)) = (m : ℝ) := by norm_num
  rw [hcast, hmcast, eval_phasePolynomial, eval_phasePolynomial]

/-- A backwards normalized phase is the nonconstant part of `P(x-X)`.
Thus its lower coefficients are the projection of `R T_x α`. -/
theorem backwardPartial_eq_reflect_translate {k : ℕ}
    (α : CoefficientVector k) (x L : ℕ) (hLx : L ≤ x) :
    backwardPartial (nonconstantPhase α) x L =
      ∑ h ∈ Finset.Icc 1 L,
        e ((reflect (translate (x : ℤ) (phasePolynomial α))).eval (h : ℝ) -
          (reflect (translate (x : ℤ) (phasePolynomial α))).eval 0) := by
  classical
  apply Finset.sum_congr rfl
  intro h hh
  simp only [Finset.mem_Icc] at hh
  rw [eval_reflect_translate, eval_reflect_translate]
  have hhx : h ≤ x := hh.2.trans hLx
  have hcast : (((x : ℤ) : ℝ)) - (h : ℝ) = ((x - h : ℕ) : ℝ) := by
    rw [show (((x : ℤ) : ℝ)) = (x : ℝ) by norm_num]
    exact (Nat.cast_sub hhx).symm
  have hxcast : (((x : ℤ) : ℝ)) = (x : ℝ) := by norm_num
  rw [hcast, sub_zero, hxcast]
  norm_num [eval_phasePolynomial]

/-! ## Orientation pigeonhole with positive partial-sum lengths -/

/-- The forward centre belonging to the cut `m`; its value lies in
`[0,N+1]` by construction. -/
def forwardCentre {N : ℕ} (m : Fin (N + 1)) : Fin (N + 2) :=
  ⟨m.1, by omega⟩

/-- The reversed-prefix centre `x=m+1`; it too lies in `[0,N+1]`. -/
def backwardCentre {N : ℕ} (m : Fin (N + 1)) : Fin (N + 2) :=
  ⟨m.1 + 1, by omega⟩

theorem forwardCentre_injective {N : ℕ} :
    Function.Injective (@forwardCentre N) := by
  intro a b hab
  apply Fin.ext
  exact congrArg (fun z : Fin (N + 2) ↦ z.1) hab

theorem backwardCentre_injective {N : ℕ} :
    Function.Injective (@backwardCentre N) := by
  intro a b hab
  apply Fin.ext
  have := congrArg Fin.val hab
  simp only [backwardCentre] at this
  omega

/-- The repaired location condition used later in the collision argument. -/
theorem centre_location {N : ℕ} (x : Fin (N + 2)) :
    (0 : ℤ) ≤ (x.1 : ℤ) ∧ (x.1 : ℤ) ≤ (N : ℤ) + 1 := by
  constructor
  · exact Int.natCast_nonneg _
  · exact_mod_cast (Nat.le_of_lt_succ x.2)

/-- For a nonzero full sum, one orientation provides at least half of the
cuts, every selected cut has positive length, and its normalized partial sum
has norm at least half of the full norm.  This is the exact orientation step
in Lemma 5.1; the subsequent block extraction is proved below. -/
theorem exists_many_oriented_weyl_cuts {k N : ℕ}
    (α : CoefficientVector k) (hlarge : 0 < ‖g α N‖) :
    (N + 1 ≤ 2 * (largeTailCuts (weylSequence α N) ‖g α N‖).card ∧
        ∀ m ∈ largeTailCuts (weylSequence α N) ‖g α N‖,
          1 ≤ N - m.1 ∧
          ‖forwardPartial (nonconstantPhase α) m.1 (N - m.1)‖ ≥
            ‖g α N‖ / 2 ∧
          (0 : ℤ) ≤ (forwardCentre m).1 ∧
          ((forwardCentre m).1 : ℤ) ≤ (N : ℤ) + 1) ∨
      (N + 1 ≤ 2 * (largePrefixCuts (weylSequence α N) ‖g α N‖).card ∧
        ∀ m ∈ largePrefixCuts (weylSequence α N) ‖g α N‖,
          1 ≤ m.1 ∧
          ‖backwardPartial (nonconstantPhase α) (m.1 + 1) m.1‖ ≥
            ‖g α N‖ / 2 ∧
          (0 : ℤ) ≤ (backwardCentre m).1 ∧
          ((backwardCentre m).1 : ℤ) ≤ (N : ℤ) + 1) := by
  have htotal : ‖g α N‖ ≤ ‖totalSum (weylSequence α N)‖ := by
    rw [totalSum_weylSequence]
  obtain hprefix | htail :=
    exists_many_large_cuts (weylSequence α N) htotal
  · right
    refine ⟨hprefix.1, ?_⟩
    intro m hm
    have hmLarge := hprefix.2 m hm
    have hlen : 1 ≤ m.1 := by
      by_contra hzero
      have hm0 : m.1 = 0 := by omega
      have hprefzero : prefixAt (weylSequence α N) m = 0 := by
        change prefixAt (phaseSequence (nonconstantPhase α) N) m = 0
        rw [prefixAt_eq_backwardPartial]
        simp [hm0, backwardPartial]
      rw [hprefzero, norm_zero] at hmLarge
      linarith
    have hid := prefixAt_eq_backwardPartial (nonconstantPhase α) m
    have hnorm :
        ‖prefixAt (weylSequence α N) m‖ =
          ‖backwardPartial (nonconstantPhase α) (m.1 + 1) m.1‖ := by
      change ‖prefixAt (phaseSequence (nonconstantPhase α) N) m‖ = _
      rw [hid, norm_mul, norm_e, one_mul]
    refine ⟨hlen, ?_, centre_location (backwardCentre m)⟩
    rwa [hnorm] at hmLarge
  · left
    refine ⟨htail.1, ?_⟩
    intro m hm
    have hmLarge := htail.2 m hm
    have hlen : 1 ≤ N - m.1 := by
      by_contra hzero
      have hmN : m.1 = N := by omega
      have htailzero : tailAt (weylSequence α N) m = 0 := by
        change tailAt (phaseSequence (nonconstantPhase α) N) m = 0
        rw [tailAt_eq_forwardPartial]
        simp [hmN, forwardPartial]
      rw [htailzero, norm_zero] at hmLarge
      linarith
    have hid := tailAt_eq_forwardPartial (nonconstantPhase α) m
    have hnorm :
        ‖tailAt (weylSequence α N) m‖ =
          ‖forwardPartial (nonconstantPhase α) m.1 (N - m.1)‖ := by
      change ‖tailAt (phaseSequence (nonconstantPhase α) N) m‖ = _
      rw [hid, norm_mul, norm_e, one_mul]
    refine ⟨hlen, ?_, centre_location (forwardCentre m)⟩
    rwa [hnorm] at hmLarge

/-! ## Exactly `B` consecutive blocks -/

/-- Width of the consecutive blocks covering the integer range `[0,N+1]`.
The extra `+1` is the ceiling convention that makes the last block total. -/
def blockWidth (N B : ℕ) : ℕ := (N + 1) / B + 1

theorem blockWidth_pos (N B : ℕ) : 0 < blockWidth N B := by
  simp [blockWidth]

private theorem endpoint_lt_blocks_mul_width (N B : ℕ) (hB : 0 < B) :
    N + 1 < B * blockWidth N B := by
  have hmod := Nat.mod_lt (N + 1) hB
  have hdecomp := Nat.mod_add_div (N + 1) B
  rw [blockWidth]
  calc
    N + 1 = (N + 1) % B + B * ((N + 1) / B) := hdecomp.symm
    _ < B + B * ((N + 1) / B) := by omega
    _ = B * ((N + 1) / B + 1) := by ring

/-- Quotient by the block width.  The preceding endpoint estimate proves
that its value is one of exactly `B` block labels. -/
def blockIndex (N B : ℕ) (hB : 0 < B) (x : Fin (N + 2)) : Fin B :=
  ⟨x.1 / blockWidth N B, by
    apply (Nat.div_lt_iff_lt_mul (blockWidth_pos N B)).2
    exact (Nat.le_of_lt_succ x.2).trans_lt
      (endpoint_lt_blocks_mul_width N B hB)⟩

/-- The points of `X` lying in block `b`. -/
def blockFiber {N B : ℕ} (hB : 0 < B) (X : Finset (Fin (N + 2)))
    (b : Fin B) : Finset (Fin (N + 2)) :=
  X.filter fun x ↦ blockIndex N B hB x = b

theorem blockFiber_subset {N B : ℕ} (hB : 0 < B)
    (X : Finset (Fin (N + 2))) (b : Fin B) :
    blockFiber hB X b ⊆ X := by
  exact Finset.filter_subset _ _

private theorem natDist_lt_width_of_same_block
    {N B : ℕ} (hB : 0 < B) {x y : Fin (N + 2)}
    (hxy : blockIndex N B hB x = blockIndex N B hB y) :
    Nat.dist x.1 y.1 < blockWidth N B := by
  have hquot : x.1 / blockWidth N B = y.1 / blockWidth N B :=
    congrArg Fin.val hxy
  let W := blockWidth N B
  have hW : 0 < W := blockWidth_pos N B
  have hxmod : x.1 % W < W := Nat.mod_lt _ hW
  have hymod : y.1 % W < W := Nat.mod_lt _ hW
  have hxdec : x.1 % W + W * (x.1 / W) = x.1 := Nat.mod_add_div _ _
  have hydec : y.1 % W + W * (y.1 / W) = y.1 := Nat.mod_add_div _ _
  have hquotW : x.1 / W = y.1 / W := hquot
  rw [← hxdec, ← hydec, hquotW, Nat.dist_add_add_right]
  rcases le_total (x.1 % W) (y.1 % W) with hle | hle
  · rw [Nat.dist_eq_sub_of_le hle]
    omega
  · rw [Nat.dist_eq_sub_of_le_right hle]
    omega

/-- One of `B` consecutive blocks contains at least the floor of the average
number of points. -/
theorem exists_dense_block {N B : ℕ} (hB : 0 < B)
    (X : Finset (Fin (N + 2))) :
    ∃ b : Fin B,
      X.card / B ≤ (blockFiber hB X b).card ∧
      ∀ x ∈ blockFiber hB X b, ∀ y ∈ blockFiber hB X b,
        Nat.dist x.1 y.1 < blockWidth N B := by
  classical
  let f := blockIndex N B hB
  have hmul : B * (X.card / B) ≤ X.card := by
    simpa [mul_comm] using Nat.div_mul_le_self X.card B
  have hmul' :
      (Finset.univ : Finset (Fin B)).card * (X.card / B) ≤ X.card := by
    simpa only [Finset.card_univ, Fintype.card_fin] using hmul
  have ht : (Finset.univ : Finset (Fin B)).Nonempty :=
    ⟨⟨0, hB⟩, Finset.mem_univ _⟩
  obtain ⟨b, hb, hcard⟩ :=
    Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
      (s := X) (t := (Finset.univ : Finset (Fin B))) (f := f)
      (fun _ _ ↦ Finset.mem_univ _) ht hmul'
  refine ⟨b, ?_, ?_⟩
  · simpa only [blockFiber, f] using hcard
  · intro x hx y hy
    have hxb : blockIndex N B hB x = b := by
      exact (Finset.mem_filter.mp (show x ∈ X.filter
        (fun z ↦ blockIndex N B hB z = b) from hx)).2
    have hyb : blockIndex N B hB y = b := by
      exact (Finset.mem_filter.mp (show y ∈ X.filter
        (fun z ↦ blockIndex N B hB z = b) from hy)).2
    exact natDist_lt_width_of_same_block hB (hxb.trans hyb.symm)

/-- With the manuscript's choice `B=4*k!`, every pair in the dense block
has twice the diameter required by the later denominator extraction. -/
theorem exists_dense_factorial_block (k N : ℕ) (hN : 1 ≤ N)
    (X : Finset (Fin (N + 2))) :
    ∃ b : Fin (4 * k.factorial),
      X.card / (4 * k.factorial) ≤
          (blockFiber (by positivity : 0 < 4 * k.factorial) X b).card ∧
      (∀ x ∈ blockFiber (by positivity : 0 < 4 * k.factorial) X b,
        (0 : ℤ) ≤ (x.1 : ℤ) ∧ (x.1 : ℤ) ≤ (N : ℤ) + 1) ∧
      (∀ x ∈ blockFiber (by positivity : 0 < 4 * k.factorial) X b,
        ∀ y ∈ blockFiber (by positivity : 0 < 4 * k.factorial) X b,
          2 * k.factorial * Nat.dist x.1 y.1 ≤ N) := by
  let hB : 0 < 4 * k.factorial := by positivity
  obtain ⟨b, hcard, hdiam⟩ := exists_dense_block hB X
  refine ⟨b, ?_, ?_, ?_⟩
  · simpa only using hcard
  · intro x hx
    exact centre_location x
  · intro x hx y hy
    have hdlt := hdiam x hx y hy
    have hdle : Nat.dist x.1 y.1 ≤ (N + 1) / (4 * k.factorial) := by
      simpa only [blockWidth] using (Nat.lt_succ_iff.mp hdlt)
    have hmuldiv :
        4 * k.factorial * ((N + 1) / (4 * k.factorial)) ≤ N + 1 := by
      simpa only [mul_comm] using
        Nat.div_mul_le_self (N + 1) (4 * k.factorial)
    have hfour : 4 * (k.factorial * Nat.dist x.1 y.1) ≤ N + 1 := by
      calc
        4 * (k.factorial * Nat.dist x.1 y.1) =
            (4 * k.factorial) * Nat.dist x.1 y.1 := by ring
        _ ≤ (4 * k.factorial) * ((N + 1) / (4 * k.factorial)) := by
          exact Nat.mul_le_mul_left _ hdle
        _ ≤ N + 1 := hmuldiv
    have hassoc :
        2 * k.factorial * Nat.dist x.1 y.1 =
          2 * (k.factorial * Nat.dist x.1 y.1) := by ring
    rw [hassoc]
    omega

/-- The form consumed by Lemma 5.4: in the selected block,
`k! * |x-y| ≤ N`.  Here `Nat.dist` is the absolute difference of the two
nonnegative integer centres. -/
theorem factorial_natDist_le_of_mem_dense_block
    {k N : ℕ} {X : Finset (Fin (N + 2))}
    {b : Fin (4 * k.factorial)}
    (hdiam : ∀ x ∈ blockFiber (by positivity : 0 < 4 * k.factorial) X b,
      ∀ y ∈ blockFiber (by positivity : 0 < 4 * k.factorial) X b,
        2 * k.factorial * Nat.dist x.1 y.1 ≤ N)
    {x y : Fin (N + 2)}
    (hx : x ∈ blockFiber (by positivity : 0 < 4 * k.factorial) X b)
    (hy : y ∈ blockFiber (by positivity : 0 < 4 * k.factorial) X b) :
    k.factorial * Nat.dist x.1 y.1 ≤ N := by
  calc
    k.factorial * Nat.dist x.1 y.1 ≤
        2 * (k.factorial * Nat.dist x.1 y.1) :=
      Nat.le_mul_of_pos_left _ (by norm_num)
    _ = 2 * k.factorial * Nat.dist x.1 y.1 := by ring
    _ ≤ N := hdiam x hx y hy

/-- For nonnegative integer representatives, `Nat.dist` is the integer
absolute difference used in Lemma 5.4. -/
theorem natAbs_intCast_sub_eq_natDist (x y : ℕ) :
    ((x : ℤ) - (y : ℤ)).natAbs = Nat.dist x y := by
  rcases le_total x y with hxy | hyx
  · rw [Nat.dist_eq_sub_of_le hxy]
    have hsub : (x : ℤ) - (y : ℤ) = -((y - x : ℕ) : ℤ) := by
      omega
    rw [hsub, Int.natAbs_neg]
    simp
  · rw [Nat.dist_eq_sub_of_le_right hyx]
    have hsub : (x : ℤ) - (y : ℤ) = ((x - y : ℕ) : ℤ) := by
      omega
    rw [hsub]
    simp

/-- Integer form of the short-block conclusion consumed by
`collision_to_preliminaryApproximation`. -/
theorem factorial_natAbs_sub_le_of_mem_dense_block
    {k N : ℕ} {X : Finset (Fin (N + 2))}
    {b : Fin (4 * k.factorial)}
    (hdiam : ∀ x ∈ blockFiber (by positivity : 0 < 4 * k.factorial) X b,
      ∀ y ∈ blockFiber (by positivity : 0 < 4 * k.factorial) X b,
        2 * k.factorial * Nat.dist x.1 y.1 ≤ N)
    {x y : Fin (N + 2)}
    (hx : x ∈ blockFiber (by positivity : 0 < 4 * k.factorial) X b)
    (hy : y ∈ blockFiber (by positivity : 0 < 4 * k.factorial) X b) :
    k.factorial * (((x.1 : ℤ) - (y.1 : ℤ)).natAbs) ≤ N := by
  rw [natAbs_intCast_sub_eq_natDist]
  exact factorial_natDist_le_of_mem_dense_block hdiam hx hy

/-! ## The fully assembled version of Lemma 5.1 -/

/-- Output data when the tail/forward orientation is the populous one. -/
structure ForwardCluster (k N : ℕ) (α : CoefficientVector k) where
  /-- The selected set of integer centres, represented intrinsically as
  elements of `[0,N+1]`. -/
  X : Finset (Fin (N + 2))
  /-- Explicit form of `|X| \gg_k N`, with only harmless integer floors. -/
  card_lower : (N + 1) / (8 * k.factorial) ≤ X.card
  /-- The repaired ambient-location condition. -/
  location : ∀ x ∈ X,
    (0 : ℤ) ≤ (x.1 : ℤ) ∧ (x.1 : ℤ) ≤ (N : ℤ) + 1
  /-- The block has length at most `N/(2k!)` in the integer sense. -/
  short : ∀ x ∈ X, ∀ y ∈ X,
    2 * k.factorial * Nat.dist x.1 y.1 ≤ N
  /-- Every point comes from a tail cut of positive length carrying a large
  normalized forward partial sum. -/
  partial_sum : ∀ x ∈ X, ∃ m : Fin (N + 1),
    m ∈ largeTailCuts (weylSequence α N) ‖g α N‖ ∧
    forwardCentre m = x ∧
    1 ≤ N - m.1 ∧
    ‖forwardPartial (nonconstantPhase α) m.1 (N - m.1)‖ ≥ ‖g α N‖ / 2

/-- Output data when the prefix/reversed orientation is the populous one. -/
structure BackwardCluster (k N : ℕ) (α : CoefficientVector k) where
  X : Finset (Fin (N + 2))
  card_lower : (N + 1) / (8 * k.factorial) ≤ X.card
  location : ∀ x ∈ X,
    (0 : ℤ) ≤ (x.1 : ℤ) ∧ (x.1 : ℤ) ≤ (N : ℤ) + 1
  short : ∀ x ∈ X, ∀ y ∈ X,
    2 * k.factorial * Nat.dist x.1 y.1 ≤ N
  /-- Every point comes from a prefix cut; after reversal it has positive
  length and a large normalized backwards partial sum. -/
  partial_sum : ∀ x ∈ X, ∃ m : Fin (N + 1),
    m ∈ largePrefixCuts (weylSequence α N) ‖g α N‖ ∧
    backwardCentre m = x ∧
    1 ≤ m.1 ∧
    ‖backwardPartial (nonconstantPhase α) (m.1 + 1) m.1‖ ≥ ‖g α N‖ / 2

private theorem orientation_card_div_le
    {n s t B : ℕ} (hB : 0 < B) (horient : n ≤ 2 * s)
    (hblock : s / B ≤ t) :
    n / (2 * B) ≤ t := by
  let q := n / (2 * B)
  have htwoB : 0 < 2 * B := Nat.mul_pos (by norm_num) hB
  have hqmul : q * (2 * B) ≤ n := by
    exact Nat.div_mul_le_self n (2 * B)
  have hqmul' : 2 * (q * B) ≤ 2 * s := by
    calc
      2 * (q * B) = q * (2 * B) := by ring
      _ ≤ n := hqmul
      _ ≤ 2 * s := horient
  have hqB : q * B ≤ s := by
    omega
  have hqdiv : q ≤ s / B := (Nat.le_div_iff_mul_le hB).2 hqB
  exact hqdiv.trans hblock

/-- Lemma 5.1 with all finite quantifiers and the missing location condition
made explicit.  The two cases are exactly the forward-tail branch and the
reversed-prefix branch.  The hypotheses `N≥1` and `‖g‖>0` are the regime in
which the manuscript discards the unique possible zero-length cut. -/
theorem allCuts_clustered {k N : ℕ} (hN : 1 ≤ N)
    (α : CoefficientVector k) (hlarge : 0 < ‖g α N‖) :
    Nonempty (ForwardCluster k N α) ∨ Nonempty (BackwardCluster k N α) := by
  classical
  let B := 4 * k.factorial
  have hB : 0 < B := by
    dsimp [B]
    positivity
  obtain hforward | hbackward := exists_many_oriented_weyl_cuts α hlarge
  · left
    let cuts := largeTailCuts (weylSequence α N) ‖g α N‖
    let X₀ : Finset (Fin (N + 2)) := cuts.image forwardCentre
    obtain ⟨b, hblockCard, hlocation, hshort⟩ :=
      exists_dense_factorial_block k N hN X₀
    let X := blockFiber (by positivity : 0 < 4 * k.factorial) X₀ b
    have hX₀card : X₀.card = cuts.card := by
      exact Finset.card_image_of_injective cuts forwardCentre_injective
    have hcardRaw : (N + 1) / (2 * B) ≤ X.card := by
      apply orientation_card_div_le hB
      · simpa only [cuts] using hforward.1
      · have hc : X₀.card / B ≤ X.card := by
          simpa only [B, X] using hblockCard
        rwa [hX₀card] at hc
    have hcard : (N + 1) / (8 * k.factorial) ≤ X.card := by
      simpa only [B, show 2 * (4 * k.factorial) = 8 * k.factorial by ring]
        using hcardRaw
    refine ⟨{
      X := X
      card_lower := hcard
      location := ?_
      short := ?_
      partial_sum := ?_ }⟩
    · intro x hx
      exact hlocation x hx
    · intro x hx y hy
      exact hshort x hx y hy
    · intro x hx
      have hx₀ : x ∈ X₀ := by
        exact blockFiber_subset (by positivity : 0 < 4 * k.factorial) X₀ b hx
      obtain ⟨m, hm, hmx⟩ := Finset.mem_image.mp hx₀
      have hmdata := hforward.2 m (by simpa only [cuts] using hm)
      refine ⟨m, ?_, hmx, hmdata.1, hmdata.2.1⟩
      simpa only [cuts] using hm
  · right
    let cuts := largePrefixCuts (weylSequence α N) ‖g α N‖
    let X₀ : Finset (Fin (N + 2)) := cuts.image backwardCentre
    obtain ⟨b, hblockCard, hlocation, hshort⟩ :=
      exists_dense_factorial_block k N hN X₀
    let X := blockFiber (by positivity : 0 < 4 * k.factorial) X₀ b
    have hX₀card : X₀.card = cuts.card := by
      exact Finset.card_image_of_injective cuts backwardCentre_injective
    have hcardRaw : (N + 1) / (2 * B) ≤ X.card := by
      apply orientation_card_div_le hB
      · simpa only [cuts] using hbackward.1
      · have hc : X₀.card / B ≤ X.card := by
          simpa only [B, X] using hblockCard
        rwa [hX₀card] at hc
    have hcard : (N + 1) / (8 * k.factorial) ≤ X.card := by
      simpa only [B, show 2 * (4 * k.factorial) = 8 * k.factorial by ring]
        using hcardRaw
    refine ⟨{
      X := X
      card_lower := hcard
      location := ?_
      short := ?_
      partial_sum := ?_ }⟩
    · intro x hx
      exact hlocation x hx
    · intro x hx y hy
      exact hshort x hx y hy
    · intro x hx
      have hx₀ : x ∈ X₀ := by
        exact blockFiber_subset (by positivity : 0 < 4 * k.factorial) X₀ b hx
      obtain ⟨m, hm, hmx⟩ := Finset.mem_image.mp hx₀
      have hmdata := hbackward.2 m (by simpa only [cuts] using hm)
      refine ⟨m, ?_, hmx, hmdata.1, hmdata.2.1⟩
      simpa only [cuts] using hm

end

end AllCuts
end ImprovedWeylBounds
