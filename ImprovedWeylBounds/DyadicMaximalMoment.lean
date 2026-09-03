import ImprovedWeylBounds.MaximalMomentWeighted
import ImprovedWeylBounds.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# A concrete dyadic grid for maximal fibre moments

This module closes the combinatorial bridge left abstract in
`MaximalMomentWeighted.lean`.  A block of level `j` has length `2^j` and
starts at a multiple of that length.  The binary expansion of every prefix
gives a disjoint concatenation into such blocks.  The common block pool is
finite and has exactly `N / 2^j` blocks at level `j`.
-/

open scoped BigOperators
open MeasureTheory Filter

namespace ImprovedWeylBounds

attribute [local instance] Classical.propDecidable

noncomputable local instance : IsProbabilityMeasure unitHaar := by
  dsimp [unitHaar]
  infer_instance

noncomputable local instance (r : ℕ) : IsProbabilityMeasure (torusHaar r) := by
  dsimp [torusHaar]
  infer_instance

/-! ## The finite dyadic block pool -/

/-- At level `j`, the ambient interval has `N / 2^j` complete aligned
blocks. -/
abbrev DyadicBlock (N : ℕ) :=
  Σ j : Fin (Nat.log2 N + 1), Fin (N / 2 ^ j.val)

def dyadicBlockLevel {N : ℕ} (b : DyadicBlock N) : ℕ := b.1.val

def dyadicBlockLength {N : ℕ} (b : DyadicBlock N) : ℕ :=
  2 ^ dyadicBlockLevel b

def dyadicBlockStartNat {N : ℕ} (b : DyadicBlock N) : ℕ :=
  b.2.val * dyadicBlockLength b

def dyadicBlockStart {N : ℕ} (b : DyadicBlock N) : ℤ :=
  dyadicBlockStartNat b

@[simp]
theorem dyadicBlockLength_pos {N : ℕ} (b : DyadicBlock N) :
    1 ≤ dyadicBlockLength b := by
  have h : 0 < 2 ^ dyadicBlockLevel b := pow_pos (by omega) _
  change 1 ≤ 2 ^ dyadicBlockLevel b
  omega

theorem dyadicBlockLength_le {N : ℕ} (hN : 1 ≤ N)
    (b : DyadicBlock N) : dyadicBlockLength b ≤ N := by
  apply (Nat.le_log2 (by omega : N ≠ 0)).1
  exact Nat.le_of_lt_succ b.1.isLt

/-! ## Binary prefix chunks -/

/-- Given decreasing binary levels, list the corresponding consecutive
chunks beginning at `a`.  A pair stores `(start, level)`. -/
def dyadicChunksFrom : ℕ → List ℕ → List (ℕ × ℕ)
  | _, [] => []
  | a, j :: js => (a, j) :: dyadicChunksFrom (a + 2 ^ j) js

/-- The chunks associated with the binary expansion of `L`, ordered from
largest to smallest. -/
def prefixDyadicChunks (L : ℕ) : List (ℕ × ℕ) :=
  dyadicChunksFrom 0 L.bitIndices.reverse

@[simp]
theorem length_dyadicChunksFrom (a : ℕ) (js : List ℕ) :
    (dyadicChunksFrom a js).length = js.length := by
  induction js generalizing a with
  | nil => rfl
  | cons j js ih => simp [dyadicChunksFrom, ih]

theorem snd_mem_of_mem_dyadicChunksFrom {a : ℕ} {js : List ℕ}
    {b : ℕ × ℕ} (hb : b ∈ dyadicChunksFrom a js) : b.2 ∈ js := by
  induction js generalizing a with
  | nil => simp [dyadicChunksFrom] at hb
  | cons j js ih =>
      simp only [dyadicChunksFrom, List.mem_cons] at hb
      rcases hb with rfl | hb
      · simp
      · exact List.mem_cons_of_mem j (ih hb)

theorem dyadicChunksFrom_nodup {a : ℕ} {js : List ℕ} (hjs : js.Nodup) :
    (dyadicChunksFrom a js).Nodup := by
  induction js generalizing a with
  | nil => simp [dyadicChunksFrom]
  | cons j js ih =>
      rw [List.nodup_cons] at hjs
      rw [dyadicChunksFrom, List.nodup_cons]
      constructor
      · intro hmem
        exact hjs.1 (snd_mem_of_mem_dyadicChunksFrom hmem)
      · exact ih hjs.2

@[simp]
theorem prefixDyadicChunks_nodup (L : ℕ) :
    (prefixDyadicChunks L).Nodup := by
  apply dyadicChunksFrom_nodup
  exact List.nodup_reverse.mpr Nat.bitIndices_nodup

def dyadicLevelSum (js : List ℕ) : ℕ :=
  (js.map fun j => 2 ^ j).sum

@[simp]
theorem dyadicLevelSum_bitIndices_reverse (L : ℕ) :
    dyadicLevelSum L.bitIndices.reverse = L := by
  rw [dyadicLevelSum, List.map_reverse, List.sum_reverse]
  exact Nat.sum_map_two_pow_bitIndices L

theorem dyadicChunksFrom_end_le {a : ℕ} {js : List ℕ}
    {b : ℕ × ℕ} (hb : b ∈ dyadicChunksFrom a js) :
    b.1 + 2 ^ b.2 ≤ a + dyadicLevelSum js := by
  induction js generalizing a with
  | nil => simp [dyadicChunksFrom] at hb
  | cons j js ih =>
      simp only [dyadicChunksFrom, List.mem_cons] at hb
      rcases hb with rfl | hb
      · simp [dyadicLevelSum]
      · have h := ih hb
        simpa [dyadicLevelSum, add_assoc] using h

theorem prefixDyadicChunk_end_le {L : ℕ} {b : ℕ × ℕ}
    (hb : b ∈ prefixDyadicChunks L) : b.1 + 2 ^ b.2 ≤ L := by
  have h := dyadicChunksFrom_end_le hb
  simpa [prefixDyadicChunks] using h

theorem prefixDyadicChunk_level_mem {L : ℕ} {b : ℕ × ℕ}
    (hb : b ∈ prefixDyadicChunks L) : b.2 ∈ L.bitIndices := by
  have h := snd_mem_of_mem_dyadicChunksFrom hb
  simpa [prefixDyadicChunks] using h

private theorem dyadicChunksFrom_aligned_aux
    {a : ℕ} {js : List ℕ} (hdesc : js.Pairwise (· > ·))
    (ha : ∀ j ∈ js, 2 ^ j ∣ a) {b : ℕ × ℕ}
    (hb : b ∈ dyadicChunksFrom a js) : 2 ^ b.2 ∣ b.1 := by
  induction js generalizing a b with
  | nil => simp [dyadicChunksFrom] at hb
  | cons j js ih =>
      rw [List.pairwise_cons] at hdesc
      simp only [dyadicChunksFrom, List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact ha j (by simp)
      · apply ih hdesc.2 _ hb
        intro i hi
        exact (ha i (by simp [hi])).add
          ((Nat.pow_dvd_pow 2 (hdesc.1 i hi).le))

theorem prefixDyadicChunk_aligned {L : ℕ} {b : ℕ × ℕ}
    (hb : b ∈ prefixDyadicChunks L) : 2 ^ b.2 ∣ b.1 := by
  have hdesc : L.bitIndices.reverse.Pairwise (· > ·) := by
    rw [List.pairwise_reverse]
    have hinc : L.bitIndices.Pairwise (· < ·) :=
      (Nat.bitIndices_sorted (n := L)).pairwise
    simpa [Function.swap_def] using hinc
  exact dyadicChunksFrom_aligned_aux hdesc (by simp) hb

/-! ## Embedding prefix chunks into the common grid -/

private theorem prefixChunk_level_lt (N : ℕ) (L : Fin (N + 1))
    (b : {b // b ∈ prefixDyadicChunks L.val}) :
    b.val.2 < Nat.log2 N + 1 := by
  have hpowL := Nat.two_pow_le_of_mem_bitIndices
    (prefixDyadicChunk_level_mem b.property)
  have hpowN : 2 ^ b.val.2 ≤ N := hpowL.trans (by omega)
  have hN : N ≠ 0 := by
    intro h
    subst N
    have hpos : 0 < 2 ^ b.val.2 := pow_pos (by omega) _
    omega
  exact Nat.lt_succ_of_le ((Nat.le_log2 hN).2 hpowN)

noncomputable def prefixChunkToDyadicBlock (N : ℕ) (L : Fin (N + 1))
    (b : {b // b ∈ prefixDyadicChunks L.val}) : DyadicBlock N := by
  let j : Fin (Nat.log2 N + 1) :=
    ⟨b.val.2, prefixChunk_level_lt N L b⟩
  let q := b.val.1 / 2 ^ b.val.2
  have halign : 2 ^ b.val.2 ∣ b.val.1 :=
    prefixDyadicChunk_aligned b.property
  have hrewrite : q * 2 ^ b.val.2 = b.val.1 := by
    exact Nat.div_mul_cancel halign
  have hend : b.val.1 + 2 ^ b.val.2 ≤ N :=
    (prefixDyadicChunk_end_le b.property).trans (by omega)
  have hq : q < N / 2 ^ b.val.2 := by
    have hqsucc : q + 1 ≤ N / 2 ^ b.val.2 := by
      rw [Nat.le_div_iff_mul_le (by positivity)]
      rw [add_mul, one_mul, hrewrite]
      exact hend
    omega
  exact ⟨j, ⟨q, by simpa [j] using hq⟩⟩

@[simp]
theorem prefixChunkToDyadicBlock_level (N : ℕ) (L : Fin (N + 1))
    (b : {b // b ∈ prefixDyadicChunks L.val}) :
    dyadicBlockLevel (prefixChunkToDyadicBlock N L b) = b.val.2 := by
  rfl

@[simp]
theorem prefixChunkToDyadicBlock_length (N : ℕ) (L : Fin (N + 1))
    (b : {b // b ∈ prefixDyadicChunks L.val}) :
    dyadicBlockLength (prefixChunkToDyadicBlock N L b) = 2 ^ b.val.2 := by
  rfl

@[simp]
theorem prefixChunkToDyadicBlock_startNat (N : ℕ) (L : Fin (N + 1))
    (b : {b // b ∈ prefixDyadicChunks L.val}) :
    dyadicBlockStartNat (prefixChunkToDyadicBlock N L b) = b.val.1 := by
  unfold dyadicBlockStartNat prefixChunkToDyadicBlock
  dsimp only
  exact Nat.div_mul_cancel (prefixDyadicChunk_aligned b.property)

@[simp]
theorem prefixChunkToDyadicBlock_start (N : ℕ) (L : Fin (N + 1))
    (b : {b // b ∈ prefixDyadicChunks L.val}) :
    dyadicBlockStart (prefixChunkToDyadicBlock N L b) = (b.val.1 : ℤ) := by
  simp [dyadicBlockStart]

noncomputable def prefixDyadicBlockList (N : ℕ) (L : Fin (N + 1)) :
    List (DyadicBlock N) :=
  (prefixDyadicChunks L.val).attach.map (prefixChunkToDyadicBlock N L)

theorem prefixChunkToDyadicBlock_injective (N : ℕ) (L : Fin (N + 1)) :
    Function.Injective (prefixChunkToDyadicBlock N L) := by
  intro b c h
  apply Subtype.ext
  apply Prod.ext
  · have hs := congrArg dyadicBlockStartNat h
    simpa using hs
  · have hl := congrArg dyadicBlockLevel h
    simpa using hl

@[simp]
theorem prefixDyadicBlockList_nodup (N : ℕ) (L : Fin (N + 1)) :
    (prefixDyadicBlockList N L).Nodup := by
  apply List.Nodup.map (prefixChunkToDyadicBlock_injective N L)
  rw [List.nodup_attach]
  exact prefixDyadicChunks_nodup L.val

noncomputable def prefixDyadicPieces (N : ℕ) (L : Fin (N + 1)) :
    Finset (DyadicBlock N) :=
  (prefixDyadicBlockList N L).toFinset

theorem prefixDyadicPieces_card_le (N : ℕ) (L : Fin (N + 1)) :
    (prefixDyadicPieces N L).card ≤ Nat.log2 N + 1 := by
  rw [prefixDyadicPieces,
    List.toFinset_card_of_nodup (prefixDyadicBlockList_nodup N L)]
  simp only [prefixDyadicBlockList, List.length_map, List.length_attach,
    length_dyadicChunksFrom, prefixDyadicChunks, List.length_reverse]
  rw [← List.toFinset_card_of_nodup (Nat.bitIndices_nodup (n := L.val))]
  have hsubset : L.val.bitIndices.toFinset ⊆
      Finset.range (Nat.log2 N + 1) := by
    intro j hj
    simp only [List.mem_toFinset] at hj
    simp only [Finset.mem_range]
    have hjpow := Nat.two_pow_le_of_mem_bitIndices hj
    have hN : N ≠ 0 := by
      intro h
      subst N
      have hpos : 0 < 2 ^ j := pow_pos (by omega) _
      omega
    exact Nat.lt_succ_of_le ((Nat.le_log2 hN).2 (hjpow.trans (by omega)))
  simpa using Finset.card_le_card hsubset

/-! ## Exact decomposition of the fibre sums -/

noncomputable def translatedFibreTerm (r : ℕ) (c : ℤ)
    (θ : UnitAddCircle) (β : Fin r → UnitAddCircle) (n : ℕ) : ℂ :=
  fourier ((((n + 1 : ℕ) : ℤ) + c) ^ (r + 1)) θ *
    torusCharacter
      (fun j => ((((n + 1 : ℕ) : ℤ) + c) ^ (j.val + 1))) β

theorem translatedFixedLeadingFibreSum_eq_sum_range
    (r N : ℕ) (c : ℤ) (θ : UnitAddCircle)
    (β : Fin r → UnitAddCircle) :
    translatedFixedLeadingFibreSum r N c θ β =
      ∑ n ∈ Finset.range N, translatedFibreTerm r c θ β n := by
  rw [translatedFixedLeadingFibreSum, torusPolynomial]
  change (∑ x : Fin N, translatedFibreTerm r c θ β x.val) = _
  rw [Fin.sum_univ_eq_sum_range]

theorem translatedFibreTerm_shift (r a n : ℕ) (c : ℤ)
    (θ : UnitAddCircle) (β : Fin r → UnitAddCircle) :
    translatedFibreTerm r c θ β (a + n) =
      translatedFibreTerm r (c + a) θ β n := by
  unfold translatedFibreTerm
  congr 1
  · congr 2 <;> push_cast <;> ring
  · congr 1
    funext j
    congr 1 <;> push_cast <;> ring

theorem translatedFixedLeadingFibreSum_add_length
    (r A B : ℕ) (c : ℤ) (θ : UnitAddCircle)
    (β : Fin r → UnitAddCircle) :
    translatedFixedLeadingFibreSum r (A + B) c θ β =
      translatedFixedLeadingFibreSum r A c θ β +
        translatedFixedLeadingFibreSum r B (c + A) θ β := by
  simp only [translatedFixedLeadingFibreSum_eq_sum_range]
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  exact translatedFibreTerm_shift r A n c θ β

theorem sum_dyadicChunksFrom_fibre
    (r a : ℕ) (js : List ℕ) (hjs : js.Nodup)
    (θ : UnitAddCircle) (β : Fin r → UnitAddCircle) :
    ∑ b ∈ (dyadicChunksFrom a js).toFinset,
        translatedFixedLeadingFibreSum r (2 ^ b.2) b.1 θ β =
      translatedFixedLeadingFibreSum r (dyadicLevelSum js) a θ β := by
  induction js generalizing a with
  | nil => simp [dyadicChunksFrom, dyadicLevelSum,
      translatedFixedLeadingFibreSum_eq_sum_range]
  | cons j js ih =>
      rw [List.nodup_cons] at hjs
      rw [dyadicChunksFrom, List.toFinset_cons]
      have hnot : (a, j) ∉ (dyadicChunksFrom (a + 2 ^ j) js).toFinset := by
        intro h
        have hm : (a, j) ∈ dyadicChunksFrom (a + 2 ^ j) js := by simpa using h
        exact hjs.1 (snd_mem_of_mem_dyadicChunksFrom hm)
      rw [Finset.sum_insert hnot, ih (a := a + 2 ^ j) hjs.2]
      simp only [dyadicLevelSum, List.map_cons, List.sum_cons]
      exact (translatedFixedLeadingFibreSum_add_length
        r (2 ^ j) (dyadicLevelSum js) a θ β).symm

theorem fixedLeadingFibreSum_eq_translated_zero
    (r N : ℕ) (θ : UnitAddCircle) (β : Fin r → UnitAddCircle) :
    fixedLeadingFibreSum r N θ β =
      translatedFixedLeadingFibreSum r N 0 θ β := by
  simp only [fixedLeadingFibreSum, translatedFixedLeadingFibreSum,
    fixedLeadingWeight, translatedFixedLeadingWeight,
    monomialFrequency, translatedMonomialFrequency]
  rfl

theorem prefixDyadicPieces_decomposition
    (r N : ℕ) (L : Fin (N + 1)) (θ : UnitAddCircle)
    (β : Fin r → UnitAddCircle) :
    fixedLeadingFibreSum r L.val θ β =
      ∑ b ∈ prefixDyadicPieces N L,
        translatedFixedLeadingFibreSum r (dyadicBlockLength b)
          (dyadicBlockStart b) θ β := by
  rw [fixedLeadingFibreSum_eq_translated_zero]
  rw [prefixDyadicPieces]
  let f : DyadicBlock N → ℂ := fun b =>
    translatedFixedLeadingFibreSum r (dyadicBlockLength b)
      (dyadicBlockStart b) θ β
  rw [List.sum_toFinset f (prefixDyadicBlockList_nodup N L)]
  simp only [prefixDyadicBlockList, List.map_map]
  have hfun : (f ∘ prefixChunkToDyadicBlock N L) =
      (fun b : ℕ × ℕ =>
        translatedFixedLeadingFibreSum r (2 ^ b.2) b.1 θ β) ∘
          Subtype.val := by
    funext b
    simp [f]
  rw [hfun, ← List.map_map, List.attach_map_subtype_val]
  rw [← List.sum_toFinset
    (fun b : ℕ × ℕ =>
      translatedFixedLeadingFibreSum r (2 ^ b.2) b.1 θ β)
    (prefixDyadicChunks_nodup L.val)]
  simpa [prefixDyadicChunks] using
    (sum_dyadicChunksFrom_fibre r 0 L.val.bitIndices.reverse
      (List.nodup_reverse.mpr Nat.bitIndices_nodup) θ β).symm

/-! ## Length-weighted size of the grid -/

private theorem one_scale_dyadic_weight_le
    (N R : ℕ) (hN : 1 ≤ N) (hR : 1 ≤ R) (hRN : R ≤ N)
    (a : ℝ) (ha : 1 ≤ a) :
    ((N / R : ℕ) : ℝ) * Real.rpow (R : ℝ) a ≤
      Real.rpow (N : ℝ) a := by
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hRpos : 0 < (R : ℝ) := by exact_mod_cast hR
  have hsub : 0 ≤ a - 1 := sub_nonneg.mpr ha
  have hfloor : ((N / R : ℕ) : ℝ) * (R : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.div_mul_le_self N R
  have hrpow : Real.rpow (R : ℝ) a =
      (R : ℝ) * Real.rpow (R : ℝ) (a - 1) := by
    calc
      Real.rpow (R : ℝ) a =
          Real.rpow (R : ℝ) ((a - 1) + 1) := by congr 1 <;> linarith
      _ = Real.rpow (R : ℝ) (a - 1) * Real.rpow (R : ℝ) 1 :=
        Real.rpow_add hRpos (a - 1) 1
      _ = (R : ℝ) * Real.rpow (R : ℝ) (a - 1) := by
        calc
          _ = Real.rpow (R : ℝ) (a - 1) * (R : ℝ) := by
            congr 1
            exact Real.rpow_one (R : ℝ)
          _ = _ := by ring
  have hNrpow : Real.rpow (N : ℝ) a =
      (N : ℝ) * Real.rpow (N : ℝ) (a - 1) := by
    calc
      Real.rpow (N : ℝ) a =
          Real.rpow (N : ℝ) ((a - 1) + 1) := by congr 1 <;> linarith
      _ = Real.rpow (N : ℝ) (a - 1) * Real.rpow (N : ℝ) 1 :=
        Real.rpow_add hNpos (a - 1) 1
      _ = (N : ℝ) * Real.rpow (N : ℝ) (a - 1) := by
        calc
          _ = Real.rpow (N : ℝ) (a - 1) * (N : ℝ) := by
            congr 1
            exact Real.rpow_one (N : ℝ)
          _ = _ := by ring
  rw [hrpow, hNrpow]
  calc
    ((N / R : ℕ) : ℝ) * ((R : ℝ) * Real.rpow (R : ℝ) (a - 1)) =
        (((N / R : ℕ) : ℝ) * (R : ℝ)) *
          Real.rpow (R : ℝ) (a - 1) := by ring
    _ ≤ (N : ℝ) * Real.rpow (N : ℝ) (a - 1) := by
      apply mul_le_mul hfloor
      · exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hRN) hsub
      · exact (Real.rpow_pos_of_pos hRpos _).le
      · exact_mod_cast Nat.zero_le N

/-- At each scale the complete aligned blocks have total weighted mass at
most `N^a`; summing over the `log₂ N + 1` possible scales gives this exact
finite estimate. -/
theorem sum_dyadicBlockLength_rpow_le
    (N : ℕ) (hN : 1 ≤ N) (a : ℝ) (ha : 1 ≤ a) :
    ∑ b : DyadicBlock N,
        Real.rpow (dyadicBlockLength b : ℝ) a ≤
      (Nat.log2 N + 1 : ℕ) * Real.rpow (N : ℝ) a := by
  rw [Fintype.sum_sigma]
  calc
    (∑ j : Fin (Nat.log2 N + 1),
        ∑ _m : Fin (N / 2 ^ j.val),
          Real.rpow ((2 ^ j.val : ℕ) : ℝ) a) =
        ∑ j : Fin (Nat.log2 N + 1),
          ((N / 2 ^ j.val : ℕ) : ℝ) *
            Real.rpow ((2 ^ j.val : ℕ) : ℝ) a := by
      apply Fintype.sum_congr
      intro j
      simp
    _ ≤ ∑ _j : Fin (Nat.log2 N + 1),
        Real.rpow (N : ℝ) a := by
      apply Finset.sum_le_sum
      intro j hj
      have hpow : 2 ^ j.val ≤ N := by
        apply (Nat.le_log2 (by omega : N ≠ 0)).1
        exact Nat.le_of_lt_succ j.isLt
      have hpowPos : 1 ≤ 2 ^ j.val := by
        have : 0 < 2 ^ j.val := pow_pos (by omega) _
        omega
      exact one_scale_dyadic_weight_le N (2 ^ j.val) hN hpowPos hpow a ha
    _ = (Nat.log2 N + 1 : ℕ) * Real.rpow (N : ℝ) a := by
      simp

/-! ## The concrete maximal theorem with its exact logarithmic factor -/

/-- The manuscript's dyadic maximal-fibre reduction with no asymptotic
notation hidden: the only loss before the final harmless absorption is the
displayed power `(log₂ N + 1)^(2s)`. -/
theorem maximalFixedLeadingFibre_criticalVMVT_log_bound
    (hVMVT : External.CriticalVMVT)
    (r : ℕ) (hr : 1 ≤ r) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 1 ≤ N → ∀ θ : UnitAddCircle,
      (∫ β,
        (Finset.univ : Finset (Fin (N + 1))).sup'
          (by simp)
          (fun L => ‖fixedLeadingFibreSum r L.val θ β‖ ^
            (2 * External.criticalMoment r)) ∂torusHaar r) ≤
        C * (((Nat.log2 N + 1 : ℕ) : ℝ) ^
            (2 * External.criticalMoment r)) *
          Real.rpow (N : ℝ)
            ((External.criticalMoment r : ℝ) + δ) := by
  obtain ⟨C, hC, hweighted⟩ :=
    maximalTranslatedFixedFibre_criticalVMVT_weighted hVMVT r hr δ hδ
  refine ⟨C, hC, ?_⟩
  intro N hN θ
  have hraw := hweighted
    (endpoints := (Finset.univ : Finset (Fin (N + 1))))
    (hendpoints := by simp)
    (blocks := (Finset.univ : Finset (DyadicBlock N)))
    (pieces := prefixDyadicPieces N)
    (blockStart := dyadicBlockStart)
    (blockLength := dyadicBlockLength)
    (L := Nat.log2 N + 1)
    (fun b _ => dyadicBlockLength_pos b) θ
    (fun L β => fixedLeadingFibreSum r L.val θ β)
    (fun _ => Finset.subset_univ _)
    (prefixDyadicPieces_card_le N)
    (fun L β => prefixDyadicPieces_decomposition r N L θ β)
  have hsum := sum_dyadicBlockLength_rpow_le N hN
    ((External.criticalMoment r : ℝ) + δ) (by
      have hs : 1 ≤ External.criticalMoment r := by
        have hprod : 2 ≤ r * (r + 1) := by
          calc
            2 = 1 * 2 := by omega
            _ ≤ r * (r + 1) := Nat.mul_le_mul hr (by omega)
        simp only [External.criticalMoment]
        omega
      exact le_add_of_le_of_nonneg (by exact_mod_cast hs) hδ.le)
  calc
    (∫ β,
        (Finset.univ : Finset (Fin (N + 1))).sup'
          (by simp)
          (fun L => ‖fixedLeadingFibreSum r L.val θ β‖ ^
            (2 * External.criticalMoment r)) ∂torusHaar r) ≤
        ((Nat.log2 N + 1 : ℕ) : ℝ) ^
            (2 * External.criticalMoment r - 1) * C *
          ∑ b ∈ (Finset.univ : Finset (DyadicBlock N)),
            Real.rpow (dyadicBlockLength b : ℝ)
              ((External.criticalMoment r : ℝ) + δ) := hraw
    _ ≤ ((Nat.log2 N + 1 : ℕ) : ℝ) ^
            (2 * External.criticalMoment r - 1) * C *
          (((Nat.log2 N + 1 : ℕ) : ℝ) *
            Real.rpow (N : ℝ)
              ((External.criticalMoment r : ℝ) + δ)) := by
      gcongr
    _ = C * (((Nat.log2 N + 1 : ℕ) : ℝ) ^
            (2 * External.criticalMoment r)) *
          Real.rpow (N : ℝ)
            ((External.criticalMoment r : ℝ) + δ) := by
      have hp : 1 ≤ 2 * External.criticalMoment r := by
        have hs : 1 ≤ External.criticalMoment r := by
          have hprod : 2 ≤ r * (r + 1) := by
            calc
              2 = 1 * 2 := by omega
              _ ≤ r * (r + 1) := Nat.mul_le_mul hr (by omega)
          simp only [External.criticalMoment]
          omega
        omega
      have he : 2 * External.criticalMoment r - 1 + 1 =
          2 * External.criticalMoment r := by omega
      calc
        _ = C *
            ((((Nat.log2 N + 1 : ℕ) : ℝ) ^
              (2 * External.criticalMoment r - 1)) *
              ((Nat.log2 N + 1 : ℕ) : ℝ)) *
            Real.rpow (N : ℝ)
              ((External.criticalMoment r : ℝ) + δ) := by ring
        _ = _ := by rw [← pow_succ, he]

/-! ## Absorbing the logarithmic factor -/

/-- Any fixed power of the number of binary scales is eventually smaller
than an arbitrarily small positive power of `N`. -/
theorem eventually_log2_add_one_pow_le_rpow
    (p : ℕ) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop,
      (((Nat.log2 N + 1 : ℕ) : ℝ) ^ p) ≤ Real.rpow (N : ℝ) η := by
  let D : ℝ := 2 / Real.log 2
  have hDpos : 0 < D := by
    dsimp [D]
    exact div_pos (by norm_num) (Real.log_pos (by norm_num))
  have hlittleReal := isLittleO_log_rpow_rpow_atTop (p : ℝ) hη
  have hlittleNat := hlittleReal.comp_tendsto tendsto_natCast_atTop_atTop
  have hscaled := hlittleNat.const_mul_left (D ^ p)
  filter_upwards [hscaled.eventuallyLE, eventually_ge_atTop (2 : ℕ)] with N hsmall hN
  have hNpos : 0 < (N : ℝ) := by positivity
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlogbOne : 1 ≤ Real.logb 2 (N : ℝ) := by
    calc
      1 = Real.logb 2 2 := (Real.logb_self_eq_one (by norm_num)).symm
      _ ≤ Real.logb 2 (N : ℝ) :=
        (Real.logb_le_logb (by norm_num) (by norm_num) hNpos).2
          (by exact_mod_cast hN)
  have hscales : ((Nat.log2 N + 1 : ℕ) : ℝ) ≤
      D * Real.log (N : ℝ) := by
    calc
      ((Nat.log2 N + 1 : ℕ) : ℝ) = (Nat.log2 N : ℝ) + 1 := by
        push_cast
        rfl
      _ ≤ Real.logb 2 (N : ℝ) + 1 := by
        gcongr
        exact Real.log2_le_logb N
      _ ≤ 2 * Real.logb 2 (N : ℝ) := by linarith
      _ = D * Real.log (N : ℝ) := by
        dsimp [D, Real.logb]
        field_simp
        <;> ring
  have hpowers : (((Nat.log2 N + 1 : ℕ) : ℝ) ^ p) ≤
      (D * Real.log (N : ℝ)) ^ p :=
    pow_le_pow_left₀ (by positivity) hscales p
  calc
    (((Nat.log2 N + 1 : ℕ) : ℝ) ^ p) ≤
        (D * Real.log (N : ℝ)) ^ p := hpowers
    _ = D ^ p * Real.rpow (Real.log (N : ℝ)) (p : ℝ) := by
      rw [mul_pow]
      congr 1
      exact (Real.rpow_natCast (Real.log (N : ℝ)) p).symm
    _ ≤ Real.rpow (N : ℝ) η := by
      simpa [Function.comp_apply, Real.norm_eq_abs,
        abs_of_pos hDpos, abs_of_pos hlogN,
        abs_of_pos (Real.rpow_pos_of_pos hNpos η)] using hsmall

/-- The maximal fixed-leading-coefficient moment bound in the manuscript's
final power-saving form, with the usual sufficiently-large-`N` quantifier
made explicit.  The constant and threshold are uniform in `θ`. -/
theorem maximalFixedLeadingFibre_criticalVMVT_eventual
    (hVMVT : External.CriticalVMVT)
    (r : ℕ) (hr : 1 ≤ r) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
      ∀ (N : ℕ), N₀ ≤ N → ∀ θ : UnitAddCircle,
        (∫ β,
          (Finset.univ : Finset (Fin (N + 1))).sup'
            (by simp)
            (fun L => ‖fixedLeadingFibreSum r L.val θ β‖ ^
              (2 * External.criticalMoment r)) ∂torusHaar r) ≤
          C * Real.rpow (N : ℝ)
            ((External.criticalMoment r : ℝ) + ε) := by
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨C, hC, hlog⟩ :=
    maximalFixedLeadingFibre_criticalVMVT_log_bound
      hVMVT r hr (ε / 2) hhalf
  have hscale := eventually_log2_add_one_pow_le_rpow
    (2 * External.criticalMoment r) (ε / 2) hhalf
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp hscale
  refine ⟨C, hC, max 1 N₁, by omega, ?_⟩
  intro N hN θ
  have hNone : 1 ≤ N := le_trans (le_max_left 1 N₁) hN
  have hscaleN : (((Nat.log2 N + 1 : ℕ) : ℝ) ^
      (2 * External.criticalMoment r)) ≤ Real.rpow (N : ℝ) (ε / 2) :=
    hN₁ N (le_trans (le_max_right 1 N₁) hN)
  have hbase := hlog N hNone θ
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hNone
  calc
    (∫ β,
        (Finset.univ : Finset (Fin (N + 1))).sup'
          (by simp)
          (fun L => ‖fixedLeadingFibreSum r L.val θ β‖ ^
            (2 * External.criticalMoment r)) ∂torusHaar r) ≤
        C * (((Nat.log2 N + 1 : ℕ) : ℝ) ^
            (2 * External.criticalMoment r)) *
          Real.rpow (N : ℝ)
            ((External.criticalMoment r : ℝ) + ε / 2) := hbase
    _ ≤ C * Real.rpow (N : ℝ) (ε / 2) *
          Real.rpow (N : ℝ)
            ((External.criticalMoment r : ℝ) + ε / 2) := by
      apply mul_le_mul_of_nonneg_right
      · exact mul_le_mul_of_nonneg_left hscaleN hC.le
      · exact (Real.rpow_pos_of_pos hNpos _).le
    _ = C * Real.rpow (N : ℝ)
          ((External.criticalMoment r : ℝ) + ε) := by
      calc
        C * Real.rpow (N : ℝ) (ε / 2) *
            Real.rpow (N : ℝ)
              ((External.criticalMoment r : ℝ) + ε / 2) =
            C * (Real.rpow (N : ℝ) (ε / 2) *
              Real.rpow (N : ℝ)
                ((External.criticalMoment r : ℝ) + ε / 2)) := by ring
        _ = C * Real.rpow (N : ℝ)
            ((ε / 2) + ((External.criticalMoment r : ℝ) + ε / 2)) := by
          congr 1
          exact (Real.rpow_add hNpos _ _).symm
        _ = _ := by congr 2 <;> ring

/-! ## Removing the large-`N` threshold -/

/-- The elementary pointwise bound for a fixed-leading fibre sum. -/
theorem norm_fixedLeadingFibreSum_le
    (r N : ℕ) (θ : UnitAddCircle) (β : Fin r → UnitAddCircle) :
    ‖fixedLeadingFibreSum r N θ β‖ ≤ N := by
  unfold fixedLeadingFibreSum torusPolynomial
  calc
    ‖∑ x : Fin N,
        fixedLeadingWeight r θ x *
          torusCharacter (monomialFrequency r x) β‖ ≤
        ∑ x : Fin N,
          ‖fixedLeadingWeight r θ x *
            torusCharacter (monomialFrequency r x) β‖ := norm_sum_le _ _
    _ = N := by
      simp [fixedLeadingWeight, torusCharacter]

/-- A uniform trivial bound for the maximal moment, used only to absorb the
finitely many values below the analytic threshold. -/
theorem integral_maximalFixedLeadingFibre_trivial
    (r N p : ℕ) (θ : UnitAddCircle) :
    (∫ β,
      (Finset.univ : Finset (Fin (N + 1))).sup'
        (by simp)
        (fun L => ‖fixedLeadingFibreSum r L.val θ β‖ ^ p)
        ∂torusHaar r) ≤ (N : ℝ) ^ p := by
  let F : (Fin r → UnitAddCircle) → ℝ := fun β =>
    (Finset.univ : Finset (Fin (N + 1))).sup'
      (by simp) (fun L => ‖fixedLeadingFibreSum r L.val θ β‖ ^ p)
  have hpartialContinuous (L : Fin (N + 1)) : Continuous (fun β =>
      ‖fixedLeadingFibreSum r L.val θ β‖ ^ p) := by
    change Continuous ((fun β =>
      ‖torusPolynomial (fixedLeadingWeight r θ)
        (monomialFrequency r) β‖) ^ p)
    exact (continuous_torusPolynomial
      (fixedLeadingWeight r θ) (monomialFrequency r)).norm.pow p
  have hFcont : Continuous F := by
    dsimp only [F]
    apply Continuous.finset_sup'_apply (by simp)
    intro L hL
    exact hpartialContinuous L
  have hFint : Integrable F (torusHaar r) := by
    simpa using hFcont.continuousOn.integrableOn_compact isCompact_univ
  have hpoint (β : Fin r → UnitAddCircle) : F β ≤ (N : ℝ) ^ p := by
    dsimp only [F]
    apply Finset.sup'_le (by simp)
    intro L hL
    calc
      ‖fixedLeadingFibreSum r L.val θ β‖ ^ p ≤ (L.val : ℝ) ^ p :=
        pow_le_pow_left₀ (norm_nonneg _)
          (norm_fixedLeadingFibreSum_le r L.val θ β) p
      _ ≤ (N : ℝ) ^ p := by
        gcongr
        omega
  calc
    (∫ β,
      (Finset.univ : Finset (Fin (N + 1))).sup'
        (by simp)
        (fun L => ‖fixedLeadingFibreSum r L.val θ β‖ ^ p)
        ∂torusHaar r) = ∫ β, F β ∂torusHaar r := rfl
    _ ≤ ∫ _β : Fin r → UnitAddCircle, (N : ℝ) ^ p ∂torusHaar r := by
      apply MeasureTheory.integral_mono hFint (MeasureTheory.integrable_const _)
      exact hpoint
    _ = (N : ℝ) ^ p := by simp

/-- The fully uniform theorem stated in the manuscript.  It is conditional
only on the accurately stated external critical VMVT; the dyadic
decomposition, weighted scale sum, logarithmic absorption, and finite
small-`N` range are all discharged internally. -/
theorem maximalFixedLeadingFibre_criticalVMVT
    (hVMVT : External.CriticalVMVT)
    (r : ℕ) (hr : 1 ≤ r) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 1 ≤ N → ∀ θ : UnitAddCircle,
      (∫ β,
        (Finset.univ : Finset (Fin (N + 1))).sup'
          (by simp)
          (fun L => ‖fixedLeadingFibreSum r L.val θ β‖ ^
            (2 * External.criticalMoment r)) ∂torusHaar r) ≤
        C * Real.rpow (N : ℝ)
          ((External.criticalMoment r : ℝ) + ε) := by
  obtain ⟨C, hC, N₀, hN₀, hlarge⟩ :=
    maximalFixedLeadingFibre_criticalVMVT_eventual hVMVT r hr ε hε
  let p := 2 * External.criticalMoment r
  let C' : ℝ := C + (N₀ : ℝ) ^ p + 1
  have hC' : 0 < C' := by
    dsimp [C']
    positivity
  refine ⟨C', hC', ?_⟩
  intro N hN θ
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hexp : 0 ≤ (External.criticalMoment r : ℝ) + ε := by
    have hs : 1 ≤ External.criticalMoment r := by
      have hprod : 2 ≤ r * (r + 1) := by
        calc
          2 = 1 * 2 := by omega
          _ ≤ r * (r + 1) := Nat.mul_le_mul hr (by omega)
      simp only [External.criticalMoment]
      omega
    positivity
  by_cases hthreshold : N₀ ≤ N
  · calc
      (∫ β,
        (Finset.univ : Finset (Fin (N + 1))).sup'
          (by simp)
          (fun L => ‖fixedLeadingFibreSum r L.val θ β‖ ^
            (2 * External.criticalMoment r)) ∂torusHaar r) ≤
          C * Real.rpow (N : ℝ)
            ((External.criticalMoment r : ℝ) + ε) := hlarge N hthreshold θ
      _ ≤ C' * Real.rpow (N : ℝ)
            ((External.criticalMoment r : ℝ) + ε) := by
        apply mul_le_mul_of_nonneg_right _
          (Real.rpow_pos_of_pos hNpos _).le
        dsimp [C']
        have hpowNonneg : 0 ≤ (N₀ : ℝ) ^ p := by positivity
        linarith
  · have hNN₀ : N ≤ N₀ := by omega
    have hpow : (N : ℝ) ^ p ≤ (N₀ : ℝ) ^ p := by
      gcongr
    have hone : 1 ≤ Real.rpow (N : ℝ)
        ((External.criticalMoment r : ℝ) + ε) :=
      Real.one_le_rpow (by exact_mod_cast hN) hexp
    calc
      (∫ β,
        (Finset.univ : Finset (Fin (N + 1))).sup'
          (by simp)
          (fun L => ‖fixedLeadingFibreSum r L.val θ β‖ ^
            (2 * External.criticalMoment r)) ∂torusHaar r) ≤
          (N : ℝ) ^ p :=
        integral_maximalFixedLeadingFibre_trivial r N p θ
      _ ≤ (N₀ : ℝ) ^ p := hpow
      _ ≤ C' := by
        dsimp [C']
        linarith [hC]
      _ ≤ C' * Real.rpow (N : ℝ)
            ((External.criticalMoment r : ℝ) + ε) := by
        nlinarith [hC'.le, hone]

end ImprovedWeylBounds
