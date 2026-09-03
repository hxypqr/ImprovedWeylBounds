import ImprovedWeylBounds.ReproducingKernel

/-!
# Anisotropic sampling on a finite torus

This file formalizes the packing argument in `main.tex`, Proposition 4.2
(lines 761--805).  Its analytic input is the explicit kernel proved in
`ReproducingKernel.lean`; no sampling or large-sieve assertion is assumed.
-/

open scoped BigOperators Convolution
open MeasureTheory

namespace ImprovedWeylBounds
namespace Sampling

noncomputable local instance : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The summable lattice weight produced by quadratic kernel decay. -/
noncomputable def latticeWeight (z : ℤ) : ℝ :=
  1 / (1 + (z : ℝ) ^ 2)

lemma latticeWeight_nonneg (z : ℤ) : 0 ≤ latticeWeight z := by
  unfold latticeWeight
  positivity

lemma latticeWeight_neg (z : ℤ) : latticeWeight (-z) = latticeWeight z := by
  unfold latticeWeight
  push_cast
  ring_nf

/-- Elementary finite form of `∑_{n≥1} n⁻² ≤ 2`. -/
lemma sum_range_inv_sq_le_two (B : ℕ) :
    (∑ m ∈ Finset.range B, 1 / ((m + 1 : ℕ) : ℝ) ^ 2) ≤ 2 := by
  have hterm (m : ℕ) :
      1 / ((m + 1 : ℕ) : ℝ) ^ 2 ≤
        2 * (1 / ((m + 1 : ℕ) : ℝ) - 1 / ((m + 2 : ℕ) : ℝ)) := by
    have h1 : (0 : ℝ) < (m + 1 : ℕ) := by positivity
    have h2 : (0 : ℝ) < (m + 2 : ℕ) := by positivity
    have hm : (1 : ℝ) ≤ (m + 1 : ℕ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
    field_simp
    push_cast at *
    nlinarith
  calc
    (∑ m ∈ Finset.range B, 1 / ((m + 1 : ℕ) : ℝ) ^ 2) ≤
        ∑ m ∈ Finset.range B,
          2 * (1 / ((m + 1 : ℕ) : ℝ) - 1 / ((m + 2 : ℕ) : ℝ)) := by
      gcongr with m hm
      exact hterm m
    _ = 2 * (1 - 1 / ((B + 1 : ℕ) : ℝ)) := by
      induction B with
      | zero => norm_num
      | succ B ih =>
          rw [Finset.sum_range_succ, ih]
          push_cast
          ring
    _ ≤ 2 := by
      have : 0 ≤ 1 / ((B + 1 : ℕ) : ℝ) := by positivity
      linarith

/-- A symmetric interval of lattice weights has a uniform mass bound. -/
lemma sum_latticeWeight_Icc_le_five (B : ℕ) :
    (∑ z ∈ Finset.Icc (-(B : ℤ)) (B : ℤ), latticeWeight z) ≤ 5 := by
  have heven : Function.Even latticeWeight := by
    intro z
    exact latticeWeight_neg z
  rw [Finset.sum_Icc_of_even_eq_range heven]
  have hterm (m : ℕ) :
      latticeWeight ((m + 1 : ℕ) : ℤ) ≤
        1 / ((m + 1 : ℕ) : ℝ) ^ 2 := by
    unfold latticeWeight
    push_cast
    have hpos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) ^ 2 := by positivity
    norm_num [Nat.cast_add, Nat.cast_one] at hpos ⊢
    have h := one_div_le_one_div_of_le
      (a := ((m : ℝ) + 1) ^ 2) (b := 1 + ((m : ℝ) + 1) ^ 2)
      (by positivity) (by nlinarith)
    norm_num at h
    exact h
  have htail :
      (∑ m ∈ Finset.range B, latticeWeight ((m + 1 : ℕ) : ℤ)) ≤ 2 := by
    calc
      (∑ m ∈ Finset.range B, latticeWeight ((m + 1 : ℕ) : ℤ)) ≤
          ∑ m ∈ Finset.range B, 1 / ((m + 1 : ℕ) : ℝ) ^ 2 := by
        gcongr with m hm
        exact hterm m
      _ ≤ 2 := sum_range_inv_sq_le_two B
  rw [Finset.sum_range_succ']
  have hzero : latticeWeight 0 = 1 := by norm_num [latticeWeight]
  have hzero' : latticeWeight (((0 : ℕ) : ℤ)) = 1 := by
    norm_num [latticeWeight]
  rw [hzero']
  simp only [nsmul_eq_mul]
  norm_num only [Nat.cast_ofNat]
  linarith

/-- The centered integer cube used to receive the cell code. -/
noncomputable def integerCube (r B : ℕ) : Finset (Fin r → ℤ) :=
  Fintype.piFinset fun _ : Fin r => Finset.Icc (-(B : ℤ)) (B : ℤ)

/-- Tensorization of the one-dimensional lattice bound. -/
lemma sum_integerCube_latticeWeight_le (r B : ℕ) :
    (∑ z ∈ integerCube r B, ∏ j : Fin r, latticeWeight (z j)) ≤ 5 ^ r := by
  classical
  rw [integerCube, Finset.sum_prod_piFinset]
  have hcoord (j : Fin r) :
      (∑ z ∈ Finset.Icc (-(B : ℤ)) (B : ℤ), latticeWeight z) ≤ 5 :=
    sum_latticeWeight_Icc_le_five B
  calc
    (∏ _j : Fin r,
        ∑ z ∈ Finset.Icc (-(B : ℤ)) (B : ℤ), latticeWeight z) ≤
        ∏ _j : Fin r, (5 : ℝ) := by
      gcongr with j
      · intro j hj
        exact Finset.sum_nonneg fun _ _ => latticeWeight_nonneg _
      · exact hcoord j
    _ = 5 ^ r := by simp

/-- An injective finite collection of integer cells inherits the product
weight bound for the full cube containing it. -/
lemma sum_latticeWeight_comp_injective_le
    {ι : Type*} [Fintype ι] (r B : ℕ) (code : ι → Fin r → ℤ)
    (hcode : Function.Injective code)
    (hB : ∀ i j, (code i j).natAbs ≤ B) :
    (∑ i : ι, ∏ j : Fin r, latticeWeight (code i j)) ≤ 5 ^ r := by
  classical
  have himage : Finset.univ.image code ⊆ integerCube r B := by
    intro z hz
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hz
    obtain ⟨i, rfl⟩ := hz
    simp only [integerCube, Fintype.mem_piFinset, Finset.mem_Icc]
    intro j
    have hj := hB i j
    have hc : ((code i j).natAbs : ℤ) ≤ (B : ℤ) := by exact_mod_cast hj
    have habs : |code i j| ≤ (B : ℤ) := by
      simpa only [Int.natCast_natAbs] using hc
    exact (abs_le.mp habs)
  calc
    (∑ i : ι, ∏ j : Fin r, latticeWeight (code i j)) =
        ∑ z ∈ Finset.univ.image code, ∏ j : Fin r, latticeWeight (z j) := by
      rw [Finset.sum_image]
      intro a ha b hb hab
      exact hcode hab
    _ ≤ ∑ z ∈ integerCube r B, ∏ j : Fin r, latticeWeight (z j) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg himage
      intro z hz hzcube
      exact Finset.prod_nonneg fun j hj => latticeWeight_nonneg _
    _ ≤ 5 ^ r := sum_integerCube_latticeWeight_le r B

/-- The representative of a circle point in `(-1/2,1/2]`. -/
noncomputable def centeredRepresentative (x : UnitAddCircle) : ℝ :=
  (AddCircle.equivIoc (1 : ℝ) (-(1 / 2 : ℝ)) x : ℝ)

lemma centeredRepresentative_mem (x : UnitAddCircle) :
    centeredRepresentative x ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) := by
  have hx := (AddCircle.equivIoc (1 : ℝ) (-(1 / 2 : ℝ)) x).property
  change -(1 / 2 : ℝ) < centeredRepresentative x ∧
    centeredRepresentative x ≤ -(1 / 2 : ℝ) + 1 at hx
  change -(1 / 2 : ℝ) < centeredRepresentative x ∧
    centeredRepresentative x ≤ 1 / 2
  constructor
  · exact hx.1
  · linarith [hx.2]

@[simp]
lemma coe_centeredRepresentative (x : UnitAddCircle) :
    (centeredRepresentative x : UnitAddCircle) = x := by
  exact AddCircle.coe_equivIoc

lemma norm_eq_abs_centeredRepresentative (x : UnitAddCircle) :
    ‖x‖ = |centeredRepresentative x| := by
  calc
    ‖x‖ = ‖(centeredRepresentative x : UnitAddCircle)‖ := by
      rw [coe_centeredRepresentative]
    _ = |centeredRepresentative x| :=
      (AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ)) one_ne_zero).2 (by
        norm_num
        rw [abs_le]
        have hx := centeredRepresentative_mem x
        exact ⟨hx.1.le, hx.2⟩)

/-- Paper's anisotropic max-metric separation, written in the logically
equivalent witness-coordinate form. -/
def AnisotropicallySeparated
    {ι : Type*} {r : ℕ} (δ : ℝ) (L : Fin r → ℕ)
    (x : ι → Fin r → UnitAddCircle) : Prop :=
  ∀ ⦃a b : ι⦄, a ≠ b →
    ∃ j : Fin r, δ ≤ (L j : ℝ) * ‖x a j - x b j‖

/-- Integer cell occupied by a sample point, relative to a base point `y`. -/
noncomputable def cellCode
    {ι : Type*} {r : ℕ} (δ : ℝ) (L : Fin r → ℕ)
    (x : ι → Fin r → UnitAddCircle) (y : Fin r → UnitAddCircle)
    (i : ι) (j : Fin r) : ℤ :=
  ⌊(L j : ℝ) * centeredRepresentative (x i j - y j) / δ⌋

/-- Equal floor cells have scaled real representatives less than `δ` apart. -/
lemma abs_scaledRepresentative_sub_lt_of_cellCode_eq
    {ι : Type*} {r : ℕ} {δ : ℝ} (hδ : 0 < δ) (L : Fin r → ℕ)
    (x : ι → Fin r → UnitAddCircle) (y : Fin r → UnitAddCircle)
    {a b : ι} {j : Fin r}
    (hcell : cellCode δ L x y a j = cellCode δ L x y b j) :
    |(L j : ℝ) * centeredRepresentative (x a j - y j) -
        (L j : ℝ) * centeredRepresentative (x b j - y j)| < δ := by
  let sa := (L j : ℝ) * centeredRepresentative (x a j - y j)
  let sb := (L j : ℝ) * centeredRepresentative (x b j - y j)
  have ha0 : ((⌊sa / δ⌋ : ℤ) : ℝ) ≤ sa / δ := Int.floor_le _
  have ha1 : sa / δ < ((⌊sa / δ⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  have hb0 : ((⌊sb / δ⌋ : ℤ) : ℝ) ≤ sb / δ := Int.floor_le _
  have hb1 : sb / δ < ((⌊sb / δ⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  have hfloor : ⌊sa / δ⌋ = ⌊sb / δ⌋ := by
    simpa [cellCode, sa, sb] using hcell
  have hquot : |sa / δ - sb / δ| < 1 := by
    rw [abs_lt]
    rw [hfloor] at ha0 ha1
    constructor
    · linarith [ha0, hb1]
    · linarith [ha1, hb0]
  have hdiv : |sa - sb| / δ < 1 := by
    have heq : sa / δ - sb / δ = (sa - sb) / δ := by ring
    rw [heq, abs_div, abs_of_pos hδ] at hquot
    exact hquot
  exact (div_lt_one hδ).mp hdiv

/-- The floor-cell code is injective precisely because two points in one
cell would violate the assumed anisotropic separation. -/
lemma cellCode_injective
    {ι : Type*} {r : ℕ} {δ : ℝ} (hδ : 0 < δ) (L : Fin r → ℕ)
    (x : ι → Fin r → UnitAddCircle)
    (hsep : AnisotropicallySeparated δ L x)
    (y : Fin r → UnitAddCircle) :
    Function.Injective (cellCode δ L x y) := by
  intro a b hab
  by_contra hne
  obtain ⟨j, hj⟩ := hsep hne
  have hcell : cellCode δ L x y a j = cellCode δ L x y b j :=
    congrFun hab j
  have hreal := abs_scaledRepresentative_sub_lt_of_cellCode_eq hδ L x y hcell
  let ua := centeredRepresentative (x a j - y j)
  let ub := centeredRepresentative (x b j - y j)
  have hcircle : ((ua - ub : ℝ) : UnitAddCircle) = x a j - x b j := by
    change ((centeredRepresentative (x a j - y j) -
      centeredRepresentative (x b j - y j) : ℝ) : UnitAddCircle) = _
    rw [QuotientAddGroup.mk_sub, coe_centeredRepresentative,
      coe_centeredRepresentative]
    abel
  have hquotient : ‖x a j - x b j‖ ≤ |ua - ub| := by
    rw [← hcircle]
    simpa [distToInt] using
      (distToInt_le_abs_sub_int (ua - ub) 0)
  have hLnonneg : (0 : ℝ) ≤ L j := by positivity
  have hscaled : (L j : ℝ) * ‖x a j - x b j‖ ≤
      |(L j : ℝ) * ua - (L j : ℝ) * ub| := by
    calc
      (L j : ℝ) * ‖x a j - x b j‖ ≤ (L j : ℝ) * |ua - ub| := by gcongr
      _ = |(L j : ℝ) * ua - (L j : ℝ) * ub| := by
        rw [← mul_sub, abs_mul, abs_of_nonneg hLnonneg]
  exact (not_lt_of_ge (hj.trans hscaled)) hreal

/-- Loss incurred by replacing a real scaled displacement by its `δ`-cell. -/
noncomputable def cellComparisonFactor (δ : ℝ) : ℝ :=
  3 * (1 + δ⁻¹ ^ 2)

lemma cellComparisonFactor_nonneg (δ : ℝ) : 0 ≤ cellComparisonFactor δ := by
  unfold cellComparisonFactor
  positivity

lemma abs_floor_le_abs_add_one (t : ℝ) :
    |((⌊t⌋ : ℤ) : ℝ)| ≤ |t| + 1 := by
  have hlo : ((⌊t⌋ : ℤ) : ℝ) ≤ t := Int.floor_le t
  have hhi : t < ((⌊t⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one t
  rw [abs_le]
  constructor
  · linarith [neg_abs_le t]
  · linarith [le_abs_self t]

/-- The denominator attached to a floor cell is controlled by the true
quadratic denominator. -/
lemma one_add_floor_sq_le_cellComparisonFactor_mul
    {δ : ℝ} (hδ : 0 < δ) (s : ℝ) :
    1 + (((⌊s / δ⌋ : ℤ) : ℝ)) ^ 2 ≤
      cellComparisonFactor δ * (1 + s ^ 2) := by
  have habs := abs_floor_le_abs_add_one (s / δ)
  have hsq : (((⌊s / δ⌋ : ℤ) : ℝ)) ^ 2 ≤ (|s / δ| + 1) ^ 2 := by
    have hz : 0 ≤ |((⌊s / δ⌋ : ℤ) : ℝ)| := abs_nonneg _
    have hr : 0 ≤ |s / δ| + 1 := by positivity
    have := (sq_le_sq₀ hz hr).2 habs
    simpa [sq_abs] using this
  have habsdiv : |s / δ| = |s| * δ⁻¹ := by
    rw [abs_div, abs_of_pos hδ, div_eq_mul_inv]
  rw [habsdiv] at hsq
  have habssq : |s| ^ 2 = s ^ 2 := sq_abs s
  have hδinv : 0 ≤ δ⁻¹ ^ 2 := sq_nonneg _
  have hsnonneg : 0 ≤ s ^ 2 := sq_nonneg _
  unfold cellComparisonFactor
  nlinarith [sq_nonneg (|s| * δ⁻¹ - 1),
    sq_nonneg (|s| * δ⁻¹ + 1)]

/-- Consequently the real decay weight is dominated by the lattice-cell
weight, with an explicit `δ`-dependent factor. -/
lemma inv_one_add_sq_le_cellComparisonFactor_mul_latticeWeight
    {δ : ℝ} (hδ : 0 < δ) (s : ℝ) :
    1 / (1 + s ^ 2) ≤
      cellComparisonFactor δ * latticeWeight ⌊s / δ⌋ := by
  have hden : 0 < 1 + s ^ 2 := by positivity
  have hcell : 0 < 1 + (((⌊s / δ⌋ : ℤ) : ℝ)) ^ 2 := by positivity
  have hcmp := one_add_floor_sq_le_cellComparisonFactor_mul hδ s
  unfold latticeWeight
  calc
    1 / (1 + s ^ 2) ≤
        cellComparisonFactor δ / (1 + (((⌊s / δ⌋ : ℤ) : ℝ)) ^ 2) := by
      rw [div_le_div_iff₀ hden hcell]
      simpa only [one_mul] using hcmp
    _ = cellComparisonFactor δ *
        (1 / (1 + (((⌊s / δ⌋ : ℤ) : ℝ)) ^ 2)) := by ring

/-- One coordinate of the explicit kernel, evaluated at a sample point, is
bounded by its integer-cell weight. -/
lemma norm_vallPoussinKernel_le_cellWeight
    {ι : Type*} {r : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (L : Fin r → ℕ) (hL : ∀ j, 0 < L j)
    (x : ι → Fin r → UnitAddCircle) (y : Fin r → UnitAddCircle)
    (i : ι) (j : Fin r) :
    ‖ReproducingKernel.vallPoussinKernel (L j) (x i j - y j)‖ ≤
      13 * (L j : ℝ) * cellComparisonFactor δ *
        latticeWeight (cellCode δ L x y i j) := by
  let u := centeredRepresentative (x i j - y j)
  let s := (L j : ℝ) * u
  have hdecay := ReproducingKernel.norm_vallPoussinKernel_le_decay
    (L j) (hL j) (x i j - y j)
  have hnorm : ‖x i j - y j‖ = |u| := norm_eq_abs_centeredRepresentative _
  have hsquare : ((L j : ℝ) * ‖x i j - y j‖) ^ 2 = s ^ 2 := by
    rw [hnorm]
    simp only [s, u, mul_pow, sq_abs]
  rw [hsquare] at hdecay
  have hweight := inv_one_add_sq_le_cellComparisonFactor_mul_latticeWeight hδ s
  have hcoeff : 0 ≤ 13 * (L j : ℝ) := by positivity
  calc
    ‖ReproducingKernel.vallPoussinKernel (L j) (x i j - y j)‖ ≤
        13 * (L j : ℝ) / (1 + s ^ 2) := hdecay
    _ = (13 * (L j : ℝ)) * (1 / (1 + s ^ 2)) := by ring
    _ ≤ (13 * (L j : ℝ)) *
        (cellComparisonFactor δ * latticeWeight ⌊s / δ⌋) := by gcongr
    _ = 13 * (L j : ℝ) * cellComparisonFactor δ *
        latticeWeight (cellCode δ L x y i j) := by
      simp only [cellCode, s, u]
      ring

/-- The cube radius can be chosen internally for every finite cell code. -/
lemma sum_latticeWeight_comp_injective_le_unbounded
    {ι : Type*} [Fintype ι] (r : ℕ) (code : ι → Fin r → ℤ)
    (hcode : Function.Injective code) :
    (∑ i : ι, ∏ j : Fin r, latticeWeight (code i j)) ≤ 5 ^ r := by
  classical
  let B : ℕ := ∑ i : ι, ∑ j : Fin r, (code i j).natAbs
  apply sum_latticeWeight_comp_injective_le r B code hcode
  intro i j
  have hj : (code i j).natAbs ≤ ∑ q : Fin r, (code i q).natAbs :=
    Finset.single_le_sum
      (fun q _ => Nat.zero_le (code i q).natAbs) (Finset.mem_univ j)
  have hi : (∑ q : Fin r, (code i q).natAbs) ≤ B := by
    exact Finset.single_le_sum
      (s := (Finset.univ : Finset ι))
      (f := fun a => ∑ q : Fin r, (code a q).natAbs)
      (fun a _ => Finset.sum_nonneg fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
  exact hj.trans hi

/-- Product of the one-dimensional kernel norms. -/
noncomputable def tensorKernelNorm
    {r : ℕ} (L : Fin r → ℕ) (z : Fin r → UnitAddCircle) : ℝ :=
  ∏ j : Fin r, ‖ReproducingKernel.vallPoussinKernel (L j) (z j)‖

lemma tensorKernelNorm_nonneg
    {r : ℕ} (L : Fin r → ℕ) (z : Fin r → UnitAddCircle) :
    0 ≤ tensorKernelNorm L z := by
  exact Finset.prod_nonneg fun _ _ => norm_nonneg _

/-- The complete anisotropic kernel-packing estimate.  This is the packing
step sketched in the proof of Proposition 4.2. -/
theorem sum_tensorKernelNorm_le_of_anisotropicallySeparated
    {ι : Type*} [Fintype ι] {r : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (L : Fin r → ℕ) (hL : ∀ j, 0 < L j)
    (x : ι → Fin r → UnitAddCircle)
    (hsep : AnisotropicallySeparated δ L x)
    (y : Fin r → UnitAddCircle) :
    (∑ i : ι, tensorKernelNorm L (fun j => x i j - y j)) ≤
      (65 * cellComparisonFactor δ) ^ r * ∏ j : Fin r, (L j : ℝ) := by
  classical
  let code := cellCode δ L x y
  have hcode : Function.Injective code := cellCode_injective hδ L x hsep y
  have hpoint (i : ι) :
      tensorKernelNorm L (fun j => x i j - y j) ≤
        (13 : ℝ) ^ r * cellComparisonFactor δ ^ r *
          (∏ j : Fin r, (L j : ℝ)) *
            ∏ j : Fin r, latticeWeight (code i j) := by
    unfold tensorKernelNorm
    calc
      (∏ j : Fin r,
          ‖ReproducingKernel.vallPoussinKernel (L j) (x i j - y j)‖) ≤
          ∏ j : Fin r,
            (13 * (L j : ℝ) * cellComparisonFactor δ *
              latticeWeight (code i j)) := by
        apply Finset.prod_le_prod
        · intro j hj
          exact norm_nonneg _
        · intro j hj
          exact norm_vallPoussinKernel_le_cellWeight hδ L hL x y i j
      _ = (13 : ℝ) ^ r * cellComparisonFactor δ ^ r *
          (∏ j : Fin r, (L j : ℝ)) *
            ∏ j : Fin r, latticeWeight (code i j) := by
        simp only [Finset.prod_mul_distrib, Finset.prod_const,
          Finset.card_univ, Fintype.card_fin]
        ring
  have hsum := sum_latticeWeight_comp_injective_le_unbounded r code hcode
  have hconst :
      0 ≤ (13 : ℝ) ^ r * cellComparisonFactor δ ^ r *
        (∏ j : Fin r, (L j : ℝ)) := by
    have hprodL : 0 ≤ ∏ j : Fin r, (L j : ℝ) :=
      Finset.prod_nonneg fun _ _ => by positivity
    exact mul_nonneg
      (mul_nonneg (pow_nonneg (by norm_num) _)
        (pow_nonneg (cellComparisonFactor_nonneg δ) _)) hprodL
  calc
    (∑ i : ι, tensorKernelNorm L (fun j => x i j - y j)) ≤
        ∑ i : ι,
          ((13 : ℝ) ^ r * cellComparisonFactor δ ^ r *
            (∏ j : Fin r, (L j : ℝ)) *
              ∏ j : Fin r, latticeWeight (code i j)) := by
      gcongr with i
      exact hpoint i
    _ = ((13 : ℝ) ^ r * cellComparisonFactor δ ^ r *
          (∏ j : Fin r, (L j : ℝ))) *
            ∑ i : ι, ∏ j : Fin r, latticeWeight (code i j) := by
      rw [Finset.mul_sum]
    _ ≤ ((13 : ℝ) ^ r * cellComparisonFactor δ ^ r *
          (∏ j : Fin r, (L j : ℝ))) * 5 ^ r := by gcongr
    _ = (65 * cellComparisonFactor δ) ^ r *
          ∏ j : Fin r, (L j : ℝ) := by
      have hpow : (65 : ℝ) ^ r = (13 : ℝ) ^ r * 5 ^ r := by
        rw [← mul_pow]
        norm_num
      rw [mul_pow, hpow]
      ring

/-- The exact anisotropic frequency box `∏ⱼ [-Lⱼ,Lⱼ]`. -/
noncomputable def anisotropicFrequencyBox {r : ℕ}
    (L : Fin r → ℕ) : Finset (Fin r → ℤ) :=
  Fintype.piFinset fun j : Fin r => ReproducingKernel.spectrumBox (L j)

/-- Constructive finite-spectrum predicate on the `r`-torus. -/
def HasSpectrumInBox {r : ℕ} (L : Fin r → ℕ)
    (f : (Fin r → UnitAddCircle) → ℂ) : Prop :=
  ∃ c : (Fin r → ℤ) → ℂ, ∀ z,
    f z = ∑ n ∈ anisotropicFrequencyBox L,
      c n * UnitAddTorus.mFourier n z

/-- Tensor product of the explicit one-dimensional reproducing kernels. -/
noncomputable def tensorKernel {r : ℕ} (L : Fin r → ℕ)
    (z : Fin r → UnitAddCircle) : ℂ :=
  ∏ j : Fin r, ReproducingKernel.vallPoussinKernel (L j) (z j)

lemma continuous_tensorKernel {r : ℕ} (L : Fin r → ℕ) :
    Continuous (tensorKernel L) := by
  unfold tensorKernel
  apply continuous_finsetProd
  intro j hj
  exact (ReproducingKernel.continuous_vallPoussinKernel (L j)).comp
    (continuous_apply j)

lemma norm_tensorKernel {r : ℕ} (L : Fin r → ℕ)
    (z : Fin r → UnitAddCircle) :
    ‖tensorKernel L z‖ = tensorKernelNorm L z := by
  simp only [tensorKernel, tensorKernelNorm, norm_prod]

/-- Product of the normalized Haar measures on the coordinate circles. -/
noncomputable abbrev torusHaarMeasure (r : ℕ) :
    Measure (Fin r → UnitAddCircle) :=
  Measure.pi fun _ : Fin r => AddCircle.haarAddCircle

noncomputable local instance torusHaarMeasureIsNegInvariant (r : ℕ) :
    (torusHaarMeasure r).IsNegInvariant where
  neg_eq_self := by
    rw [Measure.neg_def]
    change Measure.map (fun x : Fin r → UnitAddCircle => fun j => -(x j))
      (Measure.pi fun _ : Fin r => AddCircle.haarAddCircle) = _
    rw [Measure.pi_map_pi (fun _ => measurable_neg.aemeasurable)]
    congr with j
    rw [Measure.map_neg_eq_self
      (AddCircle.haarAddCircle : Measure UnitAddCircle)]

/-- Haar convolution on the finite torus. -/
noncomputable def torusConvolution {r : ℕ}
    (κ f : (Fin r → UnitAddCircle) → ℂ)
    (x : Fin r → UnitAddCircle) : ℂ :=
  ∫ y, κ y * f (x - y) ∂torusHaarMeasure r

/-- Symmetric form of Haar convolution, putting the data function at the
common integration point. -/
lemma torusConvolution_eq_swap {r : ℕ}
    (κ f : (Fin r → UnitAddCircle) → ℂ)
    (x : Fin r → UnitAddCircle) :
    torusConvolution κ f x =
      ∫ y, κ (x - y) * f y ∂torusHaarMeasure r := by
  change (κ ⋆[(ContinuousLinearMap.mul ℂ ℂ), torusHaarMeasure r] f) x = _
  exact convolution_mul_swap

lemma mFourier_apply_sub {r : ℕ} (n : Fin r → ℤ)
    (x y : Fin r → UnitAddCircle) :
    UnitAddTorus.mFourier n (x - y) =
      UnitAddTorus.mFourier n x * UnitAddTorus.mFourier (-n) y := by
  change (∏ j : Fin r, fourier (n j) (x j - y j)) =
    (∏ j : Fin r, fourier (n j) (x j)) *
      ∏ j : Fin r, fourier (-n j) (y j)
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  exact ReproducingKernel.fourier_apply_sub (n j) (x j) (y j)

lemma natAbs_le_of_mem_anisotropicFrequencyBox
    {r : ℕ} {L : Fin r → ℕ} {n : Fin r → ℤ}
    (hn : n ∈ anisotropicFrequencyBox L) (j : Fin r) :
    (n j).natAbs ≤ L j := by
  simp only [anisotropicFrequencyBox, Fintype.mem_piFinset] at hn
  have hj := hn j
  simp only [ReproducingKernel.spectrumBox, Finset.mem_Icc] at hj
  have hs : (n j).natAbs ≤ ((L j : ℕ) : ℤ).natAbs := by
    rw [Int.natAbs_le_iff_sq_le]
    nlinarith [hj.1, hj.2]
  simpa using hs

/-- The tensor kernel has multiplier one throughout the anisotropic box. -/
lemma integral_tensorKernel_mul_mFourier_neg_eq_one
    {r : ℕ} (L : Fin r → ℕ) (hL : ∀ j, 0 < L j)
    (n : Fin r → ℤ) (hn : n ∈ anisotropicFrequencyBox L) :
    (∫ y : Fin r → UnitAddCircle,
      tensorKernel L y * UnitAddTorus.mFourier (-n) y
        ∂torusHaarMeasure r) = 1 := by
  change (∫ y : Fin r → UnitAddCircle,
    (∏ j : Fin r, ReproducingKernel.vallPoussinKernel (L j) (y j)) *
      ∏ j : Fin r, fourier (-n j) (y j) ∂torusHaarMeasure r) = 1
  simp_rw [← Finset.prod_mul_distrib]
  have hfub := integral_fintype_prod_eq_prod
    (μ := fun _ : Fin r => AddCircle.haarAddCircle)
    (fun j z => ReproducingKernel.vallPoussinKernel (L j) z * fourier (-n j) z)
  rw [hfub]
  apply Finset.prod_eq_one
  intro j hj
  have hcoeff := ReproducingKernel.fourierCoeff_vallPoussinKernel_eq_one
    (L j) (hL j) (n j) (natAbs_le_of_mem_anisotropicFrequencyBox hn j)
  unfold fourierCoeff at hcoeff
  simpa only [smul_eq_mul, mul_comm] using hcoeff

/-- The tensor convolution acts diagonally on each multivariate character. -/
lemma torusConvolution_tensorKernel_mFourier
    {r : ℕ} (L : Fin r → ℕ) (hL : ∀ j, 0 < L j)
    (n : Fin r → ℤ) (hn : n ∈ anisotropicFrequencyBox L)
    (x : Fin r → UnitAddCircle) :
    torusConvolution (tensorKernel L) (UnitAddTorus.mFourier n) x =
      UnitAddTorus.mFourier n x := by
  unfold torusConvolution
  calc
    (∫ y : Fin r → UnitAddCircle,
        tensorKernel L y * UnitAddTorus.mFourier n (x - y)
          ∂torusHaarMeasure r) =
      ∫ y : Fin r → UnitAddCircle,
        UnitAddTorus.mFourier n x *
          (tensorKernel L y * UnitAddTorus.mFourier (-n) y)
            ∂torusHaarMeasure r := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [mFourier_apply_sub]
      ring
    _ = UnitAddTorus.mFourier n x *
        (∫ y : Fin r → UnitAddCircle,
          tensorKernel L y * UnitAddTorus.mFourier (-n) y
            ∂torusHaarMeasure r) := by
      rw [integral_const_mul]
    _ = UnitAddTorus.mFourier n x := by
      rw [integral_tensorKernel_mul_mFourier_neg_eq_one L hL n hn, mul_one]

/-- Multivariate version of Lemma 4.1: tensor convolution reproduces every
function with spectrum in the stated box. -/
theorem torusConvolution_tensorKernel_eq
    {r : ℕ} (L : Fin r → ℕ) (hL : ∀ j, 0 < L j)
    (f : (Fin r → UnitAddCircle) → ℂ) (hf : HasSpectrumInBox L f)
    (x : Fin r → UnitAddCircle) :
    torusConvolution (tensorKernel L) f x = f x := by
  classical
  obtain ⟨c, hc⟩ := hf
  rw [hc x]
  unfold torusConvolution
  simp_rw [hc]
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro n hn
    have hchar := torusConvolution_tensorKernel_mFourier L hL n hn x
    unfold torusConvolution at hchar
    calc
      (∫ y : Fin r → UnitAddCircle,
          tensorKernel L y *
            (c n * UnitAddTorus.mFourier n (x - y))
              ∂torusHaarMeasure r) =
          c n * (∫ y : Fin r → UnitAddCircle,
            tensorKernel L y * UnitAddTorus.mFourier n (x - y)
              ∂torusHaarMeasure r) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with y
        ring
      _ = c n * UnitAddTorus.mFourier n x := by rw [hchar]
  · intro n hn
    apply Continuous.integrable_of_hasCompactSupport
    · exact (continuous_tensorKernel L).mul
        (continuous_const.mul
          ((map_continuous (UnitAddTorus.mFourier n)).comp
            (continuous_const.sub continuous_id)))
    · exact HasCompactSupport.of_compactSpace _

/-- A finite Fourier expansion with an arbitrary finite indexing type.  Using
an indexing type rather than a set permits repeated frequencies and makes
closure under products completely algebraic. -/
structure BoundedSpectrumExpansion {r : ℕ} (L : Fin r → ℕ)
    (f : (Fin r → UnitAddCircle) → ℂ) where
  Index : Type
  indexFintype : Fintype Index
  frequency : Index → Fin r → ℤ
  coefficient : Index → ℂ
  frequency_le : ∀ a j, (frequency a j).natAbs ≤ L j
  eq_sum : ∀ z, f z = ∑ a : Index,
    coefficient a * UnitAddTorus.mFourier (frequency a) z

/-- Existence of a certified finite Fourier expansion in the box. -/
def HasBoundedSpectrum {r : ℕ} (L : Fin r → ℕ)
    (f : (Fin r → UnitAddCircle) → ℂ) : Prop :=
  Nonempty (BoundedSpectrumExpansion L f)

namespace BoundedSpectrumExpansion

variable {r : ℕ} {L M : Fin r → ℕ}
  {f g : (Fin r → UnitAddCircle) → ℂ}

/-- Enlarging coordinate bounds preserves a spectral expansion. -/
def mono (E : BoundedSpectrumExpansion L f) (hLM : ∀ j, L j ≤ M j) :
    BoundedSpectrumExpansion M f where
  Index := E.Index
  indexFintype := E.indexFintype
  frequency := E.frequency
  coefficient := E.coefficient
  frequency_le a j := (E.frequency_le a j).trans (hLM j)
  eq_sum := E.eq_sum

/-- Pointwise sum of frequency bounds. -/
def addBounds (L M : Fin r → ℕ) : Fin r → ℕ :=
  fun j => L j + M j

/-- Integer dilation of frequency bounds. -/
def scaleBounds (q : ℕ) (L : Fin r → ℕ) : Fin r → ℕ :=
  fun j => q * L j

/-- Products add spectral widths. -/
noncomputable def mul
    (E : BoundedSpectrumExpansion L f)
    (F : BoundedSpectrumExpansion M g) :
    BoundedSpectrumExpansion (addBounds L M) (fun z => f z * g z) where
  Index := E.Index × F.Index
  indexFintype := by
    letI := E.indexFintype
    letI := F.indexFintype
    infer_instance
  frequency ab := E.frequency ab.1 + F.frequency ab.2
  coefficient ab := E.coefficient ab.1 * F.coefficient ab.2
  frequency_le ab j := by
    have hadd := Int.natAbs_add_le (E.frequency ab.1 j) (F.frequency ab.2 j)
    exact hadd.trans (Nat.add_le_add (E.frequency_le ab.1 j) (F.frequency_le ab.2 j))
  eq_sum z := by
    letI := E.indexFintype
    letI := F.indexFintype
    rw [E.eq_sum, F.eq_sum]
    rw [Finset.sum_mul_sum]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    rw [UnitAddTorus.mFourier_add]
    ring

/-- Complex conjugation reflects the spectrum. -/
noncomputable def conj (E : BoundedSpectrumExpansion L f) :
    BoundedSpectrumExpansion L (fun z => star (f z)) where
  Index := E.Index
  indexFintype := E.indexFintype
  frequency a := -E.frequency a
  coefficient a := star (E.coefficient a)
  frequency_le a j := by simpa using E.frequency_le a j
  eq_sum z := by
    letI := E.indexFintype
    rw [E.eq_sum, star_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [star_mul]
    have hfour :
        star (UnitAddTorus.mFourier (E.frequency a) z) =
          UnitAddTorus.mFourier (-E.frequency a) z := by
      symm
      simpa only [starRingEnd_apply] using
        (UnitAddTorus.mFourier_neg (n := E.frequency a) (x := z))
    rw [hfour]
    ring

/-- The constant one has zero spectrum. -/
noncomputable def one (L : Fin r → ℕ) :
    BoundedSpectrumExpansion L (fun _ => (1 : ℂ)) where
  Index := Fin 1
  indexFintype := inferInstance
  frequency _ := 0
  coefficient _ := 1
  frequency_le _ _ := by simp
  eq_sum z := by simp [UnitAddTorus.mFourier_zero]

/-- Natural powers multiply the coordinate widths. -/
noncomputable def pow (q : ℕ) (E : BoundedSpectrumExpansion L f) :
    BoundedSpectrumExpansion (scaleBounds q L) (fun z => (f z) ^ q) := by
  induction q with
  | zero =>
      simpa using one (scaleBounds 0 L)
  | succ q ih =>
      have H := mul ih E
      exact H.mono (by
        intro j
        simp [addBounds, scaleBounds, Nat.add_mul])

end BoundedSpectrumExpansion

namespace HasBoundedSpectrum

variable {r : ℕ} {L M : Fin r → ℕ}
  {f g : (Fin r → UnitAddCircle) → ℂ}

lemma mono (hf : HasBoundedSpectrum L f) (hLM : ∀ j, L j ≤ M j) :
    HasBoundedSpectrum M f := by
  obtain ⟨E⟩ := hf
  exact ⟨E.mono hLM⟩

lemma mul (hf : HasBoundedSpectrum L f) (hg : HasBoundedSpectrum M g) :
    HasBoundedSpectrum (BoundedSpectrumExpansion.addBounds L M)
      (fun z => f z * g z) := by
  obtain ⟨E⟩ := hf
  obtain ⟨F⟩ := hg
  exact ⟨E.mul F⟩

lemma conj (hf : HasBoundedSpectrum L f) :
    HasBoundedSpectrum L (fun z => star (f z)) := by
  obtain ⟨E⟩ := hf
  exact ⟨E.conj⟩

lemma pow (q : ℕ) (hf : HasBoundedSpectrum L f) :
    HasBoundedSpectrum (BoundedSpectrumExpansion.scaleBounds q L)
      (fun z => (f z) ^ q) := by
  obtain ⟨E⟩ := hf
  exact ⟨E.pow q⟩

/-- The `q`-th power of `f * conj f` has width `2q L`. -/
lemma normSqPow (q : ℕ) (hf : HasBoundedSpectrum L f) :
    HasBoundedSpectrum (BoundedSpectrumExpansion.scaleBounds (2 * q) L)
      (fun z => (f z * star (f z)) ^ q) := by
  have hprod := hf.mul hf.conj
  have hpow := hprod.pow q
  exact hpow.mono (by
    intro j
    simp only [BoundedSpectrumExpansion.scaleBounds,
      BoundedSpectrumExpansion.addBounds]
    exact le_of_eq (by ring))

end HasBoundedSpectrum

namespace BoundedSpectrumExpansion

variable {r : ℕ} {L : Fin r → ℕ}
  {f : (Fin r → UnitAddCircle) → ℂ}

lemma frequency_mem_box (E : BoundedSpectrumExpansion L f) (a : E.Index) :
    E.frequency a ∈ anisotropicFrequencyBox L := by
  simp only [anisotropicFrequencyBox, Fintype.mem_piFinset,
    ReproducingKernel.spectrumBox, Finset.mem_Icc]
  intro j
  have hsq : (E.frequency a j) ^ 2 ≤ ((L j : ℕ) : ℤ) ^ 2 := by
    rw [← Int.natAbs_le_iff_sq_le]
    simpa using E.frequency_le a j
  constructor <;> nlinarith

/-- A certified bounded Fourier expansion is continuous. -/
lemma continuous (E : BoundedSpectrumExpansion L f) : Continuous f := by
  classical
  letI := E.indexFintype
  have heq : f = fun z => ∑ a : E.Index,
      E.coefficient a * UnitAddTorus.mFourier (E.frequency a) z :=
    funext E.eq_sum
  rw [heq]
  fun_prop

/-- Lemma 4.1 for an arbitrary finite indexing set of frequencies. -/
theorem torusConvolution_tensorKernel_eq_of_expansion
    (E : BoundedSpectrumExpansion L f) (hL : ∀ j, 0 < L j)
    (x : Fin r → UnitAddCircle) :
    torusConvolution (tensorKernel L) f x = f x := by
  classical
  letI := E.indexFintype
  rw [E.eq_sum x]
  unfold torusConvolution
  simp_rw [E.eq_sum]
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro a ha
    have hchar := torusConvolution_tensorKernel_mFourier L hL
      (E.frequency a) (E.frequency_mem_box a) x
    unfold torusConvolution at hchar
    calc
      (∫ y : Fin r → UnitAddCircle,
          tensorKernel L y *
            (E.coefficient a * UnitAddTorus.mFourier (E.frequency a) (x - y))
              ∂torusHaarMeasure r) =
          E.coefficient a * (∫ y : Fin r → UnitAddCircle,
            tensorKernel L y * UnitAddTorus.mFourier (E.frequency a) (x - y)
              ∂torusHaarMeasure r) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with y
        ring
      _ = E.coefficient a * UnitAddTorus.mFourier (E.frequency a) x := by
        rw [hchar]
  · intro a ha
    apply Continuous.integrable_of_hasCompactSupport
    · exact (continuous_tensorKernel L).mul
        (continuous_const.mul
          ((map_continuous (UnitAddTorus.mFourier (E.frequency a))).comp
            (continuous_const.sub continuous_id)))
    · exact HasCompactSupport.of_compactSpace _

end BoundedSpectrumExpansion

namespace HasBoundedSpectrum

variable {r : ℕ} {L : Fin r → ℕ}
  {f : (Fin r → UnitAddCircle) → ℂ}

lemma continuous (hf : HasBoundedSpectrum L f) : Continuous f := by
  obtain ⟨E⟩ := hf
  exact E.continuous

/-- Lemma 4.1 in the finite-spectrum certificate interface. -/
theorem torusConvolution_tensorKernel_eq
    (hf : HasBoundedSpectrum L f) (hL : ∀ j, 0 < L j)
    (x : Fin r → UnitAddCircle) :
    torusConvolution (tensorKernel L) f x = f x := by
  obtain ⟨E⟩ := hf
  exact E.torusConvolution_tensorKernel_eq_of_expansion hL x

end HasBoundedSpectrum

lemma continuous_tensorKernelNorm {r : ℕ} (L : Fin r → ℕ) :
    Continuous (tensorKernelNorm L) := by
  simpa only [norm_tensorKernel] using (continuous_tensorKernel L).norm

lemma integrable_tensorKernelNorm_mul
    {r : ℕ} (L : Fin r → ℕ) (x : Fin r → UnitAddCircle)
    (H : (Fin r → UnitAddCircle) → ℝ) (hH : Continuous H) :
    Integrable
      (fun y => tensorKernelNorm L (fun j => x j - y j) * H y)
      (torusHaarMeasure r) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact ((continuous_tensorKernelNorm L).comp
      (continuous_const.sub continuous_id)).mul hH
  · exact HasCompactSupport.of_compactSpace _

/-- Proposition 4.2, analytic form with an explicit continuous pointwise
majorant.  The constant comes solely from the internally proved packing
bound. -/
theorem anisotropicSampling_of_majorant
    {ι : Type*} [Fintype ι] {r : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (L : Fin r → ℕ) (hL : ∀ j, 0 < L j)
    (x : ι → Fin r → UnitAddCircle)
    (hsep : AnisotropicallySeparated δ L x)
    (F : ι → (Fin r → UnitAddCircle) → ℂ)
    (hF : ∀ i, HasBoundedSpectrum L (F i))
    (H : (Fin r → UnitAddCircle) → ℝ) (hH : Continuous H)
    (hHnonneg : ∀ y, 0 ≤ H y)
    (hmajor : ∀ i y, ‖F i y‖ ≤ H y) :
    (∑ i : ι, ‖F i (x i)‖) ≤
      ((65 * cellComparisonFactor δ) ^ r *
          ∏ j : Fin r, (L j : ℝ)) *
        ∫ y, H y ∂torusHaarMeasure r := by
  classical
  have hshift (i : ι) : Continuous
      (fun y : Fin r → UnitAddCircle =>
        tensorKernelNorm L (fun j => x i j - y j)) :=
    (continuous_tensorKernelNorm L).comp (continuous_const.sub continuous_id)
  have hFnorm (i : ι) : Continuous
      (fun y : Fin r → UnitAddCircle => ‖F i y‖) :=
    (hF i).continuous.norm
  have hminorInt (i : ι) : Integrable
      (fun y : Fin r → UnitAddCircle =>
        tensorKernelNorm L (fun j => x i j - y j) * ‖F i y‖)
      (torusHaarMeasure r) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (hshift i).mul (hFnorm i)
    · exact HasCompactSupport.of_compactSpace _
  have hmajorInt (i : ι) : Integrable
      (fun y : Fin r → UnitAddCircle =>
        tensorKernelNorm L (fun j => x i j - y j) * H y)
      (torusHaarMeasure r) :=
    integrable_tensorKernelNorm_mul L (x i) H hH
  have hpoint (i : ι) :
      ‖F i (x i)‖ ≤
        ∫ y, tensorKernelNorm L (fun j => x i j - y j) * H y
          ∂torusHaarMeasure r := by
    have hrepro := (hF i).torusConvolution_tensorKernel_eq hL (x i)
    rw [torusConvolution_eq_swap] at hrepro
    calc
      ‖F i (x i)‖ =
          ‖∫ y, tensorKernel L (x i - y) * F i y
              ∂torusHaarMeasure r‖ := by rw [hrepro]
      _ ≤ ∫ y, ‖tensorKernel L (x i - y) * F i y‖
              ∂torusHaarMeasure r := norm_integral_le_integral_norm _
      _ = ∫ y, tensorKernelNorm L (fun j => x i j - y j) * ‖F i y‖
              ∂torusHaarMeasure r := by
        apply integral_congr_ae
        filter_upwards [] with y
        rw [norm_mul, norm_tensorKernel]
        rfl
      _ ≤ ∫ y, tensorKernelNorm L (fun j => x i j - y j) * H y
              ∂torusHaarMeasure r := by
        apply integral_mono (hminorInt i) (hmajorInt i)
        intro y
        exact mul_le_mul_of_nonneg_left (hmajor i y)
          (tensorKernelNorm_nonneg L _)
  have hsumInt : Integrable
      (fun y : Fin r → UnitAddCircle =>
        ∑ i : ι, tensorKernelNorm L (fun j => x i j - y j) * H y)
      (torusHaarMeasure r) := by
    apply integrable_finsetSum Finset.univ
    intro i hi
    exact hmajorInt i
  have hHInt : Integrable H (torusHaarMeasure r) := by
    apply Continuous.integrable_of_hasCompactSupport hH
    exact HasCompactSupport.of_compactSpace _
  let C : ℝ := (65 * cellComparisonFactor δ) ^ r *
    ∏ j : Fin r, (L j : ℝ)
  calc
    (∑ i : ι, ‖F i (x i)‖) ≤
        ∑ i : ι, ∫ y,
          tensorKernelNorm L (fun j => x i j - y j) * H y
            ∂torusHaarMeasure r := Finset.sum_le_sum fun i hi => hpoint i
    _ = ∫ y, ∑ i : ι,
          tensorKernelNorm L (fun j => x i j - y j) * H y
            ∂torusHaarMeasure r := by
      rw [integral_finsetSum]
      intro i hi
      exact hmajorInt i
    _ = ∫ y, (∑ i : ι,
          tensorKernelNorm L (fun j => x i j - y j)) * H y
            ∂torusHaarMeasure r := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [Finset.sum_mul]
    _ ≤ ∫ y, C * H y ∂torusHaarMeasure r := by
      apply integral_mono
      · simpa only [Finset.sum_mul] using hsumInt
      · exact hHInt.const_mul C
      · intro y
        exact mul_le_mul_of_nonneg_right
          (sum_tensorKernelNorm_le_of_anisotropicallySeparated
            hδ L hL x hsep y) (hHnonneg y)
    _ = C * ∫ y, H y ∂torusHaarMeasure r := integral_const_mul C H
    _ = ((65 * cellComparisonFactor δ) ^ r *
          ∏ j : Fin r, (L j : ℝ)) *
        ∫ y, H y ∂torusHaarMeasure r := rfl

/-- Pointwise maximum of the `p`-th powers of the norms of a nonempty
finite family. -/
noncomputable def familyMaxPower
    {ι : Type*} [Fintype ι] [Nonempty ι] {r : ℕ}
    (p : ℕ) (F : ι → (Fin r → UnitAddCircle) → ℂ)
    (y : Fin r → UnitAddCircle) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => ‖F i y‖ ^ p)

lemma norm_pow_le_familyMaxPower
    {ι : Type*} [Fintype ι] [Nonempty ι] {r : ℕ}
    (p : ℕ) (F : ι → (Fin r → UnitAddCircle) → ℂ)
    (i : ι) (y : Fin r → UnitAddCircle) :
    ‖F i y‖ ^ p ≤ familyMaxPower p F y := by
  exact Finset.le_sup' (fun a : ι => ‖F a y‖ ^ p) (Finset.mem_univ i)

lemma familyMaxPower_nonneg
    {ι : Type*} [Fintype ι] [Nonempty ι] {r : ℕ}
    (p : ℕ) (F : ι → (Fin r → UnitAddCircle) → ℂ)
    (y : Fin r → UnitAddCircle) :
    0 ≤ familyMaxPower p F y := by
  let i : ι := Classical.choice inferInstance
  exact (pow_nonneg (norm_nonneg _) p).trans
    (norm_pow_le_familyMaxPower p F i y)

lemma continuous_familyMaxPower
    {ι : Type*} [Fintype ι] [Nonempty ι] {r : ℕ} {L : Fin r → ℕ}
    (p : ℕ) (F : ι → (Fin r → UnitAddCircle) → ℂ)
    (hF : ∀ i, HasBoundedSpectrum L (F i)) :
    Continuous (familyMaxPower p F) := by
  unfold familyMaxPower
  apply Continuous.finset_sup'_apply Finset.univ_nonempty
  intro i hi
  exact (hF i).continuous.norm.pow p

/-- Positive-even-exponent form of Proposition 4.2.  Taking
`2*q = K(k) = k(k-1)` gives exactly the exponent used by the orbit-collision
argument. -/
theorem anisotropicSampling_even
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {r : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (q : ℕ) (hq : 0 < q)
    (L : Fin r → ℕ) (hL : ∀ j, 0 < L j)
    (x : ι → Fin r → UnitAddCircle)
    (hsep : AnisotropicallySeparated δ L x)
    (F : ι → (Fin r → UnitAddCircle) → ℂ)
    (hF : ∀ i, HasBoundedSpectrum L (F i)) :
    (∑ i : ι, ‖F i (x i)‖ ^ (2 * q)) ≤
      ((130 * (q : ℝ) * cellComparisonFactor δ) ^ r *
          ∏ j : Fin r, (L j : ℝ)) *
        ∫ y, familyMaxPower (2 * q) F y ∂torusHaarMeasure r := by
  classical
  let P : Fin r → ℕ := BoundedSpectrumExpansion.scaleBounds (2 * q) L
  let G : ι → (Fin r → UnitAddCircle) → ℂ :=
    fun i y => (F i y * star (F i y)) ^ q
  have hP (j : Fin r) : 0 < P j := by
    dsimp [P, BoundedSpectrumExpansion.scaleBounds]
    exact Nat.mul_pos (by omega) (hL j)
  have hGP (i : ι) : HasBoundedSpectrum P (G i) := by
    dsimp [P, G]
    exact (hF i).normSqPow q
  have hsepP : AnisotropicallySeparated δ P x := by
    intro a b hab
    obtain ⟨j, hj⟩ := hsep hab
    refine ⟨j, hj.trans ?_⟩
    apply mul_le_mul_of_nonneg_right
    · norm_cast
      exact Nat.le_mul_of_pos_left (L j) (by omega : 0 < 2 * q)
    · exact norm_nonneg _
  have hnormG (i : ι) (y : Fin r → UnitAddCircle) :
      ‖G i y‖ = ‖F i y‖ ^ (2 * q) := by
    dsimp [G]
    rw [norm_pow, norm_mul]
    simp only [starRingEnd_apply, norm_star]
    rw [← pow_two, ← pow_mul]
  have hsample := anisotropicSampling_of_majorant hδ P hP x hsepP G hGP
    (familyMaxPower (2 * q) F)
    (continuous_familyMaxPower (2 * q) F hF)
    (familyMaxPower_nonneg (2 * q) F)
    (fun i y => by
      rw [hnormG]
      exact norm_pow_le_familyMaxPower (2 * q) F i y)
  have hprodP :
      (∏ j : Fin r, (P j : ℝ)) =
        (2 * (q : ℝ)) ^ r * ∏ j : Fin r, (L j : ℝ) := by
    dsimp [P, BoundedSpectrumExpansion.scaleBounds]
    simp only [Nat.cast_mul, Nat.cast_ofNat, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [mul_pow]
  calc
    (∑ i : ι, ‖F i (x i)‖ ^ (2 * q)) =
        ∑ i : ι, ‖G i (x i)‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hnormG]
    _ ≤ ((65 * cellComparisonFactor δ) ^ r *
          ∏ j : Fin r, (P j : ℝ)) *
        ∫ y, familyMaxPower (2 * q) F y ∂torusHaarMeasure r := hsample
    _ = ((130 * (q : ℝ) * cellComparisonFactor δ) ^ r *
          ∏ j : Fin r, (L j : ℝ)) *
        ∫ y, familyMaxPower (2 * q) F y ∂torusHaarMeasure r := by
      rw [hprodP]
      have hbase :
          (65 * cellComparisonFactor δ) * (2 * (q : ℝ)) =
            130 * (q : ℝ) * cellComparisonFactor δ := by ring
      have hpows :
          (65 * cellComparisonFactor δ) ^ r * (2 * (q : ℝ)) ^ r =
            (130 * (q : ℝ) * cellComparisonFactor δ) ^ r := by
        rw [← mul_pow, hbase]
      calc
        (65 * cellComparisonFactor δ) ^ r *
              ((2 * (q : ℝ)) ^ r * ∏ j : Fin r, (L j : ℝ)) *
            ∫ y, familyMaxPower (2 * q) F y ∂torusHaarMeasure r =
            ((65 * cellComparisonFactor δ) ^ r * (2 * (q : ℝ)) ^ r) *
              (∏ j : Fin r, (L j : ℝ)) *
            ∫ y, familyMaxPower (2 * q) F y ∂torusHaarMeasure r := by ring
        _ = ((130 * (q : ℝ) * cellComparisonFactor δ) ^ r *
              ∏ j : Fin r, (L j : ℝ)) *
            ∫ y, familyMaxPower (2 * q) F y ∂torusHaarMeasure r := by
          rw [hpows]

/-- Half of the critical Vinogradov exponent `K(k)=k(k-1)`. -/
def criticalHalfExponent (k : ℕ) : ℕ := K k / 2

lemma two_mul_criticalHalfExponent (k : ℕ) :
    2 * criticalHalfExponent k = K k := by
  unfold criticalHalfExponent K
  exact Nat.mul_div_cancel' (Nat.even_mul_pred_self k).two_dvd

lemma criticalHalfExponent_pos {k : ℕ} (hk : 2 ≤ k) :
    0 < criticalHalfExponent k := by
  unfold criticalHalfExponent
  apply Nat.div_pos
  · unfold K
    calc
      2 = 2 * 1 := by omega
      _ ≤ k * (k - 1) := Nat.mul_le_mul hk (by omega)
  · norm_num

/-- Proposition 4.2 specialized exactly to the paper's critical exponent
`K(k)=k(k-1)`. -/
theorem anisotropicSampling_criticalExponent
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {r : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (k : ℕ) (hk : 2 ≤ k)
    (L : Fin r → ℕ) (hL : ∀ j, 0 < L j)
    (x : ι → Fin r → UnitAddCircle)
    (hsep : AnisotropicallySeparated δ L x)
    (F : ι → (Fin r → UnitAddCircle) → ℂ)
    (hF : ∀ i, HasBoundedSpectrum L (F i)) :
    (∑ i : ι, ‖F i (x i)‖ ^ K k) ≤
      ((130 * (criticalHalfExponent k : ℝ) * cellComparisonFactor δ) ^ r *
          ∏ j : Fin r, (L j : ℝ)) *
        ∫ y, familyMaxPower (K k) F y ∂torusHaarMeasure r := by
  simpa only [two_mul_criticalHalfExponent] using
    anisotropicSampling_even hδ (criticalHalfExponent k)
      (criticalHalfExponent_pos hk) L hL x hsep F hF

end Sampling
end ImprovedWeylBounds
