import ImprovedWeylBounds.Conditional.FiniteFieldConsequences
import ImprovedWeylBounds.Asymptotics

/-!
# Fully quantified finite-field corollaries

This file expands the numerical and asymptotic bookkeeping in Corollaries
7.1--7.3 of `main.tex` (lines 1184--1296).  The only external input is the
explicit `External.ErdosTuran` proposition in the discrepancy statements;
all floor, logarithm, cyclic-interval, and epsilon-selection steps are proved
here.
-/

open scoped BigOperators
open Filter Polynomial

namespace ImprovedWeylBounds
namespace Conditional

open External Applications

noncomputable section

/-- The loss-free scale `E_d(p,H)` from equation (7.5). -/
noncomputable def finiteFieldScale (d p H : ℕ) : ℝ :=
  Real.rpow (p : ℝ) (1 / (d : ℝ)) +
    Real.rpow (H : ℝ) (1 - 1 / (Delta d : ℝ))

lemma finiteFieldScale_pos {d p H : ℕ} (hp : 0 < p) (hH : 0 < H) :
    0 < finiteFieldScale d p H := by
  unfold finiteFieldScale
  exact add_pos (Real.rpow_pos_of_pos (by exact_mod_cast hp) _)
    (Real.rpow_pos_of_pos (by exact_mod_cast hH) _)

lemma finiteFieldScale_gt_one {d p H : ℕ}
    (hd : 0 < d) (hp : 1 < p) (hH : 0 < H) :
    1 < finiteFieldScale d p H := by
  unfold finiteFieldScale
  have hpow : 1 < Real.rpow (p : ℝ) (1 / (d : ℝ)) := by
    apply Real.one_lt_rpow
    · exact_mod_cast hp
    · positivity
  exact hpow.trans_le (le_add_of_nonneg_right (Real.rpow_nonneg (by positivity) _))

/-- Factoring the auxiliary `H^ε` out of the two branches of the short-sum
bound. -/
lemma finiteFieldScale_mul_rpow
    {d p H : ℕ} (hH : 0 < H) (ε : ℝ) :
    finiteFieldScale d p H * Real.rpow (H : ℝ) ε =
      Real.rpow (p : ℝ) (1 / (d : ℝ)) * Real.rpow (H : ℝ) ε +
        Real.rpow (H : ℝ) (1 - 1 / (Delta d : ℝ) + ε) := by
  unfold finiteFieldScale
  rw [add_mul]
  congr 1
  exact (Real.rpow_add (by exact_mod_cast hH : (0 : ℝ) < H)
    (1 - 1 / (Delta d : ℝ)) ε).symm

/-- A finite count discrepancy is always at most the sample size. -/
lemma halfOpenDiscrepancyAtMost_card
    {H : ℕ} (x : Fin H → ℝ) :
    HalfOpenDiscrepancyAtMost x H := by
  classical
  intro a b ha hab hb
  have hcountNat : countInHalfOpenModOne x a b ≤ H := by
    unfold countInHalfOpenModOne
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
      (Finset.card_univ.trans (Fintype.card_fin H))
  have hcount : (countInHalfOpenModOne x a b : ℝ) ≤ H := by
    exact_mod_cast hcountNat
  have hlength0 : 0 ≤ b - a := sub_nonneg.mpr hab
  have hlength1 : b - a ≤ 1 := by linarith
  have hexpect0 : 0 ≤ (H : ℝ) * (b - a) :=
    mul_nonneg (Nat.cast_nonneg H) hlength0
  have hexpectH : (H : ℝ) * (b - a) ≤ H := by
    have hHr : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
    nlinarith
  have hHr : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
  rw [abs_le]
  constructor <;> linarith

/-- Raising an `H^ε` factor to a natural power multiplies the real
exponent. -/
lemma rpow_pow_eq_rpow_nat_mul
    {H s : ℕ} (_hH : 0 < H) (ε : ℝ) :
    (Real.rpow (H : ℝ) ε) ^ s =
      Real.rpow (H : ℝ) ((s : ℝ) * ε) := by
  calc
    (Real.rpow (H : ℝ) ε) ^ s =
        Real.rpow (Real.rpow (H : ℝ) ε) (s : ℝ) :=
      (Real.rpow_natCast (Real.rpow (H : ℝ) ε) s).symm
    _ = Real.rpow (H : ℝ) (ε * (s : ℝ)) :=
      (Real.rpow_mul (by exact_mod_cast (Nat.zero_le H) : (0 : ℝ) ≤ H)
        ε (s : ℝ)).symm
    _ = Real.rpow (H : ℝ) ((s : ℝ) * ε) := by ring_nf

/-- Length of the oriented half-open cyclic interval from `a` to `b` in
`[0,1)`. -/
def cyclicHalfOpenLength (a b : ℝ) : ℝ :=
  if a ≤ b then b - a else (1 - a) + b

/-- The oriented cyclic interval from `a` to `b` contains no sample point.
In the wrapping case this explicitly records both ordinary empty pieces. -/
def EmptyCyclicHalfOpen {H : ℕ} (x : Fin H → ℝ) (a b : ℝ) : Prop :=
  if a ≤ b then countInHalfOpenModOne x a b = 0
  else countInHalfOpenModOne x a 1 = 0 ∧
    countInHalfOpenModOne x 0 b = 0

/-- Exact cyclic-interval splitting: an empty cyclic interval has normalized
length at most twice the ordinary discrepancy divided by `H`. -/
theorem emptyCyclicHalfOpen_length_le
    {H : ℕ} (hH : 1 ≤ H) {x : Fin H → ℝ} {B a b : ℝ}
    (hB : 0 ≤ B) (hdisc : HalfOpenDiscrepancyAtMost x B)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (hempty : EmptyCyclicHalfOpen x a b) :
    cyclicHalfOpenLength a b ≤ 2 * B / H := by
  by_cases hab : a ≤ b
  · rw [cyclicHalfOpenLength, if_pos hab]
    rw [EmptyCyclicHalfOpen, if_pos hab] at hempty
    have hordinary := empty_interval_length_le hH hdisc ha hab hb1 hempty
    calc
      b - a ≤ B / H := hordinary
      _ ≤ 2 * B / H := by
        have hHr : (0 : ℝ) < H := by positivity
        apply (div_le_div_iff_of_pos_right hHr).2
        linarith
  · have hba : b ≤ a := le_of_not_ge hab
    rw [cyclicHalfOpenLength, if_neg hab]
    rw [EmptyCyclicHalfOpen, if_neg hab] at hempty
    have hfirst := empty_interval_length_le hH hdisc ha ha1 le_rfl hempty.1
    have hsecond := empty_interval_length_le hH hdisc (by norm_num) hb hb1 hempty.2
    calc
      (1 - a) + b = (1 - a) + (b - 0) := by ring
      _ ≤ B / H + B / H := add_le_add hfirst hsecond
      _ = 2 * B / H := by ring

/-- A count-discrepancy bound converted to the paper's residue-length scale.
The conclusion measures a cyclic arc of normalized length `Y/p` as `Y`. -/
theorem emptyCyclicHalfOpen_residueLength_le
    {p H : ℕ} (hH : 1 ≤ H) {x : Fin H → ℝ} {B a b : ℝ}
    (hB : 0 ≤ B) (hdisc : HalfOpenDiscrepancyAtMost x B)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (hempty : EmptyCyclicHalfOpen x a b) :
    (p : ℝ) * cyclicHalfOpenLength a b ≤ 2 * (p : ℝ) * B / H := by
  have h := emptyCyclicHalfOpen_length_le hH hB hdisc ha ha1 hb hb1 hempty
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  calc
    (p : ℝ) * cyclicHalfOpenLength a b ≤ (p : ℝ) * (2 * B / H) := by
      gcongr
    _ = 2 * (p : ℝ) * B / H := by ring

/-- Availability of the finite-field short-sum estimate with every positive
power loss.  This is the quantified input needed when a corollary chooses a
smaller auxiliary epsilon. -/
def FiniteFieldShortIntervalBoundsAllLosses (d : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → FiniteFieldShortIntervalBoundAll d ε

/-- Corollary 7.1 (`main.tex`, lines 1184--1211), with all constants and the
choice `T = floor(H/E_d(p,H))` made explicit.  The result is in fact uniform
for every `H ≥ 1`, stronger than an eventual formulation. -/
theorem finiteFieldDiscrepancyCorollary
    (hErdosTuran : ErdosTuran)
    (d : ℕ) (hd : 3 ≤ d) (ε : ℝ) (hε : 0 < ε)
    (hAll : FiniteFieldShortIntervalBoundsAllLosses d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (p H : ℕ) [NeZero p], p.Prime → d < p →
        ∀ (M : ℤ) (P : (ZMod p)[X]),
          1 ≤ H → H ≤ p → P.natDegree = d →
          HalfOpenDiscrepancyAtMost
            (normalizedIntervalPolynomialValue p P M H)
            (C * finiteFieldScale d p H * Real.rpow (H : ℝ) ε) := by
  let η : ℝ := ε / 2
  have hη : 0 < η := by dsimp [η]; linarith
  obtain ⟨C₀, hC₀, htrunc⟩ :=
    finiteFieldDiscrepancyAtTruncation hErdosTuran d η (hAll η hη)
  let C : ℝ := 3 + 3 * C₀ * (1 + 1 / η)
  have hfactor : 0 < 1 + 1 / η := by positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro p H _ hp hdp M P hH hHp hdeg
  have hHpos : 0 < H := by omega
  have hpPos : 0 < p := hp.pos
  let E : ℝ := finiteFieldScale d p H
  have hEpos : 0 < E := finiteFieldScale_pos hpPos hHpos
  have hEone : 1 < E :=
    finiteFieldScale_gt_one (by omega) (by omega) hHpos
  have hHreal : (0 : ℝ) < H := by exact_mod_cast hHpos
  have hHηone : 1 ≤ Real.rpow (H : ℝ) η := by
    simpa using Real.one_le_rpow (by exact_mod_cast hH : (1 : ℝ) ≤ H) hη.le
  have hHεone : 1 ≤ Real.rpow (H : ℝ) ε := by
    simpa using Real.one_le_rpow (by exact_mod_cast hH : (1 : ℝ) ≤ H) hε.le
  by_cases hlarge : (H : ℝ) / 2 ≤ E
  · apply halfOpenDiscrepancyAtMost_mono
      (halfOpenDiscrepancyAtMost_card
        (normalizedIntervalPolynomialValue p P M H))
    have hCtwo : (2 : ℝ) ≤ C := by
      dsimp [C]
      have hnonneg : 0 ≤ 3 * C₀ * (1 + 1 / η) := by positivity
      linarith
    calc
      (H : ℝ) ≤ 2 * E := by linarith
      _ ≤ C * E := mul_le_mul_of_nonneg_right hCtwo hEpos.le
      _ ≤ C * E * Real.rpow (H : ℝ) ε := by
        simpa only [mul_one] using
          (mul_le_mul_of_nonneg_left hHεone
            (mul_nonneg hC.le hEpos.le))
  · have hshort : E < (H : ℝ) / 2 := lt_of_not_ge hlarge
    let T : ℕ := ⌊(H : ℝ) / E⌋₊
    have hratioNonneg : 0 ≤ (H : ℝ) / E := by positivity
    have hratioTwo : (2 : ℝ) < (H : ℝ) / E := by
      rw [lt_div_iff₀ hEpos]
      linarith
    have hT : 1 ≤ T := by
      dsimp [T]
      rw [Nat.one_le_floor_iff]
      linarith
    have hTcast_le : (T : ℝ) ≤ (H : ℝ) / E := by
      dsimp [T]
      exact Nat.floor_le hratioNonneg
    have hratio_lt_H : (H : ℝ) / E < H := by
      rw [div_lt_iff₀ hEpos]
      nlinarith
    have hTltHreal : (T : ℝ) < H := hTcast_le.trans_lt hratio_lt_H
    have hTltH : T < H := by exact_mod_cast hTltHreal
    have hTp : T < p := hTltH.trans_le hHp
    have hfloorUpper : (H : ℝ) / E < (T + 1 : ℕ) := by
      dsimp [T]
      simpa only [Nat.cast_add, Nat.cast_one] using
        Nat.lt_floor_add_one ((H : ℝ) / E)
    have hfirst : 3 * (H : ℝ) / (T + 1 : ℕ) ≤ 3 * E := by
      have hden : (0 : ℝ) < (T + 1 : ℕ) := by positivity
      have hdiv : (H : ℝ) / (T + 1 : ℕ) < E := by
        rw [div_lt_iff₀ hden]
        rw [div_lt_iff₀ hEpos] at hfloorUpper
        nlinarith
      calc
        3 * (H : ℝ) / (T + 1 : ℕ) =
            3 * ((H : ℝ) / (T + 1 : ℕ)) := by ring
        _ ≤ 3 * E := mul_le_mul_of_nonneg_left hdiv.le (by norm_num)
    have hlogTH : Real.log T ≤ Real.log H := by
      apply Real.log_le_log
      · positivity
      · exact_mod_cast hTltH.le
    have hlog : 1 + Real.log T ≤
        (1 + 1 / η) * Real.rpow (H : ℝ) η := by
      calc
        1 + Real.log T ≤ 1 + Real.log H := by linarith
        _ ≤ (1 + 1 / η) * Real.rpow (H : ℝ) η :=
          one_add_log_nat_le_rpow H hH η hη
    have hscale :
        Real.rpow (p : ℝ) (1 / (d : ℝ)) * Real.rpow (H : ℝ) η +
            Real.rpow (H : ℝ) (1 - 1 / (Delta d : ℝ) + η) =
          E * Real.rpow (H : ℝ) η := by
      dsimp [E]
      exact (finiteFieldScale_mul_rpow hHpos η).symm
    have hηη : η + η = ε := by dsimp [η]; ring
    have hpowcombine :
        Real.rpow (H : ℝ) η * Real.rpow (H : ℝ) η =
          Real.rpow (H : ℝ) ε := by
      calc
        Real.rpow (H : ℝ) η * Real.rpow (H : ℝ) η =
            Real.rpow (H : ℝ) (η + η) :=
          (Real.rpow_add hHreal η η).symm
        _ = Real.rpow (H : ℝ) ε := by rw [hηη]
    apply halfOpenDiscrepancyAtMost_mono
      (htrunc p H hp hdp M P hH hHp hdeg T hT hTp)
    rw [hscale]
    calc
      3 * (H : ℝ) / (T + 1 : ℕ) +
          3 * (C₀ * (E * Real.rpow (H : ℝ) η)) *
            (1 + Real.log T) ≤
          3 * E + 3 * (C₀ * (E * Real.rpow (H : ℝ) η)) *
            ((1 + 1 / η) * Real.rpow (H : ℝ) η) := by
        gcongr
      _ = 3 * E +
          (3 * C₀ * (1 + 1 / η)) * E *
            Real.rpow (H : ℝ) ε := by rw [← hpowcombine]; ring
      _ ≤ 3 * E * Real.rpow (H : ℝ) ε +
          (3 * C₀ * (1 + 1 / η)) * E *
            Real.rpow (H : ℝ) ε := by
        have hgrow : 3 * E ≤ 3 * E * Real.rpow (H : ℝ) ε := by
          simpa only [mul_one] using
            (mul_le_mul_of_nonneg_left hHεone (by positivity : 0 ≤ 3 * E))
        exact add_le_add hgrow le_rfl
      _ = C * E * Real.rpow (H : ℝ) ε := by
        dsimp [C]
        ring

/-- Every empty oriented cyclic interval has residue-scale length at most
`G`.  Multiplication by `p` converts normalized circle length to the number
of residue spacings. -/
def CyclicResidueGapAtMost
    (p : ℕ) {H : ℕ} (x : Fin H → ℝ) (G : ℝ) : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 →
    EmptyCyclicHalfOpen x a b →
      (p : ℝ) * cyclicHalfOpenLength a b ≤ G

/-- Corollary 7.2 (`main.tex`, lines 1225--1242).  The factor two is the
explicit loss from splitting a wrapping cyclic interval at zero. -/
theorem finiteFieldGapCorollary
    (hErdosTuran : ErdosTuran)
    (d : ℕ) (hd : 3 ≤ d) (ε : ℝ) (hε : 0 < ε)
    (hAll : FiniteFieldShortIntervalBoundsAllLosses d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (p H : ℕ) [NeZero p], p.Prime → d < p →
        ∀ (M : ℤ) (P : (ZMod p)[X]),
          1 ≤ H → H ≤ p → P.natDegree = d →
          CyclicResidueGapAtMost p
            (normalizedIntervalPolynomialValue p P M H)
            (C * ((p : ℝ) / H) * finiteFieldScale d p H *
              Real.rpow (H : ℝ) ε) := by
  obtain ⟨C₀, hC₀, hdisc⟩ :=
    finiteFieldDiscrepancyCorollary hErdosTuran d hd ε hε hAll
  refine ⟨2 * C₀, by positivity, ?_⟩
  intro p H _ hp hdp M P hH hHp hdeg a b ha ha1 hb hb1 hempty
  let B : ℝ := C₀ * finiteFieldScale d p H * Real.rpow (H : ℝ) ε
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg
      (mul_nonneg hC₀.le
        (finiteFieldScale_pos hp.pos (by omega : 0 < H)).le)
      (Real.rpow_nonneg (by positivity) _)
  have hsplit := emptyCyclicHalfOpen_residueLength_le
    (p := p) hH hB (hdisc p H hp hdp M P hH hHp hdeg)
      ha ha1 hb hb1 hempty
  dsimp [B] at hsplit
  calc
    (p : ℝ) * cyclicHalfOpenLength a b ≤
        2 * (p : ℝ) *
          (C₀ * finiteFieldScale d p H * Real.rpow (H : ℝ) ε) / H :=
      hsplit
    _ = (2 * C₀) * ((p : ℝ) / H) * finiteFieldScale d p H *
          Real.rpow (H : ℝ) ε := by ring

/-- The auxiliary loss selected in Corollary 7.3.  It satisfies
`s * additiveAuxiliaryLoss s η = η/2` when `s > 0`. -/
noncomputable def additiveAuxiliaryLoss (s : ℕ) (η : ℝ) : ℝ :=
  η / (2 * (s : ℝ))

lemma additiveAuxiliaryLoss_pos
    {s : ℕ} {η : ℝ} (hs : 1 ≤ s) (hη : 0 < η) :
    0 < additiveAuxiliaryLoss s η := by
  unfold additiveAuxiliaryLoss
  positivity

lemma nat_mul_additiveAuxiliaryLoss
    {s : ℕ} {η : ℝ} (hs : 1 ≤ s) :
    (s : ℝ) * additiveAuxiliaryLoss s η = η / 2 := by
  unfold additiveAuxiliaryLoss
  have hs0 : (s : ℝ) ≠ 0 := by positivity
  field_simp

/-- Corollary 7.3 (`main.tex`, lines 1261--1296).  The returned `C` is the
uniform short-sum constant at the internally selected loss
`η/(2s)`.  The returned threshold explicitly ensures
`C^s H^(η/2) < H^η`; this is the precise sufficiently-large-`H` content
hidden by the manuscript's `o(H^s/p)` notation. -/
theorem finiteFieldAdditiveBasisCorollary
    (d : ℕ) (_hd : 3 ≤ d) (s : ℕ) (hs : 1 ≤ s)
    (η : ℝ) (hη : 0 < η)
    (hAll : FiniteFieldShortIntervalBoundsAllLosses d) :
    ∃ C : ℝ, 0 < C ∧ ∃ H₀ : ℕ, 1 ≤ H₀ ∧
      (∀ H : ℕ, H₀ ≤ H →
        C ^ s * Real.rpow (H : ℝ) (η / 2) <
          Real.rpow (H : ℝ) η) ∧
      ∀ (p H : ℕ) [NeZero p], p.Prime → d < p →
        ∀ (M : ℤ) (P : (ZMod p)[X]),
          H₀ ≤ H → H ≤ p → P.natDegree = d →
          (p : ℝ) * Real.rpow (H : ℝ) η ≤
            ((H : ℝ) / finiteFieldScale d p H) ^ s →
          ∀ a : ZMod p,
            0 < representationCount (s := s)
              (intervalPolynomialValue p P M H) a := by
  let ε₀ : ℝ := additiveAuxiliaryLoss s η
  have hε₀ : 0 < ε₀ := additiveAuxiliaryLoss_pos hs hη
  obtain ⟨C, hC, hbasis⟩ :=
    finiteFieldAdditiveBasis_of_shortSum d ε₀ (hAll ε₀ hε₀)
  have hexponents : η / 2 < η := by linarith
  have hevent := eventually_const_mul_rpow_lt_rpow
    (C ^ s) (η / 2) η hexponents
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hevent
  let H₀ : ℕ := max 1 N₀
  have hH₀ : 1 ≤ H₀ := le_max_left 1 N₀
  have hthreshold : ∀ H : ℕ, H₀ ≤ H →
      C ^ s * Real.rpow (H : ℝ) (η / 2) <
        Real.rpow (H : ℝ) η := by
    intro H hHH₀
    exact hN₀ H ((le_max_right 1 N₀).trans hHH₀)
  refine ⟨C, hC, H₀, hH₀, hthreshold, ?_⟩
  intro p H _ hp hdp M P hHH₀ hHp hdeg hcondition a
  have hH : 1 ≤ H := hH₀.trans hHH₀
  have hHpos : 0 < H := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  let E : ℝ := finiteFieldScale d p H
  have hEpos : 0 < E := finiteFieldScale_pos hp.pos hHpos
  have hscale :
      Real.rpow (p : ℝ) (1 / (d : ℝ)) * Real.rpow (H : ℝ) ε₀ +
          Real.rpow (H : ℝ) (1 - 1 / (Delta d : ℝ) + ε₀) =
        E * Real.rpow (H : ℝ) ε₀ := by
    dsimp [E]
    exact (finiteFieldScale_mul_rpow hHpos ε₀).symm
  have hsexponent : (s : ℝ) * ε₀ = η / 2 := by
    dsimp [ε₀]
    exact nat_mul_additiveAuxiliaryLoss hs
  have hsmall :
      C ^ s * Real.rpow (H : ℝ) ((s : ℝ) * ε₀) <
        Real.rpow (H : ℝ) η := by
    rw [hsexponent]
    exact hthreshold H hHH₀
  have hEpowpos : 0 < E ^ s := pow_pos hEpos s
  have hcondition' :
      (p : ℝ) * Real.rpow (H : ℝ) η * E ^ s ≤ (H : ℝ) ^ s := by
    calc
      (p : ℝ) * Real.rpow (H : ℝ) η * E ^ s ≤
          (((H : ℝ) / E) ^ s) * E ^ s :=
        mul_le_mul_of_nonneg_right hcondition hEpowpos.le
      _ = (H : ℝ) ^ s := by
        rw [div_pow]
        field_simp
  have hleft :
      (C * (E * Real.rpow (H : ℝ) ε₀)) ^ s =
        C ^ s * E ^ s *
          Real.rpow (H : ℝ) ((s : ℝ) * ε₀) := by
    rw [mul_pow, mul_pow, rpow_pow_eq_rpow_nat_mul hHpos ε₀]
    ring
  have hsmallScaled :
      (p : ℝ) *
          (C ^ s * Real.rpow (H : ℝ) ((s : ℝ) * ε₀)) * E ^ s <
        (p : ℝ) * Real.rpow (H : ℝ) η * E ^ s := by
    simpa only [mul_assoc] using
      (mul_lt_mul_of_pos_left
        (mul_lt_mul_of_pos_right hsmall hEpowpos) hpR)
  have hmain :
      (C * (E * Real.rpow (H : ℝ) ε₀)) ^ s <
        (H : ℝ) ^ s / (p : ℝ) := by
    rw [hleft]
    apply (lt_div_iff₀ hpR).2
    calc
      (C ^ s * E ^ s *
          Real.rpow (H : ℝ) ((s : ℝ) * ε₀)) * (p : ℝ) =
          (p : ℝ) *
            (C ^ s * Real.rpow (H : ℝ) ((s : ℝ) * ε₀)) * E ^ s := by
        ring
      _ < (p : ℝ) * Real.rpow (H : ℝ) η * E ^ s := hsmallScaled
      _ ≤ (H : ℝ) ^ s := hcondition'
  apply hbasis p H hp hdp M P hH hHp hdeg s a
  rw [hscale]
  exact hmain

end

end Conditional
end ImprovedWeylBounds
