import ImprovedWeylBounds.Conditional.Compression
import ImprovedWeylBounds.Conditional.Inverse

/-!
# Assembly of the new inverse theorem

The geometric part of the paper produces a preliminary denominator bounded
by `N`.  This file isolates that output as a proposition and verifies all of
the remaining internal bookkeeping: Baker's amplitude condition, denominator
compression, and weakening the auxiliary loss to the user-requested loss.
-/

namespace ImprovedWeylBounds.Conditional

open ImprovedWeylBounds External

/-- Exact interface for the output of the all-cuts/collision argument.  This
is internal to the manuscript; it is separated here so the subsequent use of
the genuinely external Baker lemma has a visible trust boundary. -/
def PreliminaryApproximationPrinciple (k : ℕ) : Prop :=
  ∀ thresholdMargin : ℝ, 0 < thresholdMargin →
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ (N : ℕ), N₀ ≤ N →
      ∀ (α : CoefficientVector k) (A : ℝ),
        0 < A → A ≤ ‖g α N‖ →
        Real.rpow (N : ℝ)
            (1 - 1 / (K k : ℝ) + thresholdMargin) < A →
        ∃ pre : PreliminaryApproximation k N α, pre.r ≤ N

/-- Once the collision argument has supplied its preliminary denominator,
Baker compression proves the new inverse principle with denominator `K k`.
Every comparison of exponents appearing in the prose proof is explicit. -/
theorem inversePrinciple_of_preliminary
    (hBaker : BakerCompression) (k : ℕ) (hk : 3 ≤ k)
    (hPreliminary : PreliminaryApproximationPrinciple k) :
    InversePrinciple k (K k) := by
  obtain ⟨η₀, hη₀, hCompress⟩ :=
    simultaneousApproximation_of_bakerCompression hBaker k hk
  have hkK_nat : k < K k := by
    rw [K]
    have hkpos : 0 < k := by omega
    have hkminus : 1 < k - 1 := by omega
    nlinarith
  have hkR : (0 : ℝ) < k := by positivity
  have hgap : 0 < (1 / (k : ℝ) - 1 / (K k : ℝ)) := by
    have hinv : 1 / (K k : ℝ) < 1 / (k : ℝ) :=
      one_div_lt_one_div_of_lt hkR (by exact_mod_cast hkK_nat)
    linarith
  intro thresholdMargin loss hmargin hloss
  let aux : ℝ := min η₀ (min loss (1 / (k : ℝ) - 1 / (K k : ℝ))) / 2
  have haux : 0 < aux := by
    dsimp [aux]
    exact div_pos (lt_min hη₀ (lt_min hloss hgap)) (by norm_num)
  have haux_eta₀ : aux ≤ η₀ := by
    dsimp [aux]
    exact (div_le_self (le_of_lt (lt_min hη₀ (lt_min hloss hgap))) (by norm_num)).trans
      (min_le_left _ _)
  have haux_loss : aux ≤ loss := by
    dsimp [aux]
    have hminpos : 0 < min η₀ (min loss (1 / (k : ℝ) - 1 / (K k : ℝ))) :=
      lt_min hη₀ (lt_min hloss hgap)
    calc
      min η₀ (min loss (1 / (k : ℝ) - 1 / (K k : ℝ))) / 2
          ≤ min η₀ (min loss (1 / (k : ℝ) - 1 / (K k : ℝ))) := by linarith
      _ ≤ min loss (1 / (k : ℝ) - 1 / (K k : ℝ)) := min_le_right _ _
      _ ≤ loss := min_le_left _ _
  have haux_gap : aux < 1 / (k : ℝ) - 1 / (K k : ℝ) := by
    dsimp [aux]
    have hminpos : 0 < min η₀ (min loss (1 / (k : ℝ) - 1 / (K k : ℝ))) :=
      lt_min hη₀ (lt_min hloss hgap)
    calc
      min η₀ (min loss (1 / (k : ℝ) - 1 / (K k : ℝ))) / 2
          < min η₀ (min loss (1 / (k : ℝ) - 1 / (K k : ℝ))) := by linarith
      _ ≤ min loss (1 / (k : ℝ) - 1 / (K k : ℝ)) := min_le_right _ _
      _ ≤ 1 / (k : ℝ) - 1 / (K k : ℝ) := min_le_right _ _
  obtain ⟨NB, hNB, hCompressN⟩ := hCompress aux haux haux_eta₀
  obtain ⟨NP, hNP, hPreN⟩ := hPreliminary thresholdMargin hmargin
  let N₀ := max NB NP
  refine ⟨1, by norm_num, N₀, ?_, ?_⟩
  · dsimp [N₀]
    omega
  · intro N hN α A hA hlarge hamp
    have hNBle : NB ≤ N := le_trans (le_max_left _ _) hN
    have hNPle : NP ≤ N := le_trans (le_max_right _ _) hN
    obtain ⟨pre, hpreN⟩ := hPreN N hNPle α A hA hlarge hamp
    have hNtwo : 2 ≤ N := hNP.trans hNPle
    have hNone : (1 : ℝ) < N := by exact_mod_cast hNtwo
    have hexp_nonneg : 0 ≤ 1 - 1 / (k : ℝ) := by
      have hkone : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
      have hinvle : 1 / (k : ℝ) ≤ 1 := (div_le_one hkR).2 hkone
      linarith
    have hrNreal : (pre.r : ℝ) ≤ (N : ℝ) := by exact_mod_cast hpreN
    have hrpow :
        Real.rpow (pre.r : ℝ) (1 - 1 / (k : ℝ)) ≤
          Real.rpow (N : ℝ) (1 - 1 / (k : ℝ)) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hrNreal hexp_nonneg
    have hexponents :
        1 - 1 / (k : ℝ) + aux <
          1 - 1 / (K k : ℝ) + thresholdMargin := by
      linarith
    have hampBaker :
        Real.rpow (pre.r : ℝ) (1 - 1 / (k : ℝ)) *
            Real.rpow (N : ℝ) aux < A := by
      calc
        Real.rpow (pre.r : ℝ) (1 - 1 / (k : ℝ)) *
              Real.rpow (N : ℝ) aux
            ≤ Real.rpow (N : ℝ) (1 - 1 / (k : ℝ)) *
                Real.rpow (N : ℝ) aux :=
              mul_le_mul_of_nonneg_right hrpow (Real.rpow_nonneg (by positivity) _)
        _ = Real.rpow (N : ℝ) (1 - 1 / (k : ℝ) + aux) := by
              exact (Real.rpow_add (by positivity : (0 : ℝ) < N) _ _).symm
        _ < Real.rpow (N : ℝ)
              (1 - 1 / (K k : ℝ) + thresholdMargin) :=
            Real.rpow_lt_rpow_of_exponent_lt hNone hexponents
        _ < A := hamp
    obtain ⟨approx⟩ := hCompressN N hNBle α A hA hlarge pre hampBaker
    have hpowLoss : Real.rpow (N : ℝ) aux ≤ Real.rpow (N : ℝ) loss :=
      Real.rpow_le_rpow_of_exponent_le hNone.le haux_loss
    refine ⟨⟨approx.q, approx.q_pos, approx.numerator, ?_, ?_⟩⟩
    · calc
        (approx.q : ℝ) ≤
            1 * (((N : ℝ) / A) ^ k) * Real.rpow (N : ℝ) aux :=
          approx.denominator_bound
        _ ≤ 1 * (((N : ℝ) / A) ^ k) * Real.rpow (N : ℝ) loss := by
          gcongr
    · intro j
      have hjexp :
          -((j.val + 1 : ℕ) : ℝ) + aux ≤
            -((j.val + 1 : ℕ) : ℝ) + loss := by linarith
      calc
        |(approx.q : ℝ) * α j - (approx.numerator j : ℝ)| ≤
            1 * (((N : ℝ) / A) ^ k) *
              Real.rpow (N : ℝ) (-((j.val + 1 : ℕ) : ℝ) + aux) :=
          approx.coefficient_bound j
        _ ≤ 1 * (((N : ℝ) / A) ^ k) *
              Real.rpow (N : ℝ) (-((j.val + 1 : ℕ) : ℝ) + loss) := by
          gcongr
          exact Real.rpow_le_rpow_of_exponent_le hNone.le hjexp

end ImprovedWeylBounds.Conditional
