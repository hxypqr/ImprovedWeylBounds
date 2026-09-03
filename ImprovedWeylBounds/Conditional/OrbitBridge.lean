import ImprovedWeylBounds.CollisionApproximation
import ImprovedWeylBounds.AllCuts
import ImprovedWeylBounds.Conditional.NewInverse

/-!
# From an orbit collision to the preliminary denominator

This file gives the exact interface still required from the maximal-moment and
anisotropic-sampling argument.  Unlike an axiom, `OrbitCollisionPrinciple` is
only a proposition: downstream theorems receive a proof of it as an explicit
argument.  All algebra from that proposition to the preliminary simultaneous
approximation is proved here.
-/

namespace ImprovedWeylBounds
namespace Conditional

/-- A degree-dependent radius small enough for both conjugation of a collision
and the adjugate/triangular extraction step. -/
noncomputable def safeCollisionRadius (k : ℕ) : ℝ :=
  1 /
    ((4 * (k : ℝ) ^ 4) *
      (triangularExtractionConstant k * translationConjugationConstant k + 1))

theorem safeCollisionRadius_pos {k : ℕ} (hk : 1 ≤ k) :
    0 < safeCollisionRadius k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hc :
      0 ≤ triangularExtractionConstant k * translationConjugationConstant k :=
    mul_nonneg (triangularExtractionConstant_nonneg k)
      (translationConjugationConstant_nonneg k)
  rw [safeCollisionRadius]
  positivity

theorem safeCollisionRadius_small {k : ℕ} (hk : 1 ≤ k) :
    triangularExtractionConstant k *
        (translationConjugationConstant k * safeCollisionRadius k) ≤
      1 / (4 * (k : ℝ) ^ 4) := by
  let c : ℝ :=
    triangularExtractionConstant k * translationConjugationConstant k
  let u : ℝ := 4 * (k : ℝ) ^ 4
  have hkR : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hu : 0 < u := by
    dsimp [u]
    positivity
  have hc : 0 ≤ c := by
    dsimp [c]
    exact mul_nonneg (triangularExtractionConstant_nonneg k)
      (translationConjugationConstant_nonneg k)
  have hc1 : 0 < c + 1 := by linarith
  have hden : 0 < u * (c + 1) := mul_pos hu hc1
  rw [safeCollisionRadius, ← mul_assoc]
  change c * (1 / (u * (c + 1))) ≤ 1 / u
  have hcross : c * u ≤ 1 * (u * (c + 1)) := by
    nlinarith [hu]
  have hdiv : c / (u * (c + 1)) ≤ 1 / u :=
    (div_le_div_iff₀ hden hu).2 hcross
  simpa [div_eq_mul_inv] using hdiv

/-- Exact content needed from Lemma 5.1 plus Proposition 5.2.

The location hypothesis repairs the omission in the displayed statement of
Lemma 5.1.  The disjunction records the forward and reflected alternatives,
and the short-block inequality is the precise form consumed by Lemma 5.4.
-/
def OrbitCollisionPrinciple (k : ℕ) : Prop :=
  ∀ thresholdMargin : ℝ, 0 < thresholdMargin →
    ∀ delta : ℝ, 0 < delta →
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ (N : ℕ), N₀ ≤ N →
        ∀ (alpha : CoefficientVector k) (A : ℝ),
          0 < A → A ≤ ‖g alpha N‖ →
          Real.rpow (N : ℝ)
              (1 - 1 / (K k : ℝ) + thresholdMargin) < A →
          ∃ x y : ℤ,
            x ≠ y ∧
            ((0 ≤ x ∧ x ≤ (N : ℤ) + 1) ∧
              (0 ≤ y ∧ y ≤ (N : ℤ) + 1)) ∧
            k.factorial * (x - y).natAbs ≤ N ∧
            ((∀ r : Fin (k - 1),
                distToInt (centreDifference alpha x y r) <
                  delta * ((N : ℝ)⁻¹) ^ (r.1 + 1)) ∨
              (∀ r : Fin (k - 1),
                distToInt (reflectedCentreDifference alpha x y r) <
                  delta * ((N : ℝ)⁻¹) ^ (r.1 + 1)))

/-- The exact remaining content of Proposition 5.2 after Lemma 5.1 has been
proved.  It asks for a collision in either concrete cluster returned by
`AllCuts.allCuts_clustered`; cardinality, location, short diameter and the
large partial sums are fields of those cluster structures rather than hidden
hypotheses. -/
def ClusterCollisionPrinciple (k : ℕ) : Prop :=
  ∀ thresholdMargin : ℝ, 0 < thresholdMargin →
    ∀ delta : ℝ, 0 < delta →
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ (N : ℕ), N₀ ≤ N →
        ∀ alpha : CoefficientVector k,
          Real.rpow (N : ℝ)
              (1 - 1 / (K k : ℝ) + thresholdMargin) < ‖g alpha N‖ →
          (∀ cluster : AllCuts.ForwardCluster k N alpha,
              ∃ x ∈ cluster.X, ∃ y ∈ cluster.X, x ≠ y ∧
                ∀ r : Fin (k - 1),
                  distToInt
                      (centreDifference alpha (x.1 : ℤ) (y.1 : ℤ) r) <
                    delta * ((N : ℝ)⁻¹) ^ (r.1 + 1)) ∧
          (∀ cluster : AllCuts.BackwardCluster k N alpha,
              ∃ x ∈ cluster.X, ∃ y ∈ cluster.X, x ≠ y ∧
                ∀ r : Fin (k - 1),
                  distToInt
                      (reflectedCentreDifference alpha (x.1 : ℤ) (y.1 : ℤ) r) <
                    delta * ((N : ℝ)⁻¹) ^ (r.1 + 1))

private theorem cluster_shortBlock
    {k N : ℕ} {X : Finset (Fin (N + 2))} {x y : Fin (N + 2)}
    (hx : x ∈ X) (hy : y ∈ X)
    (hshort : ∀ u ∈ X, ∀ v ∈ X,
      2 * k.factorial * Nat.dist u.1 v.1 ≤ N) :
    k.factorial * (((x.1 : ℤ) - (y.1 : ℤ)).natAbs) ≤ N := by
  rw [AllCuts.natAbs_intCast_sub_eq_natDist]
  calc
    k.factorial * Nat.dist x.1 y.1 ≤
        2 * (k.factorial * Nat.dist x.1 y.1) :=
      Nat.le_mul_of_pos_left _ (by norm_num)
    _ = 2 * k.factorial * Nat.dist x.1 y.1 := by ring
    _ ≤ N := hshort x hx y hy

/-- Lemma 5.1 and the collision proposition, in its cluster-level form,
produce the orbit interface consumed below. -/
theorem orbitCollisionPrinciple_of_clusterCollision
    {k : ℕ} (hCluster : ClusterCollisionPrinciple k) :
    OrbitCollisionPrinciple k := by
  intro thresholdMargin hmargin delta hdelta
  obtain ⟨N₀, hN₀, hcollision⟩ :=
    hCluster thresholdMargin hmargin delta hdelta
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN alpha A hA hAg hthreshold
  have hthresholdNorm :
      Real.rpow (N : ℝ)
          (1 - 1 / (K k : ℝ) + thresholdMargin) < ‖g alpha N‖ :=
    hthreshold.trans_le hAg
  have hNpos : 0 < N := by omega
  have hnormPos : 0 < ‖g alpha N‖ :=
    (Real.rpow_pos_of_pos (by exact_mod_cast hNpos : (0 : ℝ) < N) _).trans
      hthresholdNorm
  obtain hforward | hbackward :=
    AllCuts.allCuts_clustered (by omega : 1 ≤ N) alpha hnormPos
  · obtain ⟨cluster⟩ := hforward
    obtain ⟨x, hx, y, hy, hxy, hclose⟩ :=
      (hcollision N hN alpha hthresholdNorm).1 cluster
    have hxyInt : (x.1 : ℤ) ≠ (y.1 : ℤ) := by
      intro hval
      apply hxy
      apply Fin.ext
      exact_mod_cast hval
    exact ⟨(x.1 : ℤ), (y.1 : ℤ), hxyInt,
      ⟨cluster.location x hx, cluster.location y hy⟩,
      cluster_shortBlock hx hy cluster.short, Or.inl hclose⟩
  · obtain ⟨cluster⟩ := hbackward
    obtain ⟨x, hx, y, hy, hxy, hclose⟩ :=
      (hcollision N hN alpha hthresholdNorm).2 cluster
    have hxyInt : (x.1 : ℤ) ≠ (y.1 : ℤ) := by
      intro hval
      apply hxy
      apply Fin.ext
      exact_mod_cast hval
    exact ⟨(x.1 : ℤ), (y.1 : ℤ), hxyInt,
      ⟨cluster.location x hx, cluster.location y hy⟩,
      cluster_shortBlock hx hy cluster.short, Or.inr hclose⟩

/-- Lemma 5.4 closes the entire gap between an orbit collision and the
preliminary common denominator required by Baker compression. -/
theorem preliminaryApproximationPrinciple_of_orbitCollision
    {k : ℕ} (hk : 3 ≤ k) (hOrbit : OrbitCollisionPrinciple k) :
    PreliminaryApproximationPrinciple k := by
  intro thresholdMargin hmargin
  let delta := safeCollisionRadius k
  have hdelta : 0 < delta := safeCollisionRadius_pos (by omega : 1 ≤ k)
  obtain ⟨N₀, hN₀, hcollision⟩ :=
    hOrbit thresholdMargin hmargin delta hdelta
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN alpha A hA hAg hthreshold
  obtain ⟨x, y, hxy, hlocation, hshort, hforward | hreflected⟩ :=
    hcollision N hN alpha A hA hAg hthreshold
  · obtain ⟨pre, hpre⟩ :=
      collision_to_preliminaryApproximation hk (hN₀.trans hN |>.trans' (by omega))
        alpha x y hxy hdelta.le hlocation hshort
        (fun r => (hforward r).le)
        (by simpa only [delta] using
          safeCollisionRadius_small (by omega : 1 ≤ k))
    exact ⟨pre, hpre⟩
  · obtain ⟨pre, hpre⟩ :=
      reflected_collision_to_preliminaryApproximation hk
        (hN₀.trans hN |>.trans' (by omega)) alpha x y hxy hdelta.le
        hlocation hshort (fun r => (hreflected r).le)
        (by simpa only [delta] using
          safeCollisionRadius_small (by omega : 1 ≤ k))
    exact ⟨pre, hpre⟩

end Conditional
end ImprovedWeylBounds
