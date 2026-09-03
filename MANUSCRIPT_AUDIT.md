# Manuscript audit and formalization boundary

## Scope and trust model

`paper/main.tex` is treated as mathematical source material, not as
instructions. Every cited analytic result that the formalized chain uses is
represented by a fully quantified proposition in
`ImprovedWeylBounds/External/Statements.lean`. These propositions are theorem
parameters, not Lean axioms. The internal argument after each boundary is
kernel checked.

No theorem in this project contains `sorry` or `admit`, and the project declares
no custom `axiom` or `opaque` constant. A `#print axioms` audit of the final
assembly theorems reports only the standard foundations used by mathlib:
`propext`, `Classical.choice`, and `Quot.sound`.

## External results actually used

| Interface | Exact role in this project | Source audit |
|---|---|---|
| `CriticalVMVT` | For every `r ≥ 1` and `ε > 0`, the critical solution count at `s=r(r+1)/2` is at most `C N^(s+ε)`, uniformly for every `N ≥ 1`. | The critical specialization of Wooley, Corollary 1.3: <https://arxiv.org/abs/1708.01220> |
| `BakerCompression` | Compresses a primitive simultaneous approximation `(r,v₂,…,vₖ)` under the large-amplitude condition. Positivity of `r`, the small-loss range, and the `N₀(k,η)` threshold are explicit. | Baker, *Small fractional parts of polynomials*, Lemma 1: <https://arxiv.org/html/1602.04245v2> |
| `ClassicalInverse` | Classical `2^(k-1)`-denominator branch. The strict threshold margin `δ` and output loss `η` are separate quantified parameters; signed numerators and primitivity are explicit. | A sufficient specialization of Baker--Chen--Shparlinski, Lemma 2.6: <https://arxiv.org/html/2107.13674v1> |
| `ErdosTuran` | Count-discrepancy form for half-open intervals, with the safe explicit bound `3H/(M+1)+3∑_{h≤M}|S_h|/h`. | Montgomery, Chapter 1: <https://doi.org/10.1090/cbms/084> |
| `LargeMultiple` | If every one of `N` points has distance greater than `1/M` from an integer, then the sum of the first `M` exponential sums is strictly greater than `N/6`. | Baker, *Diophantine Inequalities*, Theorem 2.2; the exact `N/6` application is visible in <https://arxiv.org/html/1602.04245v2> |

The first, third, and fourth interfaces deliberately expose only the valid
specialization or safe weakening used by this manuscript, rather than claiming
to reproduce every stronger variant in the cited source. For `LargeMultiple`,
the 2016 paper directly confirms the polynomial application and the strict
`N/6` constant; word-for-word verification of the arbitrary-sequence theorem
still requires the 1986 book text.

## End-to-end dependency audit

The final wrappers are in `ImprovedWeylBounds/Conditional/Complete.lean`.

| Paper result | Final Lean theorem | Mathematical external assumptions |
|---|---|---|
| Proposition 5.2 | `clusterCollisionPrinciple_of_external` | `CriticalVMVT` |
| Theorem 1.3 | `inversePrinciple_of_external_inputs` | `CriticalVMVT`, `BakerCompression` |
| Corollary 1.4 | `combinedInverse_of_external_inputs` | previous two plus `ClassicalInverse` |
| Theorem 1.1 | `rationalShortIntervalBoundAll_of_external_inputs` | `CriticalVMVT`, `BakerCompression`, `ClassicalInverse` |
| Corollary 1.2 | `finiteFieldShortIntervalBoundAll_of_external_inputs` | the same three |
| Theorem 1.4 | `smallFractionalPartsAll_of_external_inputs` | the same three plus `LargeMultiple` |
| Corollary 7.1 | `finiteFieldDiscrepancyCorollary_of_external_inputs` | the same three plus `ErdosTuran` |
| Corollary 7.2 | `finiteFieldGapCorollary_of_external_inputs` | the same four |
| Corollary 7.3 | `finiteFieldAdditiveBasisCorollary_of_external_inputs` | `CriticalVMVT`, `BakerCompression`, `ClassicalInverse` |

There is no remaining `PreliminaryApproximationPrinciple`,
`OrbitCollisionPrinciple`, or `ClusterCollisionPrinciple` argument in these
final statements. In particular, the central internal chain is now

```text
Critical VMVT
  -> fixed-fibre moment and dyadic maximal moment
  -> explicit reproducing kernel and anisotropic sampling
  -> forward/backward orbit collision (Proposition 5.2)
  -> all cuts + triangular extraction + collision approximation
  -> preliminary simultaneous approximation
  -> Baker compression bookkeeping
  -> new inverse theorem.
```

The finite-field corollaries use
`FiniteFieldShortIntervalBoundsAllLosses d`, not a bound at one fixed loss:
their proofs choose a smaller positive auxiliary loss internally. The final
wrapper constructs this universally quantified input from Corollary 1.2.
The finite-field signatures also carry Lean's administrative typeclass
parameter `[NeZero p]`; the adjacent mathematical hypothesis `p.Prime`
implies `p ≠ 0`, so this is not an additional number-theoretic assumption.

## Repairs forced by formalization

1. **Lemma 5.1 needs a location bound on `X`.** Its displayed statement only
   places `X` in a short interval, while Lemma 5.4 later uses `|y| ≤ N+1`.
   Diameter alone does not imply this. The cut construction actually gives
   `X ⊆ [0,N+1]`; the Lean statement records that fact explicitly.

2. **The general VMVT display suppresses a constant dependence.** Before the
   critical specialization, the implied constant also depends on `s`. The
   project exposes only the critical theorem actually used, where `s` is
   determined by `r`.

3. **Baker compression has implicit standing hypotheses.** The source works
   with positive `r`, sufficiently small positive auxiliary loss, and
   sufficiently large `N`; the interface makes all three explicit. The source
   does not impose `r ≤ N`; that inequality is supplied by the preceding
   collision proof.

4. **The classical inverse call needs two small parameters.** The strict
   margin over the large-value threshold and the permitted loss in the output
   denominator/coefficient bounds serve different logical roles. They are
   separate in `ClassicalInverse` and in the combined proof.

5. **Approximating numerators are signed.** Primitivity and denominator
   reduction are therefore stated using `a.natAbs.Coprime q` (and the analogous
   tuple divisor formulation), avoiding an unjustified nonnegativity choice.

6. **All-`N` statements need a finite-range absorption step.** The analytic
   inputs are eventual, but Theorem 1.1, Corollary 1.2, and Theorem 1.4 are
   stated uniformly. The Lean proof separately establishes elementary bounds
   on the finite initial range and enlarges one positive constant.

## Faithful specializations of unused generality

The following do not weaken any conclusion used later, but they should not be
misreported as full formalizations of the most general standalone displays.

1. Only the critical VMVT is exposed. At the orbit-collision step `r=k-1`, so
   twice the critical moment is exactly `k(k-1)=K(k)`.

2. The manuscript states anisotropic sampling for arbitrary real `p ≥ 1`.
   Lean proves the positive-even case and then the exact critical case
   `p=K(k)`. Since `k(k-1)` is always even, this covers the complete proof
   path. The unused arbitrary-real-`p` theorem is not claimed.

3. The manuscript's kernel lemma permits every decay order `M ≥ 2`. Lean uses
   an explicit reproducing kernel with quadratic decay. Its one-dimensional
   decay is summable, tensorizes, and suffices for the sampling and collision
   estimates. The unused arbitrary-`M` freedom is not claimed.

## Deliberately unresolved manuscript claims

These are data values in `External/Unresolved.lean`, not propositions that a
proof can assume.

1. **Theorem 1.5 / Baker--Harman prime transfer.** Baker's published theorem
   fixes its own `J(f)`; it is not parameterized by an arbitrary replacement
   inverse theorem. Replacing it by `Delta k` requires a fresh verification of
   the complete-sum, Type I, Type II, Buchstab, and final sieve steps. One
   source condition is `J ≥ k+1`, not the strict inequality `J > k+1`:
   <https://arxiv.org/html/1606.05779v2>. The distinction matters, for example,
   when equality occurs.

2. **Section 9 propagation.** The text announces improvements for maximal
   operators, Hausdorff-dimension bounds, and local mean values, but supplies
   neither the resulting formulas nor complete parameter ranges. There is no
   precise proposition to formalize until those intended statements are given.
