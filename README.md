# Improved Weyl bounds on short intervals: a conditional Lean 4 formalization

This repository contains a conditional Lean 4 formalization accompanying the
paper *Improved Weyl bounds on short intervals*. The manuscript itself is not
distributed in this repository.

> [!IMPORTANT]
> **Formalization status.** Under five explicitly stated external analytic-
> number-theory hypotheses, Lean kernel-checks the internal proof chain leading
> to the main results and the three corollaries in Section 7. These five
> hypotheses are propositions, not custom Lean axioms. The repository does not
> reprove them from first principles and does not claim to formalize the entire
> paper.
>
> **Explicitly outside the current formalization:** (1) the Harman-sieve
> transfer from the new inverse theorem to the prime Weyl-sum conclusion in
> Theorem 1.5; and (2) the propagation claims in Section 9 concerning maximal
> operators, Hausdorff-dimension bounds, and local mean values. Their entries
> in `External/Unresolved.lean` are audit metadata values, not propositions,
> theorems, assumptions, or axioms.

## Building and entry points

The project pins Lean and mathlib to `v4.32.1`. With `elan` installed, run:

```text
lake build
```

- Top-level import: `ImprovedWeylBounds.lean`
- End-to-end assembly: `ImprovedWeylBounds/Conditional/Complete.lean`
- External proposition interfaces: `ImprovedWeylBounds/External/Statements.lean`
- Unresolved-item metadata: `ImprovedWeylBounds/External/Unresolved.lean`
- Detailed audit: `MANUSCRIPT_AUDIT.md`

## Conditionally assembled paper results

`Conditional/Complete.lean` contains the final theorems whose only remaining
mathematical assumptions are the genuinely external inputs listed below.

| Paper result | Lean theorem | External inputs |
|---|---|---|
| Proposition 5.2 | `clusterCollisionPrinciple_of_external` | `CriticalVMVT` |
| Theorem 1.3 | `inversePrinciple_of_external_inputs` | `CriticalVMVT`, `BakerCompression` |
| Corollary 1.4 | `combinedInverse_of_external_inputs` | `CriticalVMVT`, `BakerCompression`, `ClassicalInverse` |
| Theorem 1.1 | `rationalShortIntervalBoundAll_of_external_inputs` | `CriticalVMVT`, `BakerCompression`, `ClassicalInverse` |
| Corollary 1.2 | `finiteFieldShortIntervalBoundAll_of_external_inputs` | `CriticalVMVT`, `BakerCompression`, `ClassicalInverse` |
| Theorem 1.4 | `smallFractionalPartsAll_of_external_inputs` | `CriticalVMVT`, `BakerCompression`, `ClassicalInverse`, `LargeMultiple` |
| Corollary 7.1 | `finiteFieldDiscrepancyCorollary_of_external_inputs` | `CriticalVMVT`, `BakerCompression`, `ClassicalInverse`, `ErdosTuran` |
| Corollary 7.2 | `finiteFieldGapCorollary_of_external_inputs` | `CriticalVMVT`, `BakerCompression`, `ClassicalInverse`, `ErdosTuran` |
| Corollary 7.3 | `finiteFieldAdditiveBasisCorollary_of_external_inputs` | `CriticalVMVT`, `BakerCompression`, `ClassicalInverse` |

The final versions of Theorem 1.1, Corollary 1.2, and Theorem 1.4 absorb the
finite initial range into one uniform constant using trivial bounds. They are
therefore stated for every positive interval length, every `1 <= H <= p`, and
every `N >= 1`, respectively. The Section 7 corollaries use a finite-field
bound available for every positive loss parameter because their proofs choose
a smaller auxiliary loss internally.

## Kernel-checked internal developments

- Polynomial translation and reflection, coefficient formulas, and Weyl-sum
  identities;
- the critical VMVT reduction to fixed-leading-coefficient fibre moments and
  then to dyadic maximal moments weighted by the actual block lengths;
- an explicit reproducing kernel, Fourier support, tensor convolution, and
  anisotropic sampling;
- all cut classifications in Lemma 5.1, including set location, cardinality,
  and diameter bounds;
- the forward and reverse translation orbits in Proposition 5.2, the
  separation contradiction, collision, and constant absorption;
- the triangular matrix in Lemma 5.3, `det A_h = k!`, and coordinatewise error
  propagation;
- the conversion in Lemma 5.4 from forward and reverse collisions to a common
  denominator approximation, including greatest-common-divisor reduction;
- all parameter choices for Baker compression and the merger of the new and
  classical inverse theorems;
- the rational-leading-coefficient bound, canonical lifts over prime fields,
  and standard additive-character identities;
- Erdos--Turan truncation, cyclic-interval decomposition, Fourier inversion for
  representation counts, and the positivity criterion; and
- large-multiple selection, coefficient-error propagation under `n = qm`, and
  the small-fractional-parts conclusion.

## Exact trust boundary

There are five external proposition interfaces: `CriticalVMVT`,
`BakerCompression`, `ClassicalInverse`, `ErdosTuran`, and `LargeMultiple`.
Each appears as an explicit theorem parameter, not as a Lean `axiom`.

The formalization makes three faithful specializations of generality unused by
the main proof:

1. Only the critical moment `s = r(r+1)/2` of the VMVT is stated and used; the
   general noncritical theorem is outside the scope of this project.
2. The manuscript states its sampling proposition for every real `p >= 1`.
   This project proves the positive-even case and derives the required case
   `p = K(k) = k(k-1)`. This exponent is always positive and even, so it covers
   every invocation in the manuscript.
3. The manuscript's kernel lemma permits every decay order `M >= 2`. The Lean
   development uses an explicit kernel with quadratic decay, which is summable
   in one dimension, tensorizes, and suffices for the sampling proof.

See `MANUSCRIPT_AUDIT.md` for the quantified interfaces, source checks,
formalization-driven repairs, and qualifications on the cited results.

## Two parts not yet formalized

### Theorem 1.5: Harman-sieve transfer to primes

Theorem 1.5 is not formalized. The repository conditionally derives the new
inverse theorem and proves several relevant parameter inequalities, including
`Delta k >= k + 1` and two Type I/II numerical inequalities. It does not verify
the transfer to the prime Weyl-sum conclusion. Baker's published theorem and
its Lemma 5 are stated for the source-defined `J(f)`, not for an arbitrary
inverse-theorem parameter. Replacing `J(f)` by `Delta k` therefore requires a
fresh verification of the interval/multiple form of Lemma 5, the complete-sum
estimates, the Type I and Type II estimates, the Buchstab decomposition, and
the final Harman-sieve argument.

`primeHarmanTransfer` is an `UnresolvedItem` value recording this obstruction
and the work still required. It is not a mathematical proposition or proof
assumption. Consequently, this repository does not claim a kernel-checked
proof of Theorem 1.5.

### Section 9: propagation claims

Section 9 is not formalized. The manuscript gives qualitative propagation
statements but does not state the resulting theorems with complete formulas,
quantifiers, and parameter ranges. Consequently, the repository neither
states nor assumes the proposed maximal-operator, Hausdorff-dimension, or
local-mean-value conclusions as Lean propositions.

This should not be confused with the proved theorem
`maximalFixedLeadingFibre_criticalVMVT`, which is a finite-prefix maximal-moment
estimate on a fixed-leading-coefficient fibre from the Section 4 proof chain,
not one of the maximal-operator norm results discussed in Section 9.

`sectionNinePropagation` is likewise only `UnresolvedItem` audit data. Turning
Section 9 into a callable formal interface requires complete definitions,
statements, and parameter ranges for each target result, followed by a check of
every place where the original proofs use the old threshold.

No theorem in this project contains `sorry` or `admit`, and the project
declares no custom `axiom` or `opaque` constant.
