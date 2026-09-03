import ImprovedWeylBounds.External.Statements

/-!
# External claims that are not yet callable

The items below are metadata, not assumptions.  In particular, this module
does not turn an informal transfer argument into an axiom.
-/

namespace ImprovedWeylBounds.External

/-- Documentation for an external-boundary claim which still lacks a precise,
source-backed theorem interface. -/
structure UnresolvedItem where
  title : String
  paperLocation : String
  source : String
  obstruction : String
  requiredWork : String
deriving Repr, DecidableEq

/-- `main.tex`, lines 1376--1409: the proposed replacement of Baker's
denominator parameter by `Δₖ` in the prime-argument Harman-sieve theorem.

Baker's published theorem fixes its own function `J(f)`; it does not state a
theorem parameterized by an arbitrary inverse-theorem oracle or denominator
parameter.  Consequently the proposed replacement is a new internal transfer
argument, not a quotable external theorem.
-/
def primeHarmanTransfer : UnresolvedItem where
  title := "Parameterized Baker--Harman sieve transfer"
  paperLocation := "main.tex:1376-1409"
  source := "https://arxiv.org/html/1606.05779v2"
  obstruction :=
    "Baker 2017, Theorem 1, is stated only for the source-defined J(f); " ++
      "no cited theorem permits arbitrary replacement of J."
  requiredWork :=
    "Formalize the interval inverse theorem and recheck the complete-sum, " ++
      "Type I, Type II, Buchstab, and final Harman-sieve arguments with J = Delta k."

/-- `main.tex`, lines 1423--1436: informal propagation to maximal operators,
Hausdorff-dimension bounds, and local mean values.

The manuscript supplies neither the resulting formulas nor all parameter
ranges, so there is presently no mathematical proposition to expose as an
external interface.
-/
def sectionNinePropagation : UnresolvedItem where
  title := "Section 9 threshold propagation"
  paperLocation := "main.tex:1423-1436"
  source :=
    "Baker--Chen--Shparlinski 2024; Baker--Chen--Shparlinski 2022; " ++
      "Brandes--Chen--Shparlinski 2024"
  obstruction :=
    "The text says that ranges improve but omits the resulting theorem statements, " ++
      "formulas, and complete parameter hypotheses."
  requiredWork :=
    "Choose each intended downstream theorem, restate it completely in the cited " ++
      "paper's notation, and verify every use of the old inverse threshold."

/-- The complete list of deliberately unresolved external-boundary items. -/
def unresolvedItems : List UnresolvedItem :=
  [primeHarmanTransfer, sectionNinePropagation]

end ImprovedWeylBounds.External
