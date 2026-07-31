---
name: flt-decomposition-verdict-cost-list-is-a-hypothesis
description: A "deliberately NOT decomposed" verdict's list of costs is written before anyone tried; price each item against the pin before inheriting the verdict
metadata:
  type: feedback
---

A leaf docstring that says "this does not usefully split, and here are the three
things the obvious cut would cost" is recording an ESTIMATE, not a measurement.
Re-price every named cost against the pin before inheriting the verdict.

Measured on `NumberField.artinMap_toPrincipalIdeal` (Artin reciprocity at modulus
`1`, `Fermat/FLT/NumberField/ArtinSymbol.lean`) on 2026-07-31. Two successive
audits had priced the abelian→cyclic reduction at "several hundred lines" over
three costs. All three were wrong:

* **"no mathlib lemma at this pin transports `Algebra.IsUnramifiedAt` down a
  tower"** — `Algebra.IsUnramifiedAt.of_liesOver` does exactly that
  (`Mathlib/NumberTheory/RamificationInertia/Unramified.lean`). This same claim
  had been inherited verbatim from a THIRD docstring, so one unchecked absence
  claim had been steering three leaves.
* **"tower functoriality of the Artin symbol"** — 15 lines. `Ideal.under_under`
  makes the exponent the same, `AlgEquiv.restrictNormal_commutes` moves the
  action across `𝓞 M → 𝓞 L`, so the restriction satisfies the defining
  congruence; then `AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt` for uniqueness and
  faithfulness of the action on `𝓞 L` to get back into `Gal(M/K)`. That
  three-step shape — *exhibit the candidate as an `IsArithFrobAt`, invoke
  uniqueness, descend through faithfulness* — is the reusable technique.
* **"the structure theorem for finite abelian groups"** — not needed.
  `CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity` gives a character
  separating the element, and `isCyclic_subgroup_units` makes the quotient
  cyclic. (Use `AlgebraicClosure ℚ` as the target, not `ℂ`, to keep the analysis
  library out of the cone.)

Whole reduction: ~150 lines, green first try after four scratch iterations.

**Why:** the verdict and the cost list are written by whoever declined the work,
i.e. by the person who had the least reason to look the lemmas up. It reads as
settled because it is specific — naming three obstacles is what makes it
convincing — and specificity is exactly what makes it checkable.

**How to apply:** for each named cost, run one `grep` over the pin and one
15-minute scratch before accepting it. Keep the verdict's MATHEMATICAL claim
(here: "the cyclic case is where every classical treatment spends its effort" —
true, and the reduction removes no mathematics) separate from its COST claim; the
first can be right while the second is off by an order of magnitude, and only the
second decides whether to do the work. See [[flt-leaf-cost-estimates-are-hypotheses]]
and [[audit-searched-production-not-invariant]].
