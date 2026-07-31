---
name: theorem-absent-from-pin-may-be-present-in-another-formulation
description: A correct "Mathlib does not have X" audit hides that THIS TREE already proves X in a different formulation; grep the docstrings for the INFORMAL STATEMENT, not for identifiers
metadata:
  type: feedback
---

An audit that says "`Mathlib` at this pin has no degree of a divisor and no degree of a
principal divisor, in any capitalisation" can be **entirely correct and still send you to
build something this tree already has**. On 2026-07-31 a whole module was commissioned for
`deg (div g) = 0` on a smooth proper curve — and
`Fermat/FLT/ModularCurve/HyperellipticJacobian.lean` already carried
`PlaceData.degOf_divisor_eq_zero`, **PROVEN**, resting on the single leaf
`degOf_poleDivisor_eq_finrank_of_transcendental` (Stichtenoth I.4.11), with all the
surrounding bookkeeping (`div = div_0 − div_∞`, `div_0 g = div_∞ g⁻¹`, `K(g) = K(g⁻¹)`,
the constant case) already Lean.

**Why every name search missed it: it is stated in a DIFFERENT FORMULATION.** That file
works over an abstract `PlaceSystem`/`PlaceData` interface — `ord : Places → F → ℤ` on the
places of a function field — so it shares not one identifier with a scheme-theoretic
search (`Scheme.ord`, `AlgebraicCycle`, `divisor`, `degree`). Identifier greps cannot
cross a change of formulation, and the correct pin-side absence claim is exactly what
stops you looking further.

**How to find it, and it costs one command: grep for the INFORMAL STATEMENT.** This
development states its mathematics in prose in docstrings, and prose survives a change of
formulation where names do not:

    grep -rn 'deg (div g) = 0' --include=*.lean Fermat/     # finds it instantly

Also grep the CITATION — an author, a theorem number, a classical name (`Stichtenoth`,
`I.4.11`, `Riemann–Roch`, `weak approximation`) — because a leaf that is a named classical
theorem is nearly always cited by name in whatever formulation carries it.

**Why:** two formulations of one theorem mean two open leaves where there is one open
node, and whoever closes one does not close the other. Worse, the second prover is
invisible to `own.py` and `leafstat.py`, which are declaration-name based.

**How to apply:** before building machinery for a named classical theorem, run the prose
grep and the citation grep over `Fermat/` in addition to the identifier grep. If the
theorem IS present in another formulation, the deliverable changes from "prove it" to
"build the bridge", and the two formulations should be cut so they bottom out at the SAME
single leaf — which is what `Fermat/FLT/Mathlib/AlgebraicGeometry/PrincipalDivisorDegree.lean`
was restructured to do (`poleDegree_inv_eq_poleDegree`, deliberately the same
`deg (g)_0 = deg (g)_∞` seam that `degOf_divisor_eq_zero` uses).

Related: [[flt-missing-machinery-may-be-downstream]] (same failure, milder cause: the
theorem is in a file that IMPORTS yours, so an identifier grep of the tree DOES find it);
[[flt-inventory-audits-understate-what-exists]]; [[audit-searched-production-not-invariant]].
