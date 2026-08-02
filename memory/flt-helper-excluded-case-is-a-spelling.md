---
name: flt-helper-excluded-case-is-a-spelling
description: "A helper lemma's excluded case is often an artefact of the expression shape it was stated in for its first consumer, not a fact about the mathematics — generalise the helper before believing a docstring that blames it."
metadata: 
  node_type: memory
  type: project
  originSessionId: 909ccc01-9e79-47df-b328-28b95516b3f1
  modified: 2026-08-02T13:14:23.827Z
---

(2026-08-02, `flt-lean-75`, closing `exists_wronskianPoly_scalar_charTwo_supersingular`,
the last leaf of `Fermat/FLT/EllipticCurve/DifferentialCharacter.lean`.)

That leaf's docstring named two remaining places and said "a prover should be sent at
those and nothing else". One of the two was not an obstruction at all. It blamed
`charTwo_AS_rootMultiplicity`'s `S(b) ≠ 0` hypothesis — correctly quoting that lemma's own
docstring — for making the root of `S` hard. But that lemma is stated in the exact
syntactic shape of its first consumer's expression, `N = Cx²f + D² + Cx·D·S`, so its
additive coefficient is `Cx·S` and `S(b) ≠ 0` is only what buys `ord_b(Cx·S) = ord_b Cx`.
In the new setting `hone` gives `Cx·S = a₃′·E`, so the same `N` has coefficient `a₃′·E`,
whose order never involves `S`. Restating the step over an ARBITRARY additive coefficient
(`N = Q + (D² + c·D)`, hypotheses `ord N < ord Q` and `ord N < 2 ord c`) is the same
twenty-line proof and the excluded place disappears.

**Why:** helpers in this tree are written to be cheap to apply at their first call site,
which means stating them in that call site's algebra — and that bakes the call site's
incidental facts into their hypotheses. A docstring that blames such a hypothesis is
quoting the helper, not the problem.

**How to apply:** when a route note says "lemma `L` does not apply here, so this case needs
new mathematics", read `L`'s PROOF and ask whether the hypothesis does mathematical work or
only establishes an inequality your setting supplies another way. If the latter, restate
`L` with the inequality as the hypothesis and the case evaporates. Related:
[[audit-lacks-x-is-about-x]], [[flt-route-residue-is-the-cheap-route]],
[[flt-leaf-cost-estimates-are-hypotheses]].

**The payoff that made it worth doing:** with the generalised step, `hparB` — the whole
output of the sibling theorem `charTwo_rootMultiplicity_B_even` — became UNUSED, because
the parity it supplies is a conclusion of the generalised step rather than an input.
Lean's unused-variable linter says so for free the moment the proof closes. Keep the binder
(underscored) rather than moving the call site; see [[flt-complementary-structure-fields-split]]
for why a signature change plus its call site is the expensive shape.
