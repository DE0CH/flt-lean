---
name: flt-route-bullet-hides-missing-hypothesis
description: "A leaf's own prescribed route can silently use the hypothesis the leaf is missing — read the route as claims and check each step's binders."
metadata: 
  node_type: memory
  type: project
  originSessionId: 0bd08c16-9ea8-41af-b780-33927fef4597
  modified: 2026-08-02T15:12:10.608Z
---

A mature flt-lean leaf carries a ROUTE ("the three data lift one at a time; only
one is obstructed"). It reads as reassurance that the leaf is attackable. Read it
instead as a LIST OF CLAIMS and check each step's hypotheses against the leaf's own
binder list: **a step the route states as obvious is exactly where a missing
hypothesis hides**, because the author was thinking of the intended application
where it holds for free.

2026-08-02, `exists_tameLocalLift_of_isSmallExtension` (item (5)(d),
`HardlyRamified/Deformation.lean`): the route said the tame character `δ` "satisfies
`δ² = 1` … so is determined by `δ(Frob) ∈ {±1}`". That step is valid only when `2` is
a unit — otherwise `δ(Frob)` is merely SOME square root of `1`. The leaf was refuted
by its own sketch, in four lines of prose, with no witness hunt.

**Witness pattern**: when a leaf asserts a lift of an object satisfying a POLYNOMIAL
equation (`x² = 1`, `x² = x`, `xⁿ = 1`), try `ZMod p^k ↠ ZMod p^(k-1)` first. Here
`ZMod 16 ↠ ZMod 8` is a small extension and `3` squares to `1` mod `8` while lifting
to no square root of `1` mod `16`. Three `decide`s.

**Cheapest oracle for WHICH hypothesis is missing: diff the binder lists of the
SIBLING CLAUSES cut from the same audit item.** Clause (5a) carried
`(h2 : IsUnit (2 : S))` saying "where `hℓOdd` enters, and it is the only place it
does"; (5d) is the same shape and did not. One `grep` for `IsUnit (2` found both the
hypothesis and its call-site discharge. Sharper scope than the standing
[[flt-decomposition-drops-a-hypothesis]] rule — clauses of ONE audit item, written
independently on the same day.

**Test for whether peeling a route bullet is a real cut: is the peeled statement
about the leaf's INPUT or its OUTPUT?** Only INPUT reduces. Pinning `δ` to `±1` is
about `ρ2` (input) and reduces; handing in a lifted `p̃`/`δ̃` is about the output and
does not, since the content is that they are chosen COMPATIBLY with the lift.

**Why:** a route is written before anyone tries, from the application, so its steps
inherit the application's ambient hypotheses silently.

**How to apply:** before proving or refuting, walk the route bullet by bullet and
check each against the binder list; then diff siblings. Record any second axis you
checked and could not settle on the declaration rather than shipping an unjustified
hypothesis. See also [[flt-leaf-cost-estimates-are-hypotheses]],
[[flt-audit-misattributes-the-hypothesis]].
