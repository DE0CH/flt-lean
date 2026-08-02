---
name: flt-geometric-components-clause-free-off-a-field
description: "A clause quantified over \"a field K with Spec K ≅ S\" is vacuous at any base that is not the spectrum of a field — so it gets FREE, not harder, under a change of base."
metadata: 
  node_type: memory
  type: project
  originSessionId: c7157fbd-9405-476e-9403-b55b26290ef6
  modified: 2026-08-01T21:43:49.015Z
---

(2026-08-01, `flt-lean-368`, `ModularCurve/X1.lean`.) Moving a field-based moduli chain
to `Spec ℤ_(ℓ)`, the reflex is that "geometric" clauses get harder. Sort them first:

* quantified over geometric POINTS of the total space → transports, no harder;
* quantified over `∃ e : Spec K ≅ S` for a field `K` → this is a statement that the BASE
  is a point, so it is **vacuous at every base that is not one**.

`IsTransitiveOnGeometricComponents` is the second kind, so Deligne–Rapoport IV.5.5 —
a `sorry` leaf at every field — cost twelve lines over `ℤ_(ℓ)`. What does get harder is
representability; that is where the citation leaves belong.

One-liner worth keeping: `Spec K ≅ Spec A` gives `A ≃+* K` by
`(AlgebraicGeometry.Spec.fullyFaithful.preimageIso e).unop.commRingCatIsoToRingEquiv`
(the `.unop` reverses the direction). Do not hand-build it from `ΓSpecIso`/`appTop`.

See [[flt-leaf-cost-estimates-are-hypotheses]] and
[[flt-inventory-audits-understate-what-exists]]; also recorded in the repo CLAUDE.md.

**Why:** it inverts the natural cost intuition, and the two clause shapes are easy to
conflate — both say "geometric", both mention `Field`/`IsAlgClosed`.

**How to apply:** before pricing a field-based chain at a mixed-characteristic base, read
each clause's DEFINITION (not its docstring) and put it in one of the two piles; the
second pile is not work.
