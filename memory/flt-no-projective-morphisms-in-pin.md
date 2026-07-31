---
name: flt-no-projective-morphisms-in-pin
description: The mathlib pin has no projective/ample morphisms and no quotient of a scheme by a group action, so "orbits lie in an affine open" is a chapter, not a lemma
metadata:
  type: project
---

Measured 2026-07-31 while auditing `exists_isNIsogenyPair` (`X0.lean`): the pin
has **no relative projectivity and no relative ampleness at all** — there is no
`Mathlib/AlgebraicGeometry/Morphisms/Projective.lean`, and
`Mathlib/AlgebraicGeometry/Group/` still contains exactly two files
(`Abelian.lean`, `Smooth.lean`). There is also no quotient of a scheme by a
group action anywhere in the pin, and no Cartier theorem for group schemes.

**Why:** any construction whose classical proof says "the orbit is finite, and a
finite subset of a quasi-projective scheme lies in an affine open" is priced as
a LEMMA by the audit and is actually a CHAPTER here — the quasi-projectivity is
the missing input, not the gluing. This is the ingredient that gets dropped from
cost estimates, because textbooks never state it.

**How to apply:** before costing a leaf that needs a quotient, a linear system, a
Riemann-Roch on a relative curve, or "choose an affine open containing these
points", check for the ample/projective input FIRST — it decides the estimate on
its own. What DOES exist, and is the only quotient nucleus in the tree, is
`Fermat/FLT/Mathlib/AlgebraicGeometry/InvariantQuotient.lean` (`Spec` of a ring
of invariants is a categorical quotient in the category of ALL schemes, for a
finite *constant* group acting by ring automorphisms) plus its flat base change
`Fermat/FLT/Mathlib/RingTheory/InvariantBaseChange.lean`; both are already
imported by `X0.lean`. The pin's fpqc material (`Morphisms/FlatDescent.lean`,
`Morphisms/Descent.lean`, the `EffectiveEpi` instance for quasi-compact flat
surjections) descends MORPHISMS and morphism PROPERTIES only — descent of
OBJECTS is absent, and `Sites/Representability.lean` is Zariski-local
representability, which is gluing rather than descent.

Related: [[flt-inventory-audits-understate-what-exists]],
[[audit-searched-production-not-invariant]],
[[flt-leaf-cost-estimates-are-hypotheses]].
