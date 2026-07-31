---
name: proper-global-sections-are-integral
description: The pin proves Γ(X,⊤) is integral over K for X universally closed over Spec K — use it instead of building an extension morphism and running a fibre dichotomy
metadata:
  type: reference
---

`Mathlib/AlgebraicGeometry/Morphisms/Proper.lean` has three lemmas that almost
nothing in this development was using, all about GLOBAL SECTIONS of a
universally closed scheme:

- `isIntegral_appTop_of_universallyClosed (f : X ⟶ Y) [UniversallyClosed f]
  [IsAffine Y] : f.appTop.hom.IsIntegral`
- `isField_of_universallyClosed (f : X ⟶ Spec (.of K)) [IsIntegral X]
  [UniversallyClosed f] : IsField Γ(X, ⊤)`
- `finite_appTop_of_universallyClosed` — same plus `LocallyOfFiniteType`, giving
  `Module.Finite`.

**Why this matters far beyond one leaf.** "A global regular function on a proper
variety is constant" is a step in many curve arguments, and the reflex here is to
formalise it geometrically: extend the function to a morphism `X ⟶ 𝔸¹`, prove that
morphism proper by cancelling against a separated target, then run a dichotomy on
its fibres ending in Zariski's main theorem
(`IsFinite.of_isProper_of_locallyQuasiFinite`). That is what
`CurveAffineComplement.lean`'s docstrings planned for
`not_exists_stalkSpecializes_eq_germ_coordOf_compl_singleton`, over two rounds of
cutting, and it needs the extension MORPHISM plus "an infinite closed subset of a
curve is the whole curve", which is real dimension theory.

With the lemma above the dichotomy does not arise: the extension is ALGEBRAIC over
`K` outright, so the "dominant" branch is impossible rather than excluded, and only
the SECTION has to be produced — never the morphism. The proof that landed is about
40 lines and uses no ZMT, no ampleness and no second properness.

**The transferable move**: when an argument wants "this function is constant / this
morphism is not dominant" on a proper scheme, reach for integrality of `Γ(X, ⊤)`
first and build the morphism only if that fails. The polynomial witness then travels
through the classifying RING map (package it as one — see
`CurveAffineComplement.coordHom` — because `Polynomial.ringHom_ext` turns any ring map
out of `K[T]` into `eval₂` of its restriction to `K` and its value at `T`), and lands
as `p ∈ (g.base η).asIdeal` at the generic point, which over a PID is a MAXIMAL ideal,
i.e. a closed point.

Related: [[flt-inventory-audits-understate-what-exists]],
[[audit-searched-production-not-invariant]] — both are the same failure shape, an
audit that searched for how to BUILD the object rather than for the invariant that
decides it.
