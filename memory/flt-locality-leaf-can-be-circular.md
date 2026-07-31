---
name: flt-locality-leaf-can-be-circular
description: "Reduce to the local case" is only a decomposition if the local case has an independent proof — restricting an abstract object along an open immersion is usually an instance of the very theorem
metadata:
  type: project
---

Katz–Mazur (8.1.6)(2) — the coarse moduli space commutes with flat base change
— is proved Zariski-locally on the base. The obvious formal decomposition is
therefore "(i) restrict the atlas to an open `U`, (ii) prove the theorem there,
(iii) glue". Step (i) is `A.BcQuotient U.ι` for an open immersion `U.ι`, and an
open immersion is FLAT: step (i) *is an instance of the theorem being proved*.
Reducing to it is circular, and the circularity is invisible because the leaf
reads as a humble special case.

The non-circular route is the other one: do not restrict the GIVEN object,
CONSTRUCT the glued one and transport at the end. That is why the leaf was
restated as `∃ A', A'.BcQuotient (Spec f)` rather than as a property of the
given `A` — the existential is exactly the licence to build a different model.
`exists_isIso_classify_of_isCoarseModuliY0_base` then carries the conclusion
back, so the existential costs nothing.

**Why:** an abstract object satisfying a universal property has no accessible
restriction; only initiality relates it to anything. "Restrict, prove, glue"
silently assumes the restriction is again a coarse space, which is the theorem.

**How to apply:** whenever a proposed sub-leaf is the target statement at a
special case of its own hypothesis (a localization, an open immersion, an
isomorphism, the identity), ask what proves the special case that does not
prove the general one. If the answer is "the same argument", it is not a
decomposition. Prefer moving the object into an existential so the prover may
build a convenient model — the trick this file already used for the field case
(`exists_gamma0AtlasOver_bcQuotient_of_field`) and which is what unblocked it.
Related: [[flt-cleaner-statement-harder-proof]], [[flt-two-leaves-may-be-one]].
