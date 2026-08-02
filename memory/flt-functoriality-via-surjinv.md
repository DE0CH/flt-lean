---
name: flt-functoriality-via-surjinv
description: A hom out of a group presented as the image of a MONOID factors via Function.surjInv — how ClassGroup.relNormHom was built in 30 lines
metadata: 
  node_type: memory
  type: project
  originSessionId: 7e6ea76e-7052-425e-a259-4631f2a36535
  modified: 2026-08-02T19:42:40.935Z
---

(2026-08-01, `flt-lean-382`.) `ClassGroup.relNormHom : ClassGroup S →* ClassGroup R` — the
ideal norm on class groups — is **not** at our pin. Mathlib carries only
`ClassGroup.extendedHom`, the pushforward in the OPPOSITE direction, and the norm cannot be
transported through `ClassGroup R = (FractionalIdeal R⁰ K)ˣ ⧸ (principal)` because there is no
relative norm on fractional ideals either.

It is ~30 lines, by a recipe that applies whenever a group is presented as the image of a
MONOID:

* `ClassGroup.mk0 : (Ideal R)⁰ →* ClassGroup R` is a monoid hom, is SURJECTIVE
  (`ClassGroup.mk0_surjective`), and `ClassGroup.mk0_eq_mk0_iff` characterises its fibres
  (`(x) I = (y) J`);
* prove the intended composite is constant on those fibres — here apply `Ideal.relNorm` to
  that equation, with `Ideal.relNorm_singleton` and `Algebra.intNorm_eq_zero`;
* define the FUNCTION by `Function.surjInv`, and get `map_mul` from `MonoidHom.mk'` after
  `obtain ⟨I, rfl⟩ := mk0_surjective a` reduces both sides to generators;
* never unfold it again — `relNormHom_mk0` is the whole interface, and tower transitivity is
  `Ideal.relNorm_relNorm` plus one `MonoidHom.ext`.

Lives in `Fermat/FLT/Mathlib/RingTheory/ClassGroupRelNorm.lean`. Applies to any
"norm/trace/degree induces a map on classes" statement.
