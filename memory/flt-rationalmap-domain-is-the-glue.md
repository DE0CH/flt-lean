---
name: flt-rationalmap-domain-is-the-glue
description: "Gluing a spread-out extension to the open it extends is mathlib's RationalMap.domain/toPartialMap, not a hand-rolled open cover — and structure-instance notation breaks ValuativeCommSq where @mk works"
metadata:
  type: project
---

Two things learned closing `exists_neronExtension_atSpecialGenericPoint`
(X0.lean, BLR *Néron Models* 1.2/8 step (i)), 2026-07-31.

**1. `Scheme.RationalMap.domain` + `RationalMap.toPartialMap` ARE the glue.**
The task's route note listed `Scheme.PartialMap.ofFromSpecStalk` as "the
spreading-out step" and then said the extension has to be "glued with the
generic fibre, and the glue is where separatedness and density are spent" —
which reads like an open-cover argument to write by hand. It is not. For
`[IsReduced X] [Y.IsSeparated]`, `RationalMap.domain f` is the sSup of the
domains of ALL representatives and `RationalMap.toPartialMap f` realises `f`
on it (`Mathlib/AlgebraicGeometry/Birational/RationalMap.lean`, the `domain`
section at the very end of the file). So:

* build the given morphism as a `PartialMap` on its open dense domain;
* build the spread-out extension as a second `PartialMap`;
* prove the two are `equiv` (`equiv_of_fromSpecStalkOfMem_eq` at the generic
  point — a dense open of an irreducible space contains it, so both domains
  do);
* take `U := (that rational map).domain`. It contains BOTH domains by
  `PartialMap.le_domain_toRationalMap`, and
  `toPartialMap_toRationalMap_restrict` says the glued morphism restricts back
  to each. No cover, no cocycle.

**Why: **`RationalMap.toPartialMap`'s own proof is the open-cover gluing, done
once in mathlib over `openCoverDomain` and `equiv_iff_of_isSeparated`. A route
note written from the `ofFromSpecStalk` end of the file stops before it.

**How to apply:** when a leaf is "extend a map defined on a dense open across
one more point", read the WHOLE of `Birational/RationalMap.lean`, not the
spreading-out lemmas the audit named. The whole leaf came to ~90 lines with
two named sub-leaves, both of which are the single missing
`Smooth ⟹ GeometricallyReduced`. Related: [[flt-recommended-route-may-be-expensive]],
[[flt-missing-machinery-may-be-downstream]].

**2. Lean: `@Struct.mk` where structure-instance notation fails.**
`ValuativeCommSq` has instance-implicit fields (`[domain : IsDomain R]`,
`[isFractionRing : IsFractionRing R K]`) BETWEEN its data fields. Writing
`{ R := XZ.presheaf.stalk η, K := XZ.functionField, i₁ := …, i₂ := … }`
fails three ways at once: `failed to synthesize IsDomain ↑(XZ.presheaf.stalk η)`
even with that exact instance in context, and `i₂` reported as
`Spec (CommRingCat.of sq.R) ⟶ SR` against `Spec (XZ.presheaf.stalk η) ⟶ SR`
— the instance fields and the later data fields are elaborated before `R` is
assigned, so `sq.R` is not yet reducible. `@ValuativeCommSq.mk _ _ f R _ _ hval
K _ _ _ i₁ i₂ ⟨hcomm⟩` fixes all three, because positional application assigns
`R` and `K` first. (X0.lean's older `bijective_pre_generic_of_isProper` uses
the brace form successfully — it works there only because its `R` is a plain
`Subring ℚ` with no coercion in the way.)

**Also: do not `haveI : Algebra A B := inferInstance` as a probe.** It creates
an opaque fvar that then SHADOWS the real instance, and the next
`IsFractionRing A B` search fails because it is stated against the real
`Algebra` path. Deleting the probe made it synthesize.
