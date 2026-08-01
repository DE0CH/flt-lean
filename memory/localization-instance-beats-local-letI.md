---
name: localization-instance-beats-local-letI
description: An OreLocalization/Quotient/Polynomial derived SMul instance beats a local letI Algebra, so a goal's Localization.AtPrime and the proof's Algebra on the base ring cannot coexist — keep the localization abstract
metadata:
  type: reference
---

`Localization.AtPrime p` is an `OreLocalization`, which carries
`OreLocalization.instSMulOfIsScalarTower : SMul R (X[S⁻¹])` derived from `SMul R X`. So
once `Algebra A C` is in scope, `SMul A (Localization.AtPrime p)` resolves to that derived
instance and **not** to a local `letI algALp : Algebra A (Localization.AtPrime p)` — in
either declaration order. Measured 2026-08-01: with `Algebra A C` in scope,
`(inferInstance : SMul A (Localization.AtPrime p)) = algALp.toSMul` is not `rfl`; without
it, it is.

The symptom is a type mismatch on `IsScalarTower.of_algebraMap_eq` whose EXPECTED type —
built from your own ascription — already names `OreLocalization.instSMulOfIsScalarTower`.
It reads as a broken lemma and is not one.

**Escape:** put every step that needs the base-ring `Algebra` into a helper lemma where the
localization is a variable `{D} [CommRing D] [Algebra C D] (M) [IsLocalization M D]`. A
variable has no derived instance, so `Algebra A D` can only be the one passed in. State the
helper's `Algebra A D` as a `letI` in its STATEMENT in the consumer's exact spelling, so the
conclusion's tensor product is syntactically the consumer's.

A hypothesis carrying its own instances as `let`s in its type (this development's `hpush`
shape) can be passed to such a helper without the caller acquiring those instances at all —
which is what makes the split possible. See [[flt-opaque-carrier-blocks-quotient-lemma]] for
the sibling trap one level down, and CLAUDE.md's section
"A LOCALIZATION IN THE GOAL AND ITS BASE RING IN THE PROOF CANNOT COEXIST".

Same hazard exists for `Polynomial`, `MvPolynomial`, `Quotient` and `TensorProduct`, all of
which derive `SMul` from the base.
