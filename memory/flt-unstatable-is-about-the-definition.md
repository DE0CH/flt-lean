---
name: flt-unstatable-is-about-the-definition
description: A "this object cannot be stated at the pin" audit verdict is scoped to the definition the auditor had in mind; enumerate other characterisations and price each separately
metadata:
  type: project
---

`finrank_cuspForm_eq_x0Genus` (`ModularCurve/X0.lean`) was a bare `sorry` because three
audits agreed the genus of a scheme "cannot currently be STATED" at this pin. The absence
they cited was real and re-checked — `grep genus` over mathlib returns nothing, there is no
coherent cohomology and no `Ω[X/S]` for a morphism of schemes — but it is an absence of
the CLASSICAL DEFINITIONS `dim H¹(X, 𝒪)` and `dim H⁰(X, Ω¹)`, not of the genus.

**Riemann's theorem** `ℓ(D) = deg D + 1 − g` for `deg D ≫ 0` characterises `g` using only
`Scheme.functionField`, `Scheme.ord` (`Mathlib/AlgebraicGeometry/OrderOfVanishing.lean`,
2025) and `Scheme.Hom.residueDegree` — all in the pin, none previously used anywhere in
this tree. Ninety lines of definitions in
`Fermat/FLT/Mathlib/AlgebraicGeometry/CurveGenus.lean` made the leaf an assembly over three
named sub-leaves.

**Why:** equivalent definitions are not equally expressible, so a feasibility verdict
inherits the definition its author happened to picture. The `Ω¹`-free characterisation also
turned out to be the *better* one for the consumers, since Abel–Jacobi and point counting
want the asymptotic form and not Serre duality.

**How to apply:** when an audit says an intermediate object is unstatable, list every
characterisation of that object and price each against the pin separately. Then `grep` for
the chosen characterisation's INGREDIENTS, not for the object's name — "zero files match
`genus`" was true and worthless. Ship a uniqueness proof with any non-textbook
characterisation (`IsCurveGenus.unique` is twelve lines); it is what stops the definition
from being a convention a consumer could satisfy by choosing the value. Related:
[[mathlib-states-point-facts-as-morphism-properties]],
[[flt-inventory-audits-understate-what-exists]], [[audit-searched-production-not-invariant]].
