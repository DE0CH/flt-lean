---
name: flt-price-the-comparison-last
description: A "route costs 1→2" pricing is often counting a structure transport you can replace by comparing the two objects at the END, where it is a bare morphism of schemes
metadata:
  type: project
---

When a route needs "an `IsFoo` for the **GIVEN** object `X`" but the construction
theorem (`exists_relPicZero`, `exists_relativeJacobian`, …) only ever produces one
for some **other** `X₀`, do NOT price a transport of the whole structure from `X₀`
to `X`. Compare `X₀` and `X` at the very END instead, where the comparison is a
morphism of SCHEMES and the identification is uniqueness of a map out of an
initial object.

**Why:** structures like `IsRelPicZeroOf` have ten fields living at sheaf level
(`modTensor`, `modPullback`, `RelPicEquiv`, `sectionIdeal`); moving one along an
isomorphism is hundreds of lines and needs new sheaf lemmas. The same isomorphism
carried at the end is `pullback.lift` plus `pullback.hom_ext` — ~120 lines of
`Category.assoc`, no sheaf anywhere. The transport is not merely cheaper there,
it is a different kind of object.

**How to apply:** do the whole construction on `X₀`; get the canonical iso
`e : X₀ ≅ X` from two-sided initiality of the two structures over the *original*
base; base change `e` if the conclusion is about a fibre product; then identify
the given comparison morphism with `(comparison out of X₀) ≫ ē` using the
uniqueness clause of the constructed structure's own universal property.

This refuted a standing `1 → 2` verdict on `isIso_jacobianBaseChangeComparison`
in `Fermat/FLT/ModularCurve/X0.lean` (2026-07-31): the route was blocked for a
day on obligation (1) "an `IsRelPicZeroOf` for the given `(J, ab, o)`", which is
not needed at all. The leaf closed at `1 → 1`, onto the strictly smaller citation
`exists_isRelPicZeroOf_baseChange`.

Corollary for audits generally: a PRICING is a hypothesis about a proof, and a
wrong one is expensive precisely because it is written as a verdict and read as a
fact. When an audit says "do not take this route", check whether its obligations
are obligations of the ROUTE or only of the particular way it was imagined.
See [[flt-cleaner-statement-harder-proof]] and [[audit-searched-production-not-invariant]].
