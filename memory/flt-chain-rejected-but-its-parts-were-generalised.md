---
name: flt-chain-rejected-but-its-parts-were-generalised
description: A docstring's "that upstream chain is hardcoded to ℚ, nothing to instantiate" verdict is about the CHAIN, not the pieces it is assembled from — check those, and check their dates
metadata:
  type: project
---

`exists_weierstrassModel_of_abelianSchemeStruct_finiteField` (`ModularCurve/X1.lean`)
was cut on 2026-07-28 with a checked-not-assumed verdict: the ℚ-side Weierstrass-model
chain in `EllipticScheme.lean` is hardcoded to `Spec (CommRingCat.of ℚ)`, its own three
leaves are open, "so there is nothing to instantiate". Every clause of that was true
about **that chain**.

It was false about the piece the chain is *itself* assembled over.
`AlgebraicGeometry.exists_isOpenImmersion_range_eq_compl_of_section`
(`Fermat/FLT/Mathlib/AlgebraicGeometry/CurveAffineComplement.lean`) is stated over an
arbitrary base field `K`, and on **2026-07-30** it grew the `Algebra K R` and
structure-morphism conjuncts *explicitly so that it would be usable over a field that is
not `ℚ`* — its own docstring says so. Applied at `K = ZMod ℓ` it discharges the entire
scheme-theoretic half, and the leaf became an assembly over one Riemann–Roch leaf
(`exists_weierstrassRingEquiv_of_abelianSchemeChart`) on 2026-07-31.

**Why:** a reuse audit naturally searches at the granularity of the thing it wants to
reuse — the named theorem with the right conclusion. When that is rejected, the search
stops, and the *sub-lemmas* it was built from are never looked at even though they are
usually the general ones (a `Fermat/FLT/Mathlib/` module is base-generic by construction;
the `ModularCurve/` assembly on top of it is what carries the hardcoded base). Worse, the
verdict is then written into a docstring where it reads as settled, and it does not expire
when someone generalises the sub-lemma two days later.

**How to apply:** when a leaf's docstring says a related development "cannot be reused",
(a) open that development's own import list and check its `Fermat/FLT/Mathlib/` inputs
before believing it, and (b) compare the docstring's date against `git log` on those
files. A generalisation commit landing *after* the audit is exactly the case the audit
cannot have seen. Same shape as [[audit-searched-production-not-invariant]] and
[[flt-dispatch-consumer-lists-are-unverified]]: the verdict is only as wide as the
granularity the auditor searched.

Corollary for the import line: the reused piece may need a **non-public** `import` only,
when it appears in proof bodies and not in signatures — that is what X1.lean does for
`CurveAffineComplement`, and it keeps the reserved-token/blast-radius problem that made
`X0.lean` import `EllipticScheme` privately from spreading.
