---
name: audit-lacks-x-is-about-x
description: An audit's "mathlib lacks X" is a claim about X, never about the obligation — re-derive what the obligation actually needs; this pin HAS Zariski's Main Theorem
metadata:
  type: project
---

Three successive audits of `hasDoubleCoverOfAffineLine_of_iso_sectionIdeal`
(`X0.lean`, the `g¹₂`) costed its `IsFinite φ` clause at Riemann–Roch, on the
recorded grounds that "mathlib at this pin has no coherent cohomology, no
`LinearSystem`, no `gonality`, no degree of a divisor". Every one of those
absences is REAL. None of them is needed: finiteness of `φ : U ⟶ 𝔸¹` from a
dense open of a proper curve is

    IsFinite = IsProper ⊓ LocallyQuasiFinite

which is `IsFinite.of_isProper_of_locallyQuasiFinite` in
`Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean` — **this pin has Zariski's
Main Theorem** — plus the four cancellation lemmas (`IsSeparated.of_comp`,
`QuasiSeparated.of_comp`, `QuasiCompact.of_comp`, `locallyOfFiniteType_of_comp`)
and `UniversallyClosed.of_valuativeCriterion`. Proven 2026-07-31 in
`Fermat/FLT/Mathlib/AlgebraicGeometry/AffineLineExtension.lean`, sorry-free.

**Why:** the audits searched the axis a `ℙ¹`/pencil route would need (degree,
`h⁰`, linear systems) and reported truthfully on it. An obligation phrased
affinely runs on a different axis entirely. Three agreeing audits are not
independent confirmation when all three searched the same axis — the same
failure shape as [[flt-inventory-audits-understate-what-exists]] and
[[audit-searched-production-not-invariant]].

**How to apply:** when a docstring costs a clause at a missing theory, do not
price the theory. Restate the clause as a property of the morphism/object and
grep mathlib for THAT property's characterisation lemmas
(`*_iff_*`, `.of_*`, `eq_*_inf_*`). `MorphismProperty` inf-decompositions
(`IsFinite.eq_proper_inf_locallyQuasiFinite`,
`IsIntegralHom.iff_universallyClosed_and_isAffineHom`,
`IsProper.eq_valuativeCriterion`) are where the cheap routes live, and they are
invisible to a search for the mathematical NOUN.

Tactical corollary from the same run: `ValuativeCommSq` is a bundled structure,
and a lift obtained from `(ValuativeCriterion f ⟨R, K, i₁, i₂, ⟨w⟩⟩).some.default`
carries `{R := …, …}.R` in its type, which no `rw` will match against the
caller's `sq.R`. Unbundle it once — state `exists_lift_of_isProper` /
`eq_of_isSeparated_of_lift` with `R`, `K` as ordinary binders and close them by
`exact` (proj-reduction is defeq) — and every later rewrite goes through.
