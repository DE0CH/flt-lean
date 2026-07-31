---
name: flt-run-the-worked-example-backwards
description: A leaf asking for a SUBFUNCTOR statement is cut by weakening it to ONE test object when the passage back is already a named leaf — and the proof of the passage is usually a PROVEN sibling's proof run in reverse.
metadata:
  type: project
---

(2026-07-31, `flt-lean-312`, `ModularCurve/X0.lean`,
`exists_gamma0Datum_specQ_isBaseChangeOf_liesIn_of_weierstrassQForm`.)

Two moves, and they compose. Both are about a leaf whose conclusion compares two
sub-objects **as subfunctors** — `∀ T (s : T ⟶ A), (∃ y, y ≫ j₁ = s) ↔ (∃ y, y ≫ j₂ = s)`
— which is the phrasing this development uses whenever a points-level phrasing
would admit a junk witness.

**1. WEAKEN THE TEST OBJECT, NOT THE COMPARISON.** The refuted phrasing such
leaves warn against is a comparison through a FREE `≃+` of geometric fibres
(over `ℚ̄` any two cyclic subgroups of order `N` are interchangeable by an
automorphism of `E(ℚ̄) ≅ (ℚ/ℤ)²`). Restricting the SAME comparison — still
through the two fixed structure maps — to `T = Spec K` is a completely different
weakening: nothing is left free to move a point of a fixed scheme. So a leaf of
this shape cuts cleanly into "the same statement at `T = Spec K`" plus a
points→subscheme upgrade, and **the upgrade is a theorem, not a hope**, whenever
the two sub-objects are finite étale over an algebraically closed base
(`exists_isIso_of_liesIn_specPt_iff` is that statement here, stated once for the
three leaves in the file that owed it).

**2. THE UPGRADE'S PROOF IS ALREADY WRITTEN, BACKWARDS.** The file contained
`exists_isIso_cyc_of_isIso_isWeierstrassModel`, PROVEN, deriving the `K`-point
comparison FROM the subfunctor one. Its proof is the three moves the reverse
direction needs, in the same order — a comparison isomorphism of the two ambient
schemes, `IsOpenImmersion.lift` to transport points on the open chart, and the
zero section for the one point off it — so the reverse proof was a
transcription with the two ends swapped, and compiled with no new mathematics.
**Before writing a `B → A`, grep the file for a proven `A → B` on the same
objects**: in a development that cuts aggressively, the two are usually written
by the same hand and share every step.

Riders, both of which cost a round:

* the transported test point must satisfy the new leaf's *section* hypothesis
  (`x ≫ f = 𝟙`); `IsOpenImmersion.lift ι x hsub` inherits it for free from
  `hs : ι ≫ d.f = weierstrassAffineStr W`, which is one `rw` and is easy to forget
  to state;
* the count does not move — one leaf out, one leaf in. Judge it by what is LEFT:
  the residue here lost every scheme-theoretic obligation and is pure arithmetic.
  See [[flt-price-the-comparison-last]] and the "cut is not measured by the delta"
  rule in CLAUDE.md.

Related: [[flt-inventory-audits-understate-what-exists]] fired inside the same
task — the docstring I wrote said two transports were missing, and one of them
(`isWeierstrassModel_map_of_isBaseChangeOf`, the model of a base change) was
PROVEN 4000 lines above. Grep each named-missing item separately; an inventory
claim covering "two transports, neither of which is in this file" is two claims.
